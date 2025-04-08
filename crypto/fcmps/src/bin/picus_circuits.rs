// Replace these with your actual crate imports.
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};

use ciphersuite::Helios;
use ciphersuite::{group::ff::PrimeField, Ciphersuite, Secp256k1, Selene, Ed25519};
use ec_divisors::DivisorCurve;

use full_chain_membership_proofs::picus::constrain_member_of_list;
use generalized_bulletproofs_circuit_abstraction::picus::PicusProgram;
use generalized_bulletproofs_circuit_abstraction::{
  picus::{PicusModule, PicusVariable},
  Circuit, LinComb, Variable,
};
use ciphersuite::group::ff::Field;
use generalized_bulletproofs_ec_gadgets::{CurveSpec, EcGadgets};

/// Inputs to the picus analyzer
struct PicusInputs<C: Ciphersuite> {
  assume_circuits: Vec<Circuit<C>>,
  assert_circuits: Vec<Circuit<C>>,
  input_vars: Vec<Variable>,
}

impl<C: Ciphersuite> PicusInputs<C> {
  /// Converts circuit into a Picus module, marking l and r as inputs.
  fn to_picus_module(&self, name: &str) -> Result<PicusModule<C::F>, String> {
    let mut module = PicusModule::new(name.to_string());
    self
      .assume_circuits
      .iter()
      .map(|circuit| module.assume_constraints(circuit))
      .collect::<Result<Vec<_>, _>>()?;
    self
      .assert_circuits
      .iter()
      .map(|circuit| module.apply_constraints(circuit))
      .collect::<Result<Vec<_>, _>>()?;

    self
      .input_vars
      .iter()
      // TODO: Handle invalid unwrap
      .map(|input_var| module.circuit_var_get_or_create_picus_var(input_var))
      .collect::<Vec<PicusVariable>>()
      .into_iter()
      .for_each(|picus_var| {
        module.mark_variable_as_input(picus_var).expect("Vars already checked")
      });
    Ok(module)
  }
}

/// Generates a circuit and returns it along with the two variables (l and r)
/// that will be marked as inputs in the Picus module.
fn generate_dummy_circuit<C: Ciphersuite>() -> PicusInputs<C> {
  let mut circuit: Circuit<C> = Circuit::<C>::empty(0);

  // Create a multiplication gate, capturing the variables.
  let (l, r, o) = circuit.mul(None, None, None);
  // Build a linear combination: l + r - o == 0.
  let lincomb = LinComb::empty().term(C::F::ONE, l).term(C::F::ONE, r).term(-C::F::ONE, o);
  circuit.constrain_equal_to_zero(lincomb);

  // Set up an inverse constraint (the details depend on your implementation).
  circuit.inverse(Some(l.into()), None);

  // Return the circuit along with variables l and r.
  PicusInputs { assume_circuits: vec![], assert_circuits: vec![circuit], input_vars: vec![l, r] }
}

fn fe_to_scalar<C>(f: <C::G as DivisorCurve>::FieldElement) -> C::F
where
  C: Ciphersuite,
  <C as Ciphersuite>::G: DivisorCurve,
{
  // TODO: Handle big vs little endian
  let repr = f.to_repr();
  let repr_bytes: &[u8] = repr.as_ref();
  let scalar = C::F::from(0);
  let mut scalar_repr = scalar.to_repr();
  let mut scalar_bytes: &mut [u8] = scalar_repr.as_mut();
  assert_eq!(repr_bytes.len(), scalar_bytes.len());
  for (i, byte) in repr_bytes.iter().enumerate() {
    scalar_bytes[i] = *byte;
  }
  C::F::from_repr(scalar_repr).expect("Serialization/de-serialization failed")
}

fn generate_member_of_list_circuit<C>(list_length: usize) -> PicusInputs<C>
where
  C: Ciphersuite,
{
  assert!(list_length > 0);

  // Build variables
  let list = (0..list_length)
    .map(|i| if i % 2 == 0 { Variable::aL(i / 2) } else { Variable::aR(i / 2) })
    .collect::<Vec<_>>();
  let maybe_member_var_index = list_length / 2;
  let maybe_member_var = if list_length % 2 == 0 {
    Variable::aL(maybe_member_var_index)
  } else {
    Variable::aR(maybe_member_var_index)
  };
  let all_vars = list.iter().cloned().chain(Some(maybe_member_var)).collect::<Vec<_>>();

  // Add membership check
  let list: Vec<LinComb<C::F>> = list.into_iter().map(|var| var.into()).collect::<Vec<_>>();
  let num_predefined_vars = (all_vars.len() + 1) / 2;
  let member_of_list_circuit: Circuit<C> = Circuit::<C>::empty(num_predefined_vars);
  let member_of_list_circuit =
    constrain_member_of_list(member_of_list_circuit, maybe_member_var.into(), list);

  // Return the circuit along with input variable (the point)
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![member_of_list_circuit],
    input_vars: all_vars,
  }
}

fn generate_ec_on_curve_circuit<C, BaseCurve>() -> PicusInputs<C>
where
  C: Ciphersuite,
  BaseCurve: DivisorCurve<FieldElement = C::F>,
{
  // Build variables
  let pt = (Variable::aL(0), Variable::aR(0));
  let num_predefined_vars = 1;

  // Add on-curve sertions
  let curve = CurveSpec { a: BaseCurve::a(), b: BaseCurve::b() };
  let mut on_curve_circuit: Circuit<C> = Circuit::<C>::empty(num_predefined_vars);
  let _ = on_curve_circuit.on_curve(&curve, pt);

  // Return the circuit along with input variable (the point)
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![on_curve_circuit],
    input_vars: vec![pt.0, pt.1],
  }
}

fn generate_ec_incomplete_add_fixed_circuit<C, BaseCurve>() -> PicusInputs<C>
where
  C: Ciphersuite,
  BaseCurve: DivisorCurve<FieldElement = C::F>,
{
  // Build variables
  let a = BaseCurve::generator();
  let a = BaseCurve::to_xy(a).expect("Generator is on curve");
  let b = (Variable::aL(0), Variable::aL(1));
  let c = (Variable::aR(0), Variable::aR(1));
  let num_predefined_vars = 2;

  // Add on-curve assumptions
  let curve = CurveSpec { a: BaseCurve::a(), b: BaseCurve::b() };
  let mut on_curve_circuit: Circuit<C> = Circuit::<C>::empty(num_predefined_vars);
  let b = on_curve_circuit.on_curve(&curve, b);
  let c = on_curve_circuit.on_curve(&curve, c);

  // Constrain addition
  let mut addition_circuit: Circuit<C> = Circuit::<C>::empty(on_curve_circuit.muls());
  addition_circuit.incomplete_add_fixed(a, b, c);

  // Return the circuit along with input variables (a is fixed, b is input, and c is output).
  PicusInputs {
    assume_circuits: vec![on_curve_circuit],
    assert_circuits: vec![addition_circuit],
    input_vars: vec![b.x(), b.y()],
  }
}

/// 3. Writes the printed Picus module to a file at the given path.
fn write_to_file<P: AsRef<Path>>(content: &str, path: P) -> std::io::Result<()> {
  let mut file = File::create(path)?;
  file.write_all(content.as_bytes())?;
  Ok(())
}

/// Generate a picus program, write it to a file, and print it to the console
fn generate_and_write_picus_program<C>(
  out_dir: &Path,
  circuit_name: &str,
  picus_inputs: PicusInputs<C>,
) -> Result<(), String>
where
  C: Ciphersuite,
{
  // Build the picus program
  let module: PicusModule<C::F> = picus_inputs.to_picus_module(circuit_name)?;
  let program: PicusProgram<C::F> = PicusProgram::new(vec![module]);

  // Write and print the picus program
  let picus_program_str = program.to_string();
  let picus_file_path = out_dir.join(format!("{}.picus", circuit_name));
  write_to_file(&picus_program_str, picus_file_path.clone())
    .expect(&format!("Failed to write to {:?}", picus_file_path));
  println!("Program:\n{}", picus_program_str);

  // Write and print the picus program as circom
  let main_module_index = 0;
  let circom_program_str = program.to_circom(main_module_index)?;
  let circom_file_path = out_dir.join(format!("{}.circom", circuit_name));
  write_to_file(&circom_program_str, circom_file_path.clone())
    .expect(&format!("Failed to write to {:?}", circom_file_path));
  println!("Program:\n{}", circom_program_str);

  Ok(())
}

/// 4. Main function which builds the circuit, converts it to a Picus module,
///    writes it to a hard-coded file, and also prints the module to stdout.
fn main() -> Result<(), Box<dyn std::error::Error>> {
  // type BaseCurve = <Ed25519 as Ciphersuite>::G;
  type BaseCurve = <Helios as Ciphersuite>::G;
  type C = Selene;

  // Create an "out" directory inside the crate directory.
  let manifest_dir = env!("CARGO_MANIFEST_DIR");
  let out_dir = PathBuf::from(manifest_dir).join("out");
  fs::create_dir_all(&out_dir)?;

  generate_and_write_picus_program(&out_dir, "dummy", generate_dummy_circuit::<C>())?;
  for list_length in 1..=8 {
    generate_and_write_picus_program(
      &out_dir,
      &format!("member_of_list{}", list_length),
      generate_member_of_list_circuit::<C>(list_length),
    );
  }
  generate_and_write_picus_program(
    &out_dir,
    "ec_on_curve",
    generate_ec_on_curve_circuit::<C, BaseCurve>(),
  )?;
  generate_and_write_picus_program(
    &out_dir,
    "ec_incomplete_add_fixed",
    generate_ec_incomplete_add_fixed_circuit::<C, BaseCurve>(),
  )?;

  Ok(())
}
