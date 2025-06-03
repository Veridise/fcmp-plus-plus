use std::cmp::max;
// Replace these with your actual crate imports.
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};

use ciphersuite::{Ed25519, group::Group, Ciphersuite, Helios, Selene};
use ec_divisors::DivisorCurve;

use full_chain_membership_proofs::FcmpParams;
use generalized_bulletproofs::transcript::{Transcript, VerifierTranscript};
use generic_array::GenericArray;
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};

use full_chain_membership_proofs::picus::{constrain_member_of_list, constrain_tuple_member_of_list};
use full_chain_membership_proofs::FcmpCurves;
use generalized_bulletproofs_circuit_abstraction::picus::PicusProgram;
use generalized_bulletproofs_circuit_abstraction::{picus::PicusModule, Circuit, LinComb, Variable};
use ciphersuite::group::ff::Field;
use ciphersuite::group::ff::PrimeField;
use generalized_bulletproofs_ec_gadgets::{
  CurveSpec, DiscreteLogParameters, Divisor, EcDlogGadgets, EcGadgets, GeneratorTable, OnCurve, PointWithDlog
};

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};
use generic_array::typenum::Unsigned;

/// Inputs to the picus analyzer
struct PicusInputs<C: Ciphersuite> {
  assume_circuits: Vec<Circuit<C>>,
  assert_circuits: Vec<Circuit<C>>,
  num_unconstrained_rows: usize,
  input_vars: Vec<Variable>,
}

impl<C: Ciphersuite> PicusInputs<C> {
  /// Converts circuit into a Picus module, marking l and r as inputs.
  fn to_picus_module(self, name: &str) -> Result<PicusModule<C::F>, String> {
    let module = PicusModule::<C::F>::from_circuits(
      name.to_string(),
      self.assume_circuits,
      self.assert_circuits,
      self.num_unconstrained_rows,
      self.input_vars,
    )?;
    Ok(module)
  }
}

fn dummy_rng() -> StdRng {
  let seed: [u8; 32] = [42; 32]; // 32-byte seed
  StdRng::from_seed(seed)
}

/// Build a simple dummy transcript
fn dummy_transript<'a>(proof: &'a [u8]) -> VerifierTranscript<'a> {
  let mut rng = dummy_rng();
  let mut context: [u8; 32] = [0; 32];
  rng.fill_bytes(&mut context);
  let context = context;

  VerifierTranscript::new(context, &proof)
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
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![circuit],
    num_unconstrained_rows: 1,
    input_vars: vec![l, r],
  }
}

fn generate_equality_circuit<C>() -> PicusInputs<C>
where
  C: Ciphersuite,
{
  // Constrain equality
  let mut equality_circuit: Circuit<C> = Circuit::<C>::empty(1);
  let l0 = Variable::aL(0);
  let r0 = Variable::aR(0);

  equality_circuit.equality(l0.into(), &r0.into());

  // Only input is left lincomb
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![equality_circuit],
    num_unconstrained_rows: 1,
    input_vars: vec![l0],
  }
}

fn generate_inequality_circuit<C>() -> PicusInputs<C>
where
  C: Ciphersuite,
{
  let mut inequality_circuit: Circuit<C> = Circuit::<C>::empty(1);
  let l0 = Variable::aL(0);
  let r0 = Variable::aR(0);

  inequality_circuit.inequality(l0.into(), &r0.into(), None);

  // Return inequality, ensuring all other variables
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![inequality_circuit],
    num_unconstrained_rows: 1,
    input_vars: vec![Variable::aL(0), Variable::aR(0)],
  }
}

fn generate_inverse_circuit<C>() -> PicusInputs<C>
where
  C: Ciphersuite,
{
  // Constrain equality
  let mut inverse_circuit: Circuit<C> = Circuit::<C>::empty(1);
  let l0 = Variable::aL(0);

  let _inv_l0 = inverse_circuit.inverse(Some(l0.into()), None);

  // Input is the inverting variable
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![inverse_circuit],
    num_unconstrained_rows: 1,
    input_vars: vec![l0],
  }
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
    num_unconstrained_rows: num_predefined_vars,
    input_vars: all_vars,
  }
}

fn generate_tuple_member_of_list_circuit<C>(
  list_length: usize,
  tuple_length: usize,
) -> PicusInputs<C>
where
  C: Ciphersuite,
{
  assert!(list_length > 0);
  assert!(tuple_length > 0);

  // Build variables
  let list = (0..list_length)
    .map(|i| {
      (0..tuple_length).map(|j| Variable::CG { commitment: i, index: j }).collect::<Vec<_>>()
    })
    .collect::<Vec<Vec<_>>>();
  let maybe_member_var = (0..tuple_length)
    .map(|j| Variable::CG { commitment: list_length, index: j })
    .collect::<Vec<_>>();
  let all_vars =
    list.iter().cloned().chain(Some(maybe_member_var.clone())).flatten().collect::<Vec<_>>();

  // Add membership check
  let num_predefined_vars = 0;
  let dummy_proof = [];
  let transcript = dummy_transript(&dummy_proof);
  let tuple_member_of_list_circuit: Circuit<C> = Circuit::<C>::empty(num_predefined_vars);
  let tuple_member_of_list_circuit = constrain_tuple_member_of_list::<C, _>(
    transcript,
    tuple_member_of_list_circuit,
    maybe_member_var.into(),
    list,
  );

  // Return the circuit along with input variable (the point)
  PicusInputs {
    assume_circuits: vec![],
    assert_circuits: vec![tuple_member_of_list_circuit],
    num_unconstrained_rows: num_predefined_vars,
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
    num_unconstrained_rows: 1,
    input_vars: vec![pt.0, pt.1],
  }
}

fn generate_ec_incomplete_add_fixed_circuit<C, BaseCurve>(
  check_b_on_curve: bool,
  check_c_on_curve: bool,
) -> PicusInputs<C>
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

  // used to hold assumptions when assuming curve-checks have been performed
  let mut on_curve_circuit = Circuit::<C>::empty(num_predefined_vars);
  // Used to create OnCurve ponts when not assuming curve checks have not been performed
  let mut dummy_circuit = Circuit::<C>::empty(num_predefined_vars);

  // Add on-curve assumptions
  let mut on_curve_pts: Vec<OnCurve> = vec![];
  let curve = CurveSpec { a: BaseCurve::a(), b: BaseCurve::b() };

  for (pt, check_on_curve) in [(b, check_b_on_curve), (c, check_c_on_curve)] {
    let on_curve_pt = if check_on_curve {
      on_curve_circuit.on_curve(&curve, pt)
    } else {
      dummy_circuit.on_curve(&curve, pt)
    };
    on_curve_pts.push(on_curve_pt);
  }
  let (b, c) = (on_curve_pts[0], on_curve_pts[1]);

  // Constrain addition
  let num_predefined_vars: usize = max(on_curve_circuit.muls(), num_predefined_vars);
  let mut addition_circuit: Circuit<C> = Circuit::<C>::empty(num_predefined_vars);
  addition_circuit.incomplete_add_fixed(a, b, c);

  // Return the circuit along with input variables (a is fixed, b is input, and c is output).
  PicusInputs {
    assume_circuits: vec![on_curve_circuit],
    assert_circuits: vec![addition_circuit],
    num_unconstrained_rows: 2,
    input_vars: vec![b.x(), b.y()],
  }
}

struct Ed25519Params;
impl DiscreteLogParameters for Ed25519Params {
  type ScalarBits = U<{ <<Ed25519 as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

struct SeleneParams;
impl DiscreteLogParameters for SeleneParams {
  type ScalarBits = U<{ <<Selene as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

struct HeliosParams;
impl DiscreteLogParameters for HeliosParams {
  type ScalarBits = U<{ <<Helios as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone)]
struct MoneroCurves;
impl FcmpCurves for MoneroCurves {
  type OC = Ed25519;
  type OcParameters = Ed25519Params;
  type C1 = Selene;
  type C1Parameters = SeleneParams;
  type C2 = Helios;
  type C2Parameters = HeliosParams;
}

/// 3. Writes the printed Picus module to a file at the given path.
fn write_to_file<P: AsRef<Path>>(content: &str, path: P) -> std::io::Result<()> {
  let mut file = File::create(path)?;
  file.write_all(content.as_bytes())?;
  Ok(())
}

/// Generate a picus program, write it to a file
///
/// Returns the picus module
fn generate_and_write_picus_module<C>(
  out_dir: &Path,
  circuit_name: &str,
  picus_inputs: PicusInputs<C>,
) -> Result<PicusModule<C::F>, String>
where
  C: Ciphersuite,
{
  println!("Generating {}...", circuit_name);
  // Build the picus program
  let module: PicusModule<C::F> = picus_inputs.to_picus_module(circuit_name)?;
  let modules = write_picus_modules::<C>(out_dir, circuit_name, vec![module])?;
  // Use into_iter().next().unwrap() instead of [0] to avoid a reference
  let module = modules.into_iter().next().unwrap();

  Ok(module)
}

/// Convert picus modules into a program and write as picus and circom files
fn write_picus_modules<C>(
  out_dir: &Path,
  circuit_name: &str,
  modules: Vec<PicusModule<<C as Ciphersuite>::F>>,
) -> Result<Vec<PicusModule<<C as Ciphersuite>::F>>, String>
where
  C: Ciphersuite,
{
  let program: PicusProgram<C::F> = PicusProgram::new(modules);
  let picus_program_str = program.to_string();
  let picus_file_path = out_dir.join(format!("{}.picus", circuit_name));
  write_to_file(&picus_program_str, picus_file_path.clone())
    .expect(&format!("Failed to write to {:?}", picus_file_path));

  let main_module_index = 0;
  let circom_program_str = program.to_circom(main_module_index)?;
  let circom_file_path = out_dir.join(format!("{}.circom", circuit_name));
  write_to_file(&circom_program_str, circom_file_path.clone())
    .expect(&format!("Failed to write to {:?}", circom_file_path));

  Ok(program.modules())
}

/// Generate all circuits over the scalar field of C, using points on
/// BaseCurve for ec-operations
fn generate_all_circuits<C, BaseCurve>(out_dir: &Path) -> Result<(), String>
where
  C: Ciphersuite,
  BaseCurve: DivisorCurve<FieldElement = C::F>,
{
  let curve_id: String = String::from_utf8(C::ID.into()).expect("Failed to parse ID");
  let dummy_picus_module = generate_and_write_picus_module(
    out_dir,
    &format!("dummy_{}", curve_id),
    generate_dummy_circuit::<C>(),
  )?;

  let inverse_picus_module = generate_and_write_picus_module(
    out_dir,
    &format!("inverse_{}", curve_id),
    generate_inverse_circuit::<C>(),
  )?;

  let inequality_picus_module = generate_and_write_picus_module(
    out_dir,
    &format!("inequality_{}", curve_id),
    generate_inequality_circuit::<C>(),
  )?;

  let equality_picus_module = generate_and_write_picus_module(
    out_dir,
    &format!("equality_{}", curve_id),
    generate_equality_circuit::<C>(),
  )?;

  let list_picus_modules = (2..=8)
    .into_iter()
    .map(|list_length| {
      generate_and_write_picus_module(
        out_dir,
        &format!("member_of_list{}_{}", list_length, curve_id),
        generate_member_of_list_circuit::<C>(list_length),
      )
    })
    .collect::<Result<Vec<PicusModule<C::F>>, _>>()?;

  let tuple_list_picus_modules = (2..=8)
    .into_iter()
    .flat_map(|list_length| {
      let curve_id = curve_id.clone();
      (1..=8).into_iter().map(move |tuple_length| {
        generate_and_write_picus_module(
          out_dir,
          &format!("tuple_member_of_list_{}_{}_{}", list_length, tuple_length, curve_id),
          generate_tuple_member_of_list_circuit::<C>(list_length, tuple_length),
        )
      })
    })
    .collect::<Result<Vec<PicusModule<C::F>>, _>>()?;

  let ec_on_curve_picus_module = generate_and_write_picus_module(
    out_dir,
    "ec_on_curve",
    generate_ec_on_curve_circuit::<C, BaseCurve>(),
  )?;

  let mut ec_addition_circuits = vec![];
  for check_b_on_curve in [true, false] {
    let b_suffix = if check_b_on_curve { "_check_b" } else { "" };
    for check_c_on_curve in [true, false] {
      let c_suffix = if check_c_on_curve { "_check_c" } else { "" };
      ec_addition_circuits.push(generate_and_write_picus_module(
        out_dir,
        &format!("ec_incomplete_add_fixed{}{}_{}", b_suffix, c_suffix, curve_id),
        generate_ec_incomplete_add_fixed_circuit::<C, BaseCurve>(
          check_b_on_curve,
          check_c_on_curve,
        ),
      )?);
    }
  }

  let all_circuits =
    [dummy_picus_module, inverse_picus_module, inequality_picus_module, equality_picus_module]
      .into_iter()
      .chain(list_picus_modules.into_iter())
      .chain(tuple_list_picus_modules.into_iter())
      .chain([ec_on_curve_picus_module].into_iter())
      .chain(ec_addition_circuits.into_iter())
      .collect::<Vec<PicusModule<C::F>>>();

  write_picus_modules::<C>(out_dir, &format!("all_{}_circuits", curve_id), all_circuits)?;

  Ok(())
}

/// 4. Main function which builds the circuit, converts it to a Picus module,
///    writes it to a hard-coded file, and also prints the module to stdout.
fn main() -> Result<(), Box<dyn std::error::Error>> {
  // Create an "out" directory inside the crate directory.
  let manifest_dir = env!("CARGO_MANIFEST_DIR");
  let out_dir = PathBuf::from(manifest_dir).join("out");
  fs::create_dir_all(&out_dir)?;

  generate_all_circuits::<Selene, <Helios as Ciphersuite>::G>(&out_dir)?;
  generate_all_circuits::<Helios, <Selene as Ciphersuite>::G>(&out_dir)?;

  Ok(())
}
