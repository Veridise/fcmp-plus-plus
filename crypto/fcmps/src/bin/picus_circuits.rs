// Replace these with your actual crate imports.
use std::fs::File;
use std::io::Write;
use std::path::Path;

use ciphersuite::{Ciphersuite, Secp256k1};

use generalized_bulletproofs_circuit_abstraction::{
  picus::{PicusModule, PicusVariable},
  Circuit, LinComb, Variable,
};
use ciphersuite::group::ff::{Field, PrimeField};

/// Inputs to the picus analyzer
struct PicusInputs<C: Ciphersuite> {
  circuit: Circuit<C>,
  input_vars: Vec<Variable>,
}

impl<C: Ciphersuite> PicusInputs<C> {
  /// Converts circuit into a Picus module, marking l and r as inputs.
  fn to_picus_module(&self, name: &str) -> Result<PicusModule<C::F>, String> {
    let mut module = PicusModule::new(name.to_string());
    module.apply_constraints(&self.circuit)?;
    self
      .input_vars
      .iter()
      // TODO: Handle invalid unwrap
      .map(|input_var| module.circuit_variable_to_picus_variable(input_var, &self.circuit).unwrap())
      .collect::<Vec<PicusVariable>>()
      .into_iter()
      .for_each(|picus_var| {
        module.mark_variable_as_input(picus_var).expect("Vars already checked")
      });
    Ok(module)
  }
}

/// 1. Generates a circuit and returns it along with the two variables (l and r)
///    that will be marked as inputs in the Picus module.
fn generate_dummy_circuit<C: Ciphersuite>() -> PicusInputs<C> {
  let mut circuit: Circuit<C> = Circuit::<C>::empty();

  // Create a multiplication gate, capturing the variables.
  let (l, r, o) = circuit.mul(None, None, None);
  // Build a linear combination: l + r - o == 0.
  let lincomb = LinComb::empty().term(C::F::ONE, l).term(C::F::ONE, r).term(-C::F::ONE, o);
  circuit.constrain_equal_to_zero(lincomb);

  // Set up an inverse constraint (the details depend on your implementation).
  circuit.inverse(Some(l.into()), None);

  // Return the circuit along with variables l and r.
  PicusInputs { circuit, input_vars: vec![l, r] }
}

/// 3. Writes the printed Picus module to a file at the given path.
fn write_picus_module_to_file<F: PrimeField, P: AsRef<Path>>(
  module: &PicusModule<F>,
  path: P,
) -> std::io::Result<()> {
  let mut file = File::create(path)?;
  // Convert the module to a string (using its Display/ToString implementation)
  let content = module.to_string();
  file.write_all(content.as_bytes())?;
  Ok(())
}

/// 4. Main function which builds the circuit, converts it to a Picus module,
///    writes it to a hard-coded file, and also prints the module to stdout.
fn main() -> Result<(), Box<dyn std::error::Error>> {
  type C = Secp256k1;
  type F = <C as Ciphersuite>::F;

  let circuit_name = "dummy";
  let file_path = format!("{}.picus", circuit_name);
  let picus_inputs: PicusInputs<_> = generate_dummy_circuit::<C>();
  let module: PicusModule<F> = picus_inputs.to_picus_module(circuit_name)?;
  write_picus_module_to_file(&module, file_path)?;
  println!("Picus module '{}':\n{}", circuit_name, module);

  Ok(())
}
