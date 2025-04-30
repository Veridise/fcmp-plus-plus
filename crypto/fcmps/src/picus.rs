use ciphersuite::Ciphersuite;
use generalized_bulletproofs_circuit_abstraction::{Circuit as BulletproofCircuit, LinComb, Transcript, Variable};

use crate::Circuit;

/// Add the member-of-list constraint to a bulletproofs circuit
pub fn constrain_member_of_list<C: Ciphersuite>(
  circuit: BulletproofCircuit<C>,
  maybe_member_var: LinComb<C::F>,
  list: Vec<LinComb<C::F>>,
) -> BulletproofCircuit<C> {
  let mut circuit_wrapper: Circuit<C> = Circuit::<C>(circuit);
  // Add membership check
  circuit_wrapper.member_of_list(maybe_member_var, list);
  circuit_wrapper.0
}

/// Add the tuple member-of-list constraint to a bulletproofs circuit
pub fn constrain_tuple_member_of_list<C: Ciphersuite, T: Transcript>(
  transcript: T,
  circuit: BulletproofCircuit<C>,
  maybe_member_var: Vec<Variable>,
  list: Vec<Vec<Variable>>,
) -> BulletproofCircuit<C> {
  let mut circuit_wrapper: Circuit<C> = Circuit::<C>(circuit);
  // Add membership check
  let mut transcript = transcript;
  circuit_wrapper.tuple_member_of_list(&mut transcript, maybe_member_var, list);
  circuit_wrapper.0
}
