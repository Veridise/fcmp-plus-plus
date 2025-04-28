use ciphersuite::Ciphersuite;
use generalized_bulletproofs::transcript::{Transcript, VerifierTranscript};
use generalized_bulletproofs_circuit_abstraction::{Circuit as BulletproofCircuit, LinComb, Variable};
use rand_core::RngCore;

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
pub fn constrain_tuple_member_of_list<C: Ciphersuite, R: RngCore>(
  rng: &mut R,
  circuit: BulletproofCircuit<C>,
  maybe_member_var: Vec<Variable>,
  list: Vec<Vec<Variable>>,
) -> BulletproofCircuit<C> {
  let mut circuit_wrapper: Circuit<C> = Circuit::<C>(circuit);

  let mut context: [u8; 32] = [0; 32];
  rng.fill_bytes(&mut context);
  let context = context;

  let proof = [];
  let mut transcript = VerifierTranscript::new(context, &proof);
  // Add membership check
  circuit_wrapper.tuple_member_of_list(&mut transcript, maybe_member_var, list);
  circuit_wrapper.0
}
