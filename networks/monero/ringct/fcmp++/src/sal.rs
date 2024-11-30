use std_shims::io;

use rand_core::{RngCore, CryptoRng};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use blake2::{Digest, Blake2b512};

use curve25519_dalek::Scalar as DalekScalar;
use dalek_ff_group::{Scalar, EdwardsPoint};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite, Ed25519,
};

use monero_generators::{T, FCMP_U, FCMP_V};

use crate::{Input, Output};

#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct RerandomizedOutput {
  input: Input,
  r_o: <Ed25519 as Ciphersuite>::F,
  r_i: <Ed25519 as Ciphersuite>::F,
  r_r_i: <Ed25519 as Ciphersuite>::F,
  r_c: <Ed25519 as Ciphersuite>::F,
}

impl RerandomizedOutput {
  pub fn new(rng: &mut (impl RngCore + CryptoRng), output: Output) -> RerandomizedOutput {
    let r_o = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_i = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_r_i = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_c = <Ed25519 as Ciphersuite>::F::random(&mut *rng);

    let O_tilde = output.O() + (EdwardsPoint(T()) * r_o);
    let I_tilde = output.I() + (EdwardsPoint(FCMP_U()) * r_i);
    let R = (EdwardsPoint(FCMP_V()) * r_i) + (EdwardsPoint(T()) * r_r_i);
    let C_tilde = output.C() + (<Ed25519 as Ciphersuite>::generator() * r_c);

    RerandomizedOutput { input: Input { O_tilde, I_tilde, R, C_tilde }, r_o, r_i, r_r_i, r_c }
  }

  pub fn write(&self, writer: &mut impl io::Write) -> io::Result<()> {
    self.input.write(writer)?;
    writer.write_all(&self.r_o.to_repr())?;
    writer.write_all(&self.r_i.to_repr())?;
    writer.write_all(&self.r_r_i.to_repr())?;
    writer.write_all(&self.r_c.to_repr())
  }

  pub fn read(reader: &mut impl io::Read) -> io::Result<Self> {
    Ok(Self {
      input: Input::read(reader)?,
      r_o: Ed25519::read_F(reader)?,
      r_i: Ed25519::read_F(reader)?,
      r_r_i: Ed25519::read_F(reader)?,
      r_c: Ed25519::read_F(reader)?,
    })
  }

  // The FCMP code expects these as used in the proof, which adds these blinds to the blinded
  // values to recover the original values (requiring their negation)
  pub fn o_blind(&self) -> <Ed25519 as Ciphersuite>::F {
    -self.r_o
  }
  pub fn i_blind(&self) -> <Ed25519 as Ciphersuite>::F {
    -self.r_i
  }
  // I's blind's blind is kept in its actual form
  pub fn i_blind_blind(&self) -> <Ed25519 as Ciphersuite>::F {
    self.r_r_i
  }
  pub fn c_blind(&self) -> <Ed25519 as Ciphersuite>::F {
    -self.r_c
  }

  pub fn input(&self) -> Input {
    self.input
  }
}

/// The opening for the O~, I~, R of an Input tuple.
///
/// This does not open C~ as it's unnecessary for the purposes of this proof.
#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct OpenedInputTuple {
  input: Input,
  // O~ = xG + yT
  x: <Ed25519 as Ciphersuite>::F,
  y: <Ed25519 as Ciphersuite>::F,
  // R = r_i V + r_r_i T
  r_i: <Ed25519 as Ciphersuite>::F,
  r_r_i: <Ed25519 as Ciphersuite>::F,
}

impl OpenedInputTuple {
  /// x and y are for the x and y variables in O = xG + yT.
  pub fn open(
    rerandomized_output: RerandomizedOutput,
    x: &<Ed25519 as Ciphersuite>::F,
    y: &<Ed25519 as Ciphersuite>::F,
  ) -> Option<OpenedInputTuple> {
    // Verify the opening is consistent.
    let mut y_tilde = rerandomized_output.r_o + y;
    if (<Ed25519 as Ciphersuite>::generator() * x) + (EdwardsPoint(T()) * y_tilde) !=
      rerandomized_output.input.O_tilde
    {
      y_tilde.zeroize();
      None?;
    }
    Some(OpenedInputTuple {
      input: rerandomized_output.input,
      x: *x,
      y: y_tilde,
      r_i: rerandomized_output.r_i,
      r_r_i: rerandomized_output.r_r_i,
    })
  }
}

// BP+ and GSP Conjuction from Cypher Stack's Review of the FCMP++ Composition
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct SpendAuthAndLinkability {
  P: <Ed25519 as Ciphersuite>::G,
  A: <Ed25519 as Ciphersuite>::G,
  B: <Ed25519 as Ciphersuite>::G,
  R_O: <Ed25519 as Ciphersuite>::G,
  R_P: <Ed25519 as Ciphersuite>::G,
  R_L: <Ed25519 as Ciphersuite>::G,
  s_alpha: <Ed25519 as Ciphersuite>::F,
  s_beta: <Ed25519 as Ciphersuite>::F,
  s_delta: <Ed25519 as Ciphersuite>::F,
  s_y: <Ed25519 as Ciphersuite>::F,
  s_z: <Ed25519 as Ciphersuite>::F,
  s_r_p: <Ed25519 as Ciphersuite>::F,
}

impl SpendAuthAndLinkability {
  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    signable_tx_hash: [u8; 32],
    opening: OpenedInputTuple,
  ) -> (<Ed25519 as Ciphersuite>::G, SpendAuthAndLinkability) {
    let G = <Ed25519 as Ciphersuite>::G::generator();
    let T = EdwardsPoint(T());
    let U = EdwardsPoint(FCMP_U());
    let V = EdwardsPoint(FCMP_V());

    let L = (opening.input.I_tilde * opening.x) - (U * (opening.r_i * opening.x));

    let mut transcript = Blake2b512::new();
    transcript.update(signable_tx_hash);
    opening.input.transcript(&mut transcript, L);

    let alpha = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let beta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let delta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let mu = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let r_y = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let r_z = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let r_p = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let r_r_p = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));

    let x_r_i = Zeroizing::new(opening.x * opening.r_i);

    let P = (G * opening.x) + (V * opening.r_i) + (U * *x_r_i) + (T * *r_p);

    let alpha_G = G * *alpha;

    let A =
      alpha_G + (V * *beta) + (U * ((*alpha * opening.r_i) + (*beta * opening.x))) + (T * *delta);
    let B = (U * (*alpha * *beta)) + (T * *mu);

    let R_O = alpha_G + (T * *r_y);
    let R_P = (U * *r_z) + (T * *r_r_p);
    let R_L = (opening.input.I_tilde * *alpha) - (U * *r_z);

    transcript.update(P.to_bytes());
    transcript.update(A.to_bytes());
    transcript.update(B.to_bytes());
    transcript.update(R_O.to_bytes());
    transcript.update(R_P.to_bytes());
    transcript.update(R_L.to_bytes());

    let e = Scalar(DalekScalar::from_hash(transcript.clone()));

    let s_alpha = *alpha + (e * opening.x);
    let s_beta = *beta + (e * opening.r_i);
    let s_delta = *mu + (e * *delta) + (*r_p * e.square());
    let s_y = *r_y + (e * opening.y);
    // z is x_r_i
    let s_z = *r_z + (e * *x_r_i);
    // r_p is overloaded into r_p' and r_p'' by the paper, hence this distinguishing
    let r_p_double_quote = Zeroizing::new(*r_p - opening.y - opening.r_r_i);
    let s_r_p = *r_r_p + (e * *r_p_double_quote);

    (
      L,
      SpendAuthAndLinkability { P, A, B, R_O, R_P, R_L, s_alpha, s_beta, s_delta, s_y, s_z, s_r_p },
    )
  }

  #[allow(clippy::result_unit_err)]
  pub fn verify(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    verifier: &mut multiexp::BatchVerifier<(), <Ed25519 as Ciphersuite>::G>,
    signable_tx_hash: [u8; 32],
    input: &Input,
    L: <Ed25519 as Ciphersuite>::G,
  ) {
    let G = <Ed25519 as Ciphersuite>::G::generator();
    let T = EdwardsPoint(T());
    let U = EdwardsPoint(FCMP_U());
    let V = EdwardsPoint(FCMP_V());

    let mut transcript = Blake2b512::new();
    transcript.update(signable_tx_hash);
    input.transcript(&mut transcript, L);

    transcript.update(self.P.to_bytes());
    transcript.update(self.A.to_bytes());
    transcript.update(self.B.to_bytes());
    transcript.update(self.R_O.to_bytes());
    transcript.update(self.R_P.to_bytes());
    transcript.update(self.R_L.to_bytes());

    let e = Scalar(DalekScalar::from_hash(transcript.clone()));

    // BP+ Verification Statement
    verifier.queue(
      rng,
      (),
      [
        (e * e, self.P),
        (e, self.A),
        (Scalar::ONE, self.B),
        // RHS
        (-(self.s_alpha * e), G),
        (-(self.s_beta * e), V),
        (-(self.s_alpha * self.s_beta), U),
        (-self.s_delta, T),
      ],
    );

    // O_tilde GSP Verification Statement
    verifier.queue(
      rng,
      (),
      [
        (Scalar::ONE, self.R_O),
        (e, input.O_tilde),
        // RHS
        (-self.s_alpha, G),
        (-self.s_y, T),
      ],
    );

    // P' GSP Verification Statement
    verifier.queue(
      rng,
      (),
      [
        (Scalar::ONE, self.R_P),
        (e, (self.P - input.O_tilde - input.R)),
        // RHS
        (-self.s_z, U),
        (-self.s_r_p, T),
      ],
    );

    // L GSP Verification Statement
    verifier.queue(
      rng,
      (),
      [
        (Scalar::ONE, self.R_L),
        (e, L),
        // RHS
        (-self.s_alpha, input.I_tilde),
        // This term was supposed to be subtracted, so our negation cancels out
        (self.s_z, U),
      ],
    );
  }
}
