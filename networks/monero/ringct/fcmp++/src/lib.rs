#![allow(non_snake_case)]

use std_shims::sync::OnceLock;

use rand_core::{RngCore, CryptoRng};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use blake2::{Digest, Blake2b512};

use curve25519_dalek::Scalar as DalekScalar;
use dalek_ff_group::{Scalar, EdwardsPoint};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite, Ed25519, Helios, Selene,
};

use generalized_bulletproofs::Generators;
use generalized_bulletproofs_ec_gadgets::*;
use fcmps::*;

use monero_io::write_varint;
use monero_primitives::keccak256;
use monero_generators::{T, FCMP_U, FCMP_V};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ed25519Params;
impl DiscreteLogParameters for Ed25519Params {
  type ScalarBits = U<{ <<Ed25519 as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SeleneParams;
impl DiscreteLogParameters for SeleneParams {
  type ScalarBits = U<{ <<Selene as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeliosParams;
impl DiscreteLogParameters for HeliosParams {
  type ScalarBits = U<{ <<Helios as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Curves;
impl FcmpCurves for Curves {
  type OC = Ed25519;
  type OcParameters = Ed25519Params;
  type C1 = Selene;
  type C1Parameters = SeleneParams;
  type C2 = Helios;
  type C2Parameters = HeliosParams;
}

fn hash_to_point_on_curve<C: Ciphersuite>(buf: &[u8]) -> C::G {
  let mut buf = keccak256(buf);
  let mut repr = <C::G as GroupEncoding>::Repr::default();
  loop {
    repr.as_mut().copy_from_slice(&buf);
    if let Ok(point) = C::read_G(&mut repr.as_ref()) {
      return point;
    }
    buf = keccak256(buf);
  }
}

static HELIOS_HASH_INIT_CELL: OnceLock<<Helios as Ciphersuite>::G> = OnceLock::new();
#[allow(non_snake_case)]
pub fn HELIOS_HASH_INIT() -> <Helios as Ciphersuite>::G {
  *HELIOS_HASH_INIT_CELL
    .get_or_init(|| hash_to_point_on_curve::<Helios>(b"Monero Helios Hash Initializer"))
}

static SELENE_HASH_INIT_CELL: OnceLock<<Selene as Ciphersuite>::G> = OnceLock::new();
#[allow(non_snake_case)]
pub fn SELENE_HASH_INIT() -> <Selene as Ciphersuite>::G {
  *SELENE_HASH_INIT_CELL
    .get_or_init(|| hash_to_point_on_curve::<Selene>(b"Monero Selene Hash Initializer"))
}

static HELIOS_GENERATORS_CELL: OnceLock<Generators<Helios>> = OnceLock::new();
#[allow(non_snake_case)]
pub fn HELIOS_GENERATORS() -> &'static Generators<Helios> {
  HELIOS_GENERATORS_CELL.get_or_init(|| {
    let g = hash_to_point_on_curve::<Helios>(b"Monero Helios G");
    let h = hash_to_point_on_curve::<Helios>(b"Monero Helios H");
    let mut g_bold = Vec::with_capacity(512);
    let mut h_bold = Vec::with_capacity(512);
    for i in 0u32 .. 512 {
      let mut g_buf = b"Monero Helios G ".to_vec();
      write_varint(&i, &mut g_buf).unwrap();
      g_bold.push(hash_to_point_on_curve::<Helios>(&g_buf));

      let mut h_buf = b"Monero Helios H ".to_vec();
      write_varint(&i, &mut h_buf).unwrap();
      h_bold.push(hash_to_point_on_curve::<Helios>(&h_buf));
    }
    Generators::new(g, h, g_bold, h_bold).unwrap()
  })
}

static SELENE_GENERATORS_CELL: OnceLock<Generators<Selene>> = OnceLock::new();
#[allow(non_snake_case)]
pub fn SELENE_GENERATORS() -> &'static Generators<Selene> {
  SELENE_GENERATORS_CELL.get_or_init(|| {
    let g = hash_to_point_on_curve::<Selene>(b"Monero Selene G");
    let h = hash_to_point_on_curve::<Selene>(b"Monero Selene H");
    let mut g_bold = Vec::with_capacity(512);
    let mut h_bold = Vec::with_capacity(512);
    for i in 0u32 .. 512 {
      let mut g_buf = b"Monero Selene G ".to_vec();
      write_varint(&i, &mut g_buf).unwrap();
      g_bold.push(hash_to_point_on_curve::<Selene>(&g_buf));

      let mut h_buf = b"Monero Selene H ".to_vec();
      write_varint(&i, &mut h_buf).unwrap();
      h_bold.push(hash_to_point_on_curve::<Selene>(&h_buf));
    }
    Generators::new(g, h, g_bold, h_bold).unwrap()
  })
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Input {
  O_tilde: <Ed25519 as Ciphersuite>::G,
  I_tilde: <Ed25519 as Ciphersuite>::G,
  C_tilde: <Ed25519 as Ciphersuite>::G,
  R: <Ed25519 as Ciphersuite>::G,
}

impl Input {
  fn transcript(&self, transcript: &mut Blake2b512, L: <Ed25519 as Ciphersuite>::G) {
    transcript.update(self.O_tilde.to_bytes());
    transcript.update(self.I_tilde.to_bytes());
    transcript.update(self.C_tilde.to_bytes());
    transcript.update(self.R.to_bytes());
    transcript.update(L.to_bytes());
  }
}

#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct RerandomizedOutput {
  input: Input,
  r_o: <Ed25519 as Ciphersuite>::F,
  r_i: <Ed25519 as Ciphersuite>::F,
  r_j: <Ed25519 as Ciphersuite>::F,
  r_c: <Ed25519 as Ciphersuite>::F,
}

impl RerandomizedOutput {
  pub fn new(
    rng: &mut (impl RngCore + CryptoRng),
    output: Output<EdwardsPoint>,
  ) -> RerandomizedOutput {
    let r_o = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_i = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_j = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_c = <Ed25519 as Ciphersuite>::F::random(&mut *rng);

    let O_tilde = output.O() + (EdwardsPoint(T()) * r_o);
    let I_tilde = output.I() + (EdwardsPoint(FCMP_U()) * r_i);
    let R = (EdwardsPoint(FCMP_V()) * r_i) + (EdwardsPoint(T()) * r_j);
    let C_tilde = output.C() + (<Ed25519 as Ciphersuite>::generator() * r_c);

    RerandomizedOutput { input: Input { O_tilde, I_tilde, R, C_tilde }, r_o, r_i, r_j, r_c }
  }

  pub fn input(&self) -> Input {
    self.input
  }
}

/// The opening for the O, I, R of an Input tuple.
///
/// This does not open C as it's unnecessary for the purposes of this proof.
#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct OpenedInputTuple {
  input: Input,
  // O~ = xG + yT
  x: <Ed25519 as Ciphersuite>::F,
  y: <Ed25519 as Ciphersuite>::F,
  // R = r_i V + r_j T
  r_i: <Ed25519 as Ciphersuite>::F,
  r_j: <Ed25519 as Ciphersuite>::F,
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
      r_j: rerandomized_output.r_j,
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

    let L = (opening.input.I_tilde * opening.x) - (U * opening.r_i);

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
    let r_p_double_quote = Zeroizing::new(*r_p - opening.y - opening.r_j);
    let s_r_p = *r_r_p + (e * *r_p_double_quote);

    (
      L,
      SpendAuthAndLinkability { P, A, B, R_O, R_P, R_L, s_alpha, s_beta, s_delta, s_y, s_z, s_r_p },
    )
  }

  #[allow(unused, clippy::result_unit_err)]
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

#[derive(Clone, Debug, Zeroize)]
pub struct FcmpPlusPlus {
  input: Input,
  fcmp: Fcmp<Curves>,
  spend_auth_and_linkability: SpendAuthAndLinkability,
}

impl FcmpPlusPlus {
  pub fn new(
    input: Input,
    fcmp: Fcmp<Curves>,
    spend_auth_and_linkability: SpendAuthAndLinkability,
  ) -> FcmpPlusPlus {
    FcmpPlusPlus { input, fcmp, spend_auth_and_linkability }
  }

  #[allow(clippy::too_many_arguments, clippy::result_unit_err)]
  pub fn verify(
    self,
    rng: &mut (impl RngCore + CryptoRng),
    verifier_ed: &mut multiexp::BatchVerifier<(), <Ed25519 as Ciphersuite>::G>,
    verifier_1: &mut generalized_bulletproofs::BatchVerifier<Selene>,
    verifier_2: &mut generalized_bulletproofs::BatchVerifier<Helios>,
    params: &FcmpParams<Curves>,
    tree: TreeRoot<<Curves as FcmpCurves>::C1, <Curves as FcmpCurves>::C2>,
    layers: usize,
    signable_tx_hash: [u8; 32],
    key_image: <Ed25519 as Ciphersuite>::G,
  ) -> Result<(), ()> {
    self.spend_auth_and_linkability.verify(
      rng,
      verifier_ed,
      signable_tx_hash,
      &self.input,
      key_image,
    );

    let fcmp_input =
      fcmps::Input::new(self.input.O_tilde, self.input.I_tilde, self.input.R, self.input.C_tilde)
        .ok_or(())?;
    self.fcmp.verify(rng, verifier_1, verifier_2, params, tree, layers, &[fcmp_input])
  }
}
