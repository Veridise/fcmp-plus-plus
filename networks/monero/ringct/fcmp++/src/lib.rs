#![allow(non_snake_case)]

use std_shims::sync::OnceLock;

use rand_core::{RngCore, CryptoRng};
use zeroize::Zeroize;

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use blake2::{Digest, Blake2b512};

use ciphersuite::{
  group::{ff::PrimeField, GroupEncoding},
  Ciphersuite, Ed25519, Helios, Selene,
};

use generalized_bulletproofs::Generators;
use generalized_bulletproofs_ec_gadgets::*;
pub use fcmps;
use fcmps::*;

use monero_io::write_varint;
use monero_primitives::keccak256;

/// The Spend-Authorization and Linkability proof.
pub mod sal;
use sal::*;

#[cfg(test)]
mod tests;

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

pub type Output = fcmps::Output<<Ed25519 as Ciphersuite>::G>;

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
