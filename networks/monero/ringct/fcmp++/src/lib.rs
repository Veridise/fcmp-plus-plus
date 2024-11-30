#![cfg_attr(docsrs, feature(doc_auto_cfg))]
// #![doc = include_str!("../README.md")] TODO
#![cfg_attr(not(feature = "std"), no_std)]
// #![deny(missing_docs)] TODO
#![allow(non_snake_case)]

use std_shims::{sync::OnceLock, vec, vec::Vec, io};

use rand_core::{RngCore, CryptoRng};
use zeroize::Zeroize;

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use blake2::{Digest, Blake2b512};

use dalek_ff_group::EdwardsPoint;
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
use monero_generators::{T, FCMP_U, FCMP_V};

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
pub fn HELIOS_HASH_INIT() -> <Helios as Ciphersuite>::G {
  *HELIOS_HASH_INIT_CELL
    .get_or_init(|| hash_to_point_on_curve::<Helios>(b"Monero Helios Hash Initializer"))
}

static SELENE_HASH_INIT_CELL: OnceLock<<Selene as Ciphersuite>::G> = OnceLock::new();
pub fn SELENE_HASH_INIT() -> <Selene as Ciphersuite>::G {
  *SELENE_HASH_INIT_CELL
    .get_or_init(|| hash_to_point_on_curve::<Selene>(b"Monero Selene Hash Initializer"))
}

static HELIOS_GENERATORS_CELL: OnceLock<Generators<Helios>> = OnceLock::new();
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

static FCMP_PARAMS_CELL: OnceLock<FcmpParams<Curves>> = OnceLock::new();
pub fn FCMP_PARAMS() -> &'static FcmpParams<Curves> {
  FCMP_PARAMS_CELL.get_or_init(|| {
    FcmpParams::<Curves>::new(
      SELENE_GENERATORS().clone(),
      HELIOS_GENERATORS().clone(),
      // Hash init generators
      SELENE_HASH_INIT(),
      HELIOS_HASH_INIT(),
      // G, T, U, V
      <Ed25519 as Ciphersuite>::generator(),
      EdwardsPoint(T()),
      EdwardsPoint(FCMP_U()),
      EdwardsPoint(FCMP_V()),
    )
  })
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Input {
  O_tilde: <Ed25519 as Ciphersuite>::G,
  I_tilde: <Ed25519 as Ciphersuite>::G,
  R: <Ed25519 as Ciphersuite>::G,
  C_tilde: <Ed25519 as Ciphersuite>::G,
}

impl Input {
  fn write_partial(&self, writer: &mut impl io::Write) -> io::Result<()> {
    writer.write_all(&self.O_tilde.to_bytes())?;
    writer.write_all(&self.I_tilde.to_bytes())?;
    writer.write_all(&self.R.to_bytes())
  }

  fn read_partial(
    C_tilde: <Ed25519 as Ciphersuite>::G,
    reader: &mut impl io::Read,
  ) -> io::Result<Input> {
    Ok(Self {
      O_tilde: Ed25519::read_G(reader)?,
      I_tilde: Ed25519::read_G(reader)?,
      R: Ed25519::read_G(reader)?,
      C_tilde,
    })
  }

  fn write_full(&self, writer: &mut impl io::Write) -> io::Result<()> {
    self.write_partial(writer)?;
    writer.write_all(&self.C_tilde.to_bytes())
  }

  fn read_full(reader: &mut impl io::Read) -> io::Result<Input> {
    let mut OIR = [0; 3 * 32];
    reader.read_exact(&mut OIR)?;
    let C_tilde = Ed25519::read_G(reader)?;
    Self::read_partial(C_tilde, &mut OIR.as_slice())
  }

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
  inputs: Vec<(Input, SpendAuthAndLinkability)>,
  fcmp: Fcmp<Curves>,
}

impl FcmpPlusPlus {
  pub fn new(inputs: Vec<(Input, SpendAuthAndLinkability)>, fcmp: Fcmp<Curves>) -> FcmpPlusPlus {
    FcmpPlusPlus { inputs, fcmp }
  }

  pub fn proof_size(inputs: usize, layers: usize) -> usize {
    // Each input tuple, without C~, each SAL, and the FCMP
    (inputs * ((3 * 32) + (12 * 32))) + Fcmp::<Curves>::proof_size(inputs, layers)
  }

  pub fn write(&self, writer: &mut impl io::Write) -> io::Result<()> {
    for (input, spend_auth_and_linkability) in &self.inputs {
      input.write_partial(writer)?;
      spend_auth_and_linkability.write(writer)?;
    }
    self.fcmp.write(writer)
  }

  /// Read an FCMP++.
  ///
  /// The pseudo-outs are passed in as Monero already defines a field for them. It's less annoying
  /// to receive them here than to move them into here and expose them to Monero. It also informs
  /// us of how many inputs we're reading a proof for.
  ///
  /// The amount of layers for the FCMP are also passed in here as the FCMP's length is variable to
  /// that.
  pub fn read(
    pseudo_outs: &[[u8; 32]],
    layers: usize,
    reader: &mut impl io::Read,
  ) -> io::Result<Self> {
    let mut inputs = vec![];
    for pseudo_out in pseudo_outs {
      let C_tilde = Ed25519::read_G(&mut pseudo_out.as_slice())?;
      inputs.push((Input::read_partial(C_tilde, reader)?, SpendAuthAndLinkability::read(reader)?));
    }
    let fcmp = Fcmp::read(reader, pseudo_outs.len(), layers)?;
    Ok(Self { inputs, fcmp })
  }

  #[allow(clippy::too_many_arguments, clippy::result_unit_err)]
  pub fn verify(
    &self,
    rng: &mut (impl RngCore + CryptoRng),
    verifier_ed: &mut multiexp::BatchVerifier<(), <Ed25519 as Ciphersuite>::G>,
    verifier_1: &mut generalized_bulletproofs::BatchVerifier<Selene>,
    verifier_2: &mut generalized_bulletproofs::BatchVerifier<Helios>,
    tree: TreeRoot<<Curves as FcmpCurves>::C1, <Curves as FcmpCurves>::C2>,
    layers: usize,
    signable_tx_hash: [u8; 32],
    key_images: Vec<<Ed25519 as Ciphersuite>::G>,
  ) -> Result<(), ()> {
    if self.inputs.len() != key_images.len() {
      Err(())?;
    }

    let mut fcmp_inputs = Vec::with_capacity(self.inputs.len());
    for ((input, spend_auth_and_linkability), key_image) in self.inputs.iter().zip(key_images) {
      spend_auth_and_linkability.verify(rng, verifier_ed, signable_tx_hash, input, key_image);

      fcmp_inputs
        .push(fcmps::Input::new(input.O_tilde, input.I_tilde, input.R, input.C_tilde).ok_or(())?);
    }

    self.fcmp.verify(rng, verifier_1, verifier_2, FCMP_PARAMS(), tree, layers, &fcmp_inputs)
  }
}
