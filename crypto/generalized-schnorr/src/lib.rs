#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

use core::ops::Deref;
#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;
use std_shims::io::{self, Read, Write};

use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, Zeroizing};

use blake2::{Digest, Blake2b512};

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};
use multiexp::{multiexp_vartime, BatchVerifier};

#[cfg(feature = "mpc")]
mod mpc;

#[cfg(test)]
mod tests;

/// A Generalized Schnorr Proof.
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct GeneralizedSchnorr<
  C: Ciphersuite,
  const OUTPUTS: usize,
  const SCALARS: usize,
  const SCALARS_PLUS_TWO: usize,
> {
  pub R: [C::G; OUTPUTS],
  pub s: [C::F; SCALARS],
}

impl<C: Ciphersuite, const OUTPUTS: usize, const SCALARS: usize, const SCALARS_PLUS_TWO: usize>
  GeneralizedSchnorr<C, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>
{
  /// Read a GeneralizedSchnorr from something implementing Read.
  pub fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
    let mut R = [C::G::identity(); OUTPUTS];
    for R in &mut R {
      *R = C::read_G(reader)?;
    }
    let mut s = [C::F::ZERO; SCALARS];
    for s in &mut s {
      *s = C::read_F(reader)?;
    }
    Ok(Self { R, s })
  }

  /// Write a GeneralizedSchnorr to something implementing Read.
  pub fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
    for R in self.R {
      writer.write_all(R.to_bytes().as_ref())?;
    }
    for s in self.s {
      writer.write_all(s.to_repr().as_ref())?;
    }
    Ok(())
  }

  fn challenge(context: [u8; 32], outputs: [C::G; OUTPUTS], nonces: [C::G; OUTPUTS]) -> C::F {
    let mut hasher = Blake2b512::new();
    hasher.update(context);
    for output in outputs {
      hasher.update(output.to_bytes());
    }
    for nonce in nonces {
      hasher.update(nonce.to_bytes());
    }

    // Ensure this field is small enough this is a successful wide reduction
    assert!(C::F::NUM_BITS <= (512 - 128));

    let mut res = C::F::ZERO;
    for (i, mut byte) in hasher.finalize().into_iter().enumerate() {
      for j in 0 .. 8 {
        let lsb = byte & 1;
        let mut bit = C::F::from(u64::from(lsb));
        for _ in 0 .. ((i * 8) + j) {
          bit = bit.double();
        }
        res += bit;

        byte >>= 1;
      }
    }

    // Negligible probability
    if bool::from(res.is_zero()) {
      panic!("zero challenge");
    }

    res
  }

  /// Serialize a GeneralizedSchnorr, returning a `Vec<u8>`.
  #[cfg(feature = "std")]
  pub fn serialize(&self) -> Vec<u8> {
    let mut buf = vec![];
    self.write(&mut buf).unwrap();
    buf
  }

  /// Prove a Generalized Schnorr statement.
  ///
  /// The matrix is assumed to be transcribed within the context.
  ///
  /// Returns the outputs and the proof for them.
  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    context: [u8; 32],
    matrix: [[C::G; SCALARS]; OUTPUTS],
    scalars: [&Zeroizing<C::F>; SCALARS],
  ) -> ([C::G; OUTPUTS], Self) {
    let outputs: [C::G; OUTPUTS] = core::array::from_fn(|i| {
      matrix[i].iter().zip(scalars.iter()).map(|(generator, scalar)| *generator * ***scalar).sum()
    });

    let nonces: [Zeroizing<C::F>; SCALARS] =
      core::array::from_fn(|_| Zeroizing::new(C::F::random(&mut *rng)));
    let R = core::array::from_fn(|i| {
      matrix[i].iter().zip(nonces.iter()).map(|(generator, nonce)| *generator * **nonce).sum()
    });

    let c = Self::challenge(context, outputs, R);
    (outputs, Self { R, s: core::array::from_fn(|i| (c * scalars[i].deref()) + nonces[i].deref()) })
  }

  /// Return the series of pairs whose products sum to zero for a valid signature.
  ///
  /// This is intended to be used with a multiexp for efficient batch verification.
  fn batch_statements(
    &self,
    context: [u8; 32],
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) -> [[(C::F, C::G); SCALARS_PLUS_TWO]; OUTPUTS] {
    assert_eq!(SCALARS_PLUS_TWO, SCALARS + 2);
    let c = Self::challenge(context, outputs, self.R);
    core::array::from_fn(|i| {
      core::array::from_fn(|j| {
        if j == SCALARS {
          (-C::F::ONE, self.R[i])
        } else if j == (SCALARS + 1) {
          (-c, outputs[i])
        } else {
          (self.s[j], matrix[i][j])
        }
      })
    })
  }

  /// Verify a Generalized Schnorr proof.
  ///
  /// The matrix is assumed to be transcribed within the context.
  #[must_use]
  pub fn verify(
    &self,
    context: [u8; 32],
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) -> bool {
    for statements in self.batch_statements(context, matrix, outputs) {
      if !bool::from(multiexp_vartime(statements.as_slice()).is_identity()) {
        return false;
      }
    }
    true
  }

  /// Queue a proof for batch verification.
  ///
  /// The matrix is assumed to be transcribed within the context.
  pub fn batch_verify<R: RngCore + CryptoRng, I: Copy + Zeroize>(
    &self,
    rng: &mut R,
    batch: &mut BatchVerifier<I, C::G>,
    id: I,
    context: [u8; 32],
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) {
    for statements in self.batch_statements(context, matrix, outputs) {
      batch.queue(rng, id, statements);
    }
  }
}
