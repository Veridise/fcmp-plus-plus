use core::fmt::Display;

use ciphersuite::group::ff::PrimeField;
use crypto_bigint::{Encoding, NonZero, Uint, U512};

/// Field to a crypto bigint
fn field_to_bigint<const LIMBS: usize, F: PrimeField>(f: &F) -> Uint<LIMBS>
where
  Uint<LIMBS>: Encoding,
{
  let is_little_endian = F::ONE.to_repr().as_ref()[0] == 1;

  let repr = f.to_repr();
  let repr_bytes: &[u8] = repr.as_ref();

  let zero = Uint::<LIMBS>::ZERO;
  if is_little_endian {
    let mut repr = zero.to_le_bytes();
    let mut bytes: &mut [u8] = repr.as_mut();
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i] = *byte;
    }
    Uint::<LIMBS>::from_le_bytes(repr)
  } else {
    let mut repr = zero.to_be_bytes();
    let mut bytes: &mut [u8] = repr.as_mut();
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i + 8 * LIMBS - repr_bytes.len()] = *byte;
    }
    Uint::<LIMBS>::from_be_bytes(repr)
  }
}

// Decimal representation of a crypto bigint
fn bigint_to_decimal<const N: usize>(bigint: Uint<N>) -> String {
  if bigint.eq(&Uint::<N>::ZERO) {
    return "0".to_string();
  }
  let mut bigint = bigint;
  let mut digits: Vec<String> = vec![];
  let ten = NonZero::new(Uint::<N>::from_u8(10u8)).unwrap();
  while bigint > Uint::<N>::ZERO {
    let (quotient, remainder) = bigint.div_rem(&ten);
    let remainder: u64 = remainder.as_words()[0];
    digits.push(remainder.to_string());
    bigint = quotient;
  }

  let digits = digits.into_iter().rev().collect::<Vec<String>>();
  digits.join("")
}

pub(crate) fn fmt_modulus(modulus_hex: &str) -> String {
  let slice_start = if modulus_hex.starts_with("0x") { 2 } else { 0 };
  let mut modulus_hex = modulus_hex[slice_start..].to_string();
  let expected_length = 512 / 4;
  if modulus_hex.len() < expected_length {
    modulus_hex = "0".repeat(expected_length - modulus_hex.len()) + &modulus_hex;
  } else if modulus_hex.len() > expected_length {
    unimplemented!("Error: Fields larger than 512 bits are not supported");
  }
  let modulus: U512 = U512::from_be_hex(&modulus_hex);
  bigint_to_decimal(modulus)
}

/// Struct representing a bigint in a field
pub(crate) struct PrintableBigint {
  magnitude: U512,
  is_negative: bool,
}

impl PrintableBigint {
  pub(crate) fn from_field<F: PrimeField>(f: &F) -> Self {
    let magnitude: U512 = field_to_bigint(f);
    let neg_magnitude: U512 = field_to_bigint(&f.neg());
    // TODO: Determine if picus supports negative numbers
    // if magnitude.le(&neg_magnitude) {
    PrintableBigint { magnitude, is_negative: false }
    // }
    // else {
    //     PrintableBigint {
    //         magnitude: neg_magnitude,
    //         is_negative: true
    //     }
    // }
  }
}

impl Display for PrintableBigint {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let sign = if self.is_negative { "-" } else { "" };
    let magnitude = bigint_to_decimal(self.magnitude);
    write!(f, "{}{}", sign, magnitude)
  }
}

#[cfg(test)]
mod test {
  use ciphersuite::{Ciphersuite, Secp256k1};

  use crate::picus::field_utils::{bigint_to_decimal, field_to_bigint, PrintableBigint};

  use super::fmt_modulus;

  #[test]
  fn test_bigint_to_decimal() {
    const SELENE_MODULUS_STR: &str =
      "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";
    assert_eq!(
      "57896044618658097711785492504343953926549254372227246365156541811699034343327",
      fmt_modulus(SELENE_MODULUS_STR)
    );

    let formatted = PrintableBigint::from_field(&<Secp256k1 as Ciphersuite>::F::ONE).to_string();
    assert_eq!("1", formatted);
  }
}
