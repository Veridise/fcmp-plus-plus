use core::fmt::Display;

use ciphersuite::group::ff::PrimeField;
use crypto_bigint::{Encoding, NonZero, Uint, U512};

/// Field to a crypto bigint
fn field_to_bigint<const N: usize, F: PrimeField>(f: &F) -> Uint<N>
where Uint<N>: Encoding
{
  let is_little_endian = F::ONE.to_repr().as_ref()[0] == 1;

  let repr = f.to_repr();
  let repr_bytes: &[u8] = repr.as_ref();

  let zero = Uint::<N>::ZERO;
  if is_little_endian {
    let mut repr = zero.to_le_bytes();
    let mut bytes: &mut [u8] = repr.as_mut();
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i] = *byte;
    }
    Uint::<N>::from_le_bytes(repr)
  }
  else {
    let mut repr = zero.to_be_bytes();
    let mut bytes: &mut [u8] = repr.as_mut();
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i + N / 8 - repr_bytes.len()] = *byte;
    }
    Uint::<N>::from_be_bytes(repr)
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

fn fmt_modulus(modulus_hex: &str) -> String {
    let slice_start = if modulus_hex.starts_with("0x") {
      2
    } else {
      0
    };
    let mut modulus_hex = modulus_hex[slice_start..].to_string();
    let expected_length = 512 / 4;
    if modulus_hex.len() < expected_length {
      modulus_hex = "0".repeat(expected_length - modulus_hex.len()) + &modulus_hex;
    } else if modulus_hex.len() > expected_length {
      unimplemented!("Error: Fields larger than 512 bits are not supported");
    }
    let modulus: U512= U512::from_be_hex(&modulus_hex);
    bigint_to_decimal(modulus)
}

/// Struct representing a bigint in a field
struct PrintableBigint<const N: usize> where Uint<N>: Encoding {
    magnitude: Uint<N>,
    is_negative: bool,
}

impl<const N: usize> PrintableBigint<N> where Uint<N>: Encoding {
    fn from_field<F: PrimeField>(f: &F) -> Self {
        let magnitude = field_to_bigint(f);
        let neg_magnitude = field_to_bigint(&f.neg());
        if magnitude.le(&neg_magnitude) {
            PrintableBigint {
                magnitude,
                is_negative: false
            }
        }
        else {
            PrintableBigint {
                magnitude: neg_magnitude,
                is_negative: true
            }
        }
    }
}

impl<const N: usize> Display for PrintableBigint<N> where Uint<N>: Encoding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let sign = if self.is_negative {
            "-"
        } else {
            ""
        };
        let magnitude = bigint_to_decimal(self.magnitude);
        write!(f, "{}{}", sign, magnitude)
    }
}
