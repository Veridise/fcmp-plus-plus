use core::fmt::{self, Display, Formatter};

use ciphersuite::group::ff::PrimeField;
use crypto_bigint::{NonZero, U512, Encoding};

use super::{
  PicusContext, PicusExpression, PicusModule, PicusProgram, PicusStatement, PicusTerm,
  PicusVariable,
};

trait DisplayWithContext {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result;
}

/// A generic wrapper type that pairs an object with its context.
pub(crate) struct WithContext<'a, 'b, T: ?Sized> {
  pub value: &'a T,
  pub context: &'b PicusContext,
}

/// Implement standard Display for the wrapper by calling the object's DisplayWithContext implementation.
impl<'a, 'b, T> Display for Box<WithContext<'a, 'b, T>>
where
  T: DisplayWithContext,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    self.value.fmt(f, self.context)
  }
}

/// Trait auto-implemented for any struct which can be displayed with a context.
/// This allows us to use the write!() macro by just appending .with(&context)
pub(crate) trait WithContextExt {
  fn with<'a, 'b>(&'a self, context: &'b PicusContext) -> Box<WithContext<'a, 'b, Self>> {
    Box::new(WithContext { value: self, context })
  }
}

impl<T: DisplayWithContext> WithContextExt for T {}

impl DisplayWithContext for PicusVariable {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match context.get_variable_name(self.0) {
      Some(name) => write!(f, "{}", name),
      None => {
        if self.0 >= context.get_num_variables() {
          Err(fmt::Error)
        } else {
          write!(f, "var_{}", self.0)
        }
      }
    }
  }
}

fn field_to_bigint<F: PrimeField>(f: &F) -> U512 {
  let is_little_endian = F::ONE.to_repr().as_ref()[0] == 1;

  let repr = f.to_repr();
  let repr_bytes: &[u8] = repr.as_ref();
  assert!(repr_bytes.len() <= 64);

  let mut bytes: [u8; 64] = [0; 64];
  if is_little_endian {
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i] = *byte;
    }
    U512::from_le_bytes(bytes)
  }
  else {
    for (i, byte) in repr_bytes.iter().enumerate() {
      bytes[i + 64 - repr_bytes.len()] = *byte;
    }
    U512::from_be_bytes(bytes)
  }
}

fn bigint_to_decimal(bigint: U512) -> String {
  if bigint.eq(&U512::ZERO) {
    return "0".to_string();
  }
  let mut bigint = bigint;
  let mut digits: Vec<String> = vec![];
  let ten = NonZero::new(U512::from_u8(10u8)).unwrap();
  while bigint > U512::ZERO {
    let (quotient, remainder) = bigint.div_rem(&ten);
    let remainder: u64 = remainder.as_words()[0];
    digits.push(remainder.to_string());
    bigint = quotient;
  }

  let digits = digits.into_iter().rev().collect::<Vec<String>>();
  digits.join("")
}

impl<F: PrimeField> DisplayWithContext for PicusTerm<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusTerm::Constant(value) => {
        let bigint: U512 = field_to_bigint(value);
        let decimal_representation = bigint_to_decimal(bigint);
        write!(f, "{}", decimal_representation)
      }
      PicusTerm::Variable(variable) => write!(f, "{}", variable.with(context)),
    }
  }
}

impl<F: PrimeField> DisplayWithContext for PicusExpression<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusExpression::PicusTerm(term) => term.fmt(f, context),
      PicusExpression::IsEqual(args) => {
        write!(f, "(= {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Multiply(args) => {
        write!(f, "(* {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Add(args) => {
        write!(f, "(+ {} {})", args.left.with(context), args.right.with(context))
      }
      PicusExpression::Subtract(args) => {
        write!(f, "(- {} {})", args.left.with(context), args.right.with(context))
      }
    }
  }
}

impl<F: PrimeField> DisplayWithContext for PicusStatement<F> {
  fn fmt(&self, f: &mut Formatter<'_>, context: &PicusContext) -> std::fmt::Result {
    match self {
      PicusStatement::Assert(expression) => write!(f, "  (assert {})", expression.with(context))?,
      PicusStatement::Assume(expression) => write!(f, "  (assume {})", expression.with(context))?,
    }
    Ok(())
  }
}

impl<F: PrimeField> Display for PicusModule<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "(begin-module {})", self.name)?;

    // Print declarations
    for (var_index, var_info) in self.context.variable_info.iter().enumerate() {
      let modifier = if var_info.is_input { "input" } else { "output" };
      writeln!(f, "  ({} {})", modifier, PicusVariable(var_index).with(&self.context))?;
    }

    // Print statements
    for statement in &self.statements {
      writeln!(f, "{}", statement.with(&self.context))?;
    }

    write!(f, "(end-module)")?;
    Ok(())
  }
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

impl<F: PrimeField> Display for PicusProgram<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    let decimal_representation = fmt_modulus(F::MODULUS);
    writeln!(f, "(prime-number {})", decimal_representation)?;
    for module in &self.modules {
      writeln!(f, "{}", module)?;
    }
    Ok(())
  }
}

#[cfg(test)]
mod test {
use ciphersuite::{Ciphersuite, Secp256k1};

use crate::picus::printer::{bigint_to_decimal, field_to_bigint, fmt_modulus};

  #[test]
  fn test_bigint_to_decimal() {
    const SELENE_MODULUS_STR: &str = "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";
    assert_eq!("57896044618658097711785492504343953926549254372227246365156541811699034343327", fmt_modulus(SELENE_MODULUS_STR));

    assert_eq!("1", bigint_to_decimal(field_to_bigint(&<Secp256k1 as Ciphersuite>::F::ONE)));
  }
}