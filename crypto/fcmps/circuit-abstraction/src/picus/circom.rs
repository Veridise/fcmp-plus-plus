use ciphersuite::group::ff::PrimeField;

use super::{
  BinaryOperatorArgs, PicusContext, PicusExpression, PicusModule, PicusProgram, PicusStatement, PicusTerm, PicusVariable
};
use super::printer::WithContextExt;

struct PicusToCircomContext<F: PrimeField> {
  inside_is_equal: bool,
  inside_mul: bool,
  module: PicusModule<F>,
}

trait CircomNormalizer<F: PrimeField> {
  type Output;
  // normalize the program for lowering to circom, i.e.
  // flattening all nested multiplications
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self::Output, String>;
}

impl<F: PrimeField> CircomNormalizer<F> for PicusVariable {
  type Output = Self;
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self, String> {
    Ok(self)
  }
}

impl<F: PrimeField> CircomNormalizer<F> for PicusTerm<F> {
  type Output = Self;
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self, String> {
    Ok(self)
  }
}

impl<F: PrimeField> CircomNormalizer<F> for BinaryOperatorArgs<F> {
  type Output = Self;
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self, String> {
    Ok(BinaryOperatorArgs {
      left: Box::new(self.left.normalize_for_circom(circom_context)?),
      right: Box::new(self.right.normalize_for_circom(circom_context)?),
    })
  }
}

impl<F: PrimeField> CircomNormalizer<F> for PicusExpression<F> {
  type Output = Self;
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self, String> {
    match self {
      PicusExpression::PicusTerm(_) => Ok(self),
      PicusExpression::IsEqual(binary_operator_args) => {
        if circom_context.inside_is_equal {
          Result::Err("Nested equality assertions are not supported".to_string())
        } else {
          let old_inside_is_equal = circom_context.inside_is_equal;
          circom_context.inside_is_equal = true;
          let normalized = binary_operator_args.normalize_for_circom(circom_context)?;
          circom_context.inside_is_equal = old_inside_is_equal;
          Ok(PicusExpression::IsEqual(normalized))
        }
      }
      PicusExpression::Multiply(binary_operator_args) => {
        // Normalize child
        let inside_mul = circom_context.inside_mul;
        circom_context.inside_mul = true;
        let normalized =
          PicusExpression::Multiply(binary_operator_args.normalize_for_circom(circom_context)?);
        circom_context.inside_mul = inside_mul;

        // If inside an outer multiplication, make an intermediate variable to hold
        // the result of the multiplication, constrain it, and return the intermediate variable
        if inside_mul {
          let result_variable: PicusExpression<F> =
            circom_context.module.fresh_variable(None).unwrap().into();
          circom_context
            .module
            .add_statement(PicusStatement::Assert(result_variable.clone().equals(normalized)));
          Ok(result_variable)
        } else {
          Ok(normalized)
        }
      }
      PicusExpression::Add(binary_operator_args) => {
        Ok(PicusExpression::Add(binary_operator_args.normalize_for_circom(circom_context)?))
      }
      PicusExpression::Subtract(binary_operator_args) => {
        Ok(PicusExpression::Subtract(binary_operator_args.normalize_for_circom(circom_context)?))
      }
    }
  }
}

impl<F: PrimeField> CircomNormalizer<F> for PicusStatement<F> {
  type Output = Self;
  fn normalize_for_circom(
    self,
    circom_context: &mut PicusToCircomContext<F>,
  ) -> Result<Self, String> {
    Ok(match self {
      PicusStatement::Assert(picus_expression) => {
        PicusStatement::Assert(picus_expression.normalize_for_circom(circom_context)?)
      }
      PicusStatement::Assume(picus_expression) => {
        PicusStatement::Assume(picus_expression.normalize_for_circom(circom_context)?)
      }
    })
  }
}

trait CircomPrinter {
  // Prints to circom. This trait is not public since, when calling recursively, we will assume that the
  // picus module being proven has been normalized to not have nested multiplications
  fn to_circom(&self, context: &PicusContext) -> Result<String, String>;
}

impl CircomPrinter for PicusVariable {
  fn to_circom(&self, context: &PicusContext) -> Result<String, String> {
    Ok(format!("{}", self.with(context)))
  }
}

impl<F: PrimeField> CircomPrinter for PicusTerm<F> {
  fn to_circom(&self, context: &PicusContext) -> Result<String, String> {
    Ok(format!("{}", self.with(context)))
  }
}

impl<F: PrimeField> CircomPrinter for PicusExpression<F> {
  /// This implementation assumes the expression has been normalized!
  fn to_circom(&self, context: &PicusContext) -> Result<String, String> {
    match self {
      PicusExpression::PicusTerm(picus_term) => picus_term.to_circom(context),
      PicusExpression::IsEqual(binary_operator_args) => Ok(format!(
        "{} === {}",
        binary_operator_args.left.as_ref().to_circom(context)?,
        binary_operator_args.right.as_ref().to_circom(context)?,
      )),
      PicusExpression::Multiply(binary_operator_args) => Ok(format!(
        "({}) * ({})",
        binary_operator_args.left.as_ref().to_circom(context)?,
        binary_operator_args.right.as_ref().to_circom(context)?,
      )),
      PicusExpression::Add(binary_operator_args) => Ok(format!(
        "{} + {}",
        binary_operator_args.left.as_ref().to_circom(context)?,
        binary_operator_args.right.as_ref().to_circom(context)?,
      )),
      PicusExpression::Subtract(binary_operator_args) => Ok(format!(
        "{} - {}",
        binary_operator_args.left.as_ref().to_circom(context)?,
        binary_operator_args.right.as_ref().to_circom(context)?,
      )),
    }
  }
}

impl<F: PrimeField> CircomPrinter for PicusStatement<F> {
  fn to_circom(&self, context: &PicusContext) -> Result<String, String> {
    match self {
      PicusStatement::Assert(picus_expression) | PicusStatement::Assume(picus_expression) => {
        Ok(format!("{};", picus_expression.to_circom(context)?))
      }
    }
  }
}

impl<F: PrimeField> PicusModule<F> {
  fn to_circom(&self) -> Result<String, String> {
    // Create empty module with the same variables
    let mut normalized_module: PicusModule<F> = PicusModule::<F>::new(self.name.clone());
    for variable_index in 0..self.num_variables() {
      normalized_module
        .fresh_variable(self.context.get_variable_name(variable_index).map(|x| x.as_str()))?;
    }
    for input_variable in &self.input_variables {
      normalized_module.mark_variable_as_input(*input_variable)?;
    }

    // Put normalized copies of all program statements into the normalized module
    let mut circom_context =
      PicusToCircomContext { inside_is_equal: false, inside_mul: false, module: normalized_module };
    self
      .statements
      .iter()
      .cloned()
      .map(|statement| statement.normalize_for_circom(&mut circom_context))
      .collect::<Result<Vec<_>, _>>()?
      .into_iter()
      .for_each(|statement| circom_context.module.add_statement(statement));

    // Done mutating normalized_module
    let normalized_module = circom_context.module;

    let declarations = (0..normalized_module.num_variables())
      .map(PicusVariable)
      .map(|var| {
        let modifier =
          if normalized_module.input_variables.contains(&var) { "input" } else { "output" };
        var.to_circom(&normalized_module.context).map(|var| format!("signal {} {};", modifier, var))
      })
      .collect::<Result<Vec<String>, _>>()?
      .join("\n  ");

    let constraints = normalized_module
      .statements
      .iter()
      .map(|statement| statement.to_circom(&normalized_module.context))
      .collect::<Result<Vec<String>, _>>()?
      .join("\n  ");
    Ok(format!(
      "template {} {{\n  // Declarations\n  {}\n\n  // Constraints\n  {}\n}}",
      normalized_module.name, declarations, constraints
    ))
  }
}

impl<F: PrimeField> PicusProgram<F> {
  /// Convert picus program to a string-representation of a circom module
  pub fn to_circom(&self) -> Result<String, String> {
    let templates = self.modules.iter()
      .map(|module| module.to_circom())
      .collect::<Result<Vec<_>, _>>()?;
    Ok(templates.join("\n"))
  }
}

#[cfg(test)]
mod tests {

  use ciphersuite::{Ciphersuite, Secp256k1};
  use generalized_bulletproofs::arithmetic_circuit_proof::LinComb;

  use crate::{
    picus::{PicusModule, PicusProgram},
    Circuit,
  };

  // TODO: Use BN254 curve
  type C = Secp256k1;
  type F = <C as Ciphersuite>::F;

  #[test]
  fn test_circom_module_printing() -> Result<(), String> {
    let mut circuit: Circuit<C> = Circuit::<C> { constraints: vec![], muls: 0, prover: None };
    let (l, r, o) = circuit.mul(None, None, None);
    let lincomb = LinComb::empty().term(F::ONE, l).term(F::ONE, r).term(F::ONE.negate(), o);
    circuit.constrain_equal_to_zero(lincomb);

    let mut module: PicusModule<F> = PicusModule::new("main".to_string());
    module.apply_constraints(&circuit);
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&l, &circuit).unwrap());
    module.mark_variable_as_input(module.circuit_variable_to_picus_variable(&r, &circuit).unwrap());

    assert_eq!(
      module.to_circom()?,
      "template main {
  // Declarations
  signal input aL_0;
  signal input aR_0;
  signal output aO_0;

  // Constraints
  (1) * (aL_0) + (1) * (aR_0) + (115792089237316195423570985008687907852837564279074904382605163141518161494336) * (aO_0) === 0;
  (aL_0) * (aR_0) === aO_0;
}"
    );
    Ok(())
  }
}
