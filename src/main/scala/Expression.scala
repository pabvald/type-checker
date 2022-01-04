/**
  * This file implements our simple programming language as defined in the
  * lecture slides chapter 8 slide 71.
  */
package de.uni_saarland.cs.se

import cafesat.api.Formulas.Formula

import scala.language.implicitConversions

// Constants
abstract class Constant

case object True extends Constant

case object False extends Constant

case class Num(value: Int) extends Constant

// Expressions
abstract class Expression {
  def _lt(expression: Expression): Smaller = Smaller(this, expression)
}

case class Const(c: Constant) extends Expression

case class Id(name: String) extends Expression

case class Smaller(lhs: Expression, rhs: Expression) extends Expression

case class If(
  condition: Expression,
  thenExpr: Expression,
  elseExpr: Expression
) extends Expression

case class Let(
  varName: Id,
  varValue: Expression,
  inExpr: Expression
) extends Expression

case class Choice(
  presenceCondition: Formula,
  trueChoice: Expression,
  falseChoice: Expression
) extends Expression

// Types
abstract class Type

case object NumTy extends Type

case object BoolTy extends Type

// VType
class VType(val types: Map[Type, Formula]) {
  /**
    * Returns the domain of this VType.
    */
  def dom(): Set[Type] = types.keys.toSet

  /**
   * Returns the range of this VType.
   */
  def rng(): Set[Formula] = types.values.toSet

  /**
    * Retrieve the formula associated with a certain type.
    */
  def formulaForType(t: Type): Option[Formula] = types.get(t)

  override def toString: String = {
    types.toSeq.map({
      case (t: Type, pc: Formula) => s"($t => $pc)"
    }).mkString("\n")
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case other: VType => types == other.types
      case _ => false
    }
  }
}

/*
 * Everything below here is only there to allow writing expressions in a nicer
 * syntax but is irrelevant for implementing the type checker.
 */

object ExpressionConversions {
  implicit def constantToExpr(constant: Constant): Expression = Const(constant)
  implicit def intToConst(i: Int): Const = Const(Num(i))
  implicit def stringToId(s: String): Id = Id(s)
}

object Expression {
  def _if(cond: Expression): IfThen = IfThen(cond)
  def _let(varName: Id): LetIs = LetIs(varName)
}

case class IfThen(cond: Expression) {
  def _then(expr: Expression): IfElse = IfElse(cond, expr)
}

case class IfElse(cond: Expression, thenExpr: Expression) {
  def _else(expr: Expression): Expression = If(cond, thenExpr, expr)
}

case class LetIs(varName: Id) {
  def _is(expr: Expression): LetIn = LetIn(varName, expr)
}

case class LetIn(varName: Id, varExpr: Expression) {
  def _in(expr: Expression): Let = Let(varName, varExpr, expr)
}
