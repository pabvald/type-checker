package de.uni_saarland.cs.se

import Expression.{_if, _let}
import ExpressionConversions.{constantToExpr, intToConst, stringToId}
import VTypeFunctions.{Theta, join, equality}

import cafesat.api.Formulas.{Formula, PropVar}
import cafesat.api.{FormulaBuilder, Formulas}
import org.scalatest.flatspec.AnyFlatSpec

class BasicTypeTests extends AnyFlatSpec {
  "The Theta of a VType" should "contain a disjunction of its range" in {
    val A: Formula = FormulaBuilder.propVar("A")
    val B: Formula = FormulaBuilder.propVar("B")
    val t: VType = new VType(Map(BoolTy -> A, NumTy -> B))

    assert(Theta(t) == (A || B))
  }

  "The join of two VTypes" should "contain the joined VTypes" in {
    val A: Formula = FormulaBuilder.propVar("A")
    val B: Formula = FormulaBuilder.propVar("B")
    val C: Formula = FormulaBuilder.propVar("C")

    val tau1: VType = new VType(Map(BoolTy -> A, NumTy -> B))
    val tau2: VType = new VType(Map(BoolTy -> C))
    val tau3: VType = new VType(Map(NumTy -> B))
    val tau4: VType = new VType(Map(NumTy -> (Formulas.True && A)))

    assert(join(tau1, tau2) == new VType(Map(BoolTy -> (A || C), NumTy -> B)))
    assert(join(tau2, tau3) == new VType(Map(BoolTy -> C, NumTy -> B)))
    assert(join(tau3, tau4) == new VType(Map(NumTy -> (B || (Formulas.True && A)))))
    assert(join(new VType(Map()), new VType(Map())) == new VType(Map()))
  }

  "The equality formula" should "have the expected form" in {
    def bicond(A: Formula, B: Formula): Formula = {
      A.iff(B)
    }

    val A: Formula = FormulaBuilder.propVar("A")
    val B: Formula = FormulaBuilder.propVar("B")
    val C: Formula = FormulaBuilder.propVar("C")

    val Psi: Formula = A
    val tau1: VType = new VType(Map(NumTy -> B))
    val tau2: VType = new VType(Map(BoolTy -> C))

    val eqFormula: Formula = bicond(Formulas.False, (!A || bicond(B, C)))

    assert(equality(tau1, tau2, Psi) == eqFormula)

  }

  "The expression 'Const(True)'" should "have the type 'BoolTy'" in {
    val testExpr: Expression = Const(True)
    val t = TypeChecker.checkType(
        testExpr,
        VariabilityContext.emptyContext(),
        TypeContext.emptyContext()
      )
    assert(t == new VType(Map(BoolTy -> Formulas.True)))
  }

  "The expression 'Const(False)'" should "have the type 'BoolTy'" in {
    val testExpr: Expression = Const(False)
    val t = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    )
    assert(t == new VType(Map(BoolTy -> Formulas.True)))
  }

  "The expression 'Const(Num(42))'" should "have the type 'NumTy'" in {
    val testExpr: Expression = Const(Num(42))
    val t = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    )
    assert(t == new VType(Map(NumTy -> Formulas.True)))
  }

  "The variable in 'x'" must "be in the context" in {
    val testExpr: Expression = Id("x")
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    ))
    assert(error.expr == testExpr)
    assert(error.typeContext == TypeContext.emptyContext())
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The variable in 'x'" should "be in the context" in {
    val testExpr: Expression = Id("x")
    val pc: Formula = FormulaBuilder.propVar("A") || FormulaBuilder.propVar("B")
    var typeContext: TypeContext = TypeContext.emptyContext()

    typeContext = typeContext.withVar(Id("x"), new VType(Map(NumTy -> pc)))
    val f = Formulas.True 
    val t: VType = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      typeContext
    )
    assert(t == new VType(Map(NumTy -> (pc && Formulas.True))))
  }

  "The expression '5 < 4'" should "have the type 'BoolTy'" in {
    val testExpr: Expression = 4 _lt 5
    val varContext: VariabilityContext = VariabilityContext.emptyContext()
    val t: VType = TypeChecker.checkType(
      testExpr,
      varContext,
      TypeContext.emptyContext()
    )
    assert(t == new VType(Map(BoolTy -> varContext.featureModel)))
  }

  "The first argument to 'Smaller'" must "have the type 'NumTy'" in {
    val testExpr: Expression = 5 _lt False
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    ))
    print(s"\n $error\n")
    assert(error.expr == testExpr)
    assert(error.typeContext == TypeContext.emptyContext())
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The second argument to 'Smaller'" must "have the type 'NumTy'" in {
    val testExpr: Expression = False _lt 5
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    ))
    print(s"\n $error\n")
    assert(error.expr == testExpr)
    assert(error.typeContext == TypeContext.emptyContext())
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The condition in 'If'" must "have the type 'BoolTy'" in {
    val testExpr: Expression = _if(3) _then True _else False
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    ))
    print(s"\n $error\n")
    assert(error.expr == testExpr)
    assert(error.typeContext == TypeContext.emptyContext())
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The 'then' and 'else' expressions in 'If'" must "have the same type" in {
    val testExpr: Expression = _if(3 _lt 4) _then True _else 3
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    ))
    print(s"\n $error\n")
    assert(error.expr == testExpr)
    assert(error.typeContext == TypeContext.emptyContext())
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The type of 'If'" should "be the join of the 'then' and 'else' types" in {
    val testExpr: Expression = _if(3 _lt 4) _then True _else False
    val t: VType = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    )
    assert(t == new VType(Map(BoolTy -> (Formulas.True || Formulas.True))))
  }

  // "The 'then' and 'else' expression" must "have the same type under the variability context" in {
  //   val testExpr: Expression = _if(True) _then Id("x") _else False
  //   val A: Formula = FormulaBuilder.propVar("A") 
  //   val B: Formula = FormulaBuilder.propVar("B")
  //   var typeContext: TypeContext = TypeContext.emptyContext()
  //   var varContext: VariabilityContext = new VariabilityContext(B)

  //   typeContext = typeContext.withVar(Id("x"), new VType(Map(BoolTy -> A)))

  //   val error = intercept[TypeCheckingError](TypeChecker.checkType(
  //     testExpr,
  //     varContext,
  //     typeContext
  //   ))
  //   print(s"\n $error\n")
  //   assert(error.expr == testExpr)
  //   assert(error.typeContext == TypeContext.emptyContext())
  //   assert(error.variabilityContext == VariabilityContext.emptyContext())
  // }

  "The 'Id' in 'Let'" must "not be in the context already" in {
    val testExpr: Expression = _let("x") _is 5 _in ("x" _lt 4)
    val typeContext = TypeContext.emptyContext()
      .withVar("x", new VType(Map(NumTy -> Formulas.True)))
    val error = intercept[TypeCheckingError](TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      typeContext
    ))
    print(s"\n $error\n")
    assert(error.expr == testExpr)
    assert(error.typeContext == typeContext)
    assert(error.variabilityContext == VariabilityContext.emptyContext())
  }

  "The VType of the 'Let' expression" should "be adequate" in {
    val testExpr: Expression = _let("x") _is 5 _in ("x" _lt 4)
    val t: VType = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    )

    assert(t == new VType(Map(BoolTy -> Formulas.True)))
  }

  "The expression 'Choice(A || B, True, 5)'" should "have a VType with two entries" in {
    val A = FormulaBuilder.propVar("A")
    val B = FormulaBuilder.propVar("B")
    val testExpr: Expression = Choice(A || B, True, 5)
    val t = TypeChecker.checkType(
      testExpr,
      VariabilityContext.emptyContext(),
      TypeContext.emptyContext()
    )
    assert(t == new VType(Map(
      BoolTy -> (Formulas.True && (A || B)),
      NumTy -> (Formulas.True && !(A || B))
    )))
  }
}
