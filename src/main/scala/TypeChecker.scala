package de.uni_saarland.cs.se

import cafesat.api.Formulas.Formula
import cafesat.api.{Formulas, Solver}
import scala.annotation.varargs


/**
  * Type context as in lecture slides 8/73.
  */
class TypeContext private(val mapping: Map[Id, VType]) {
  def this() = {
    this(Map())
  }

  /**
    * Create a extended copy of this type context that sets the type for the
    * given variable.
    */
  def withVar(id: Id, value: VType): TypeContext = {
    new TypeContext(mapping updated(id, value))
  }

  /**
    * Get the type for a given variable.
    */
  def typeForVar(id: Id): Option[VType] = mapping.get(id)

  override def equals(obj: Any): Boolean = {
    obj match {
      case other: TypeContext => mapping == other.mapping
      case _ => false
    }
  }

  // override def toString: String = {
  //   mapping.toSeq.map({
  //     case (id: Id, t: VType) => s"(${id.name}, type)"
  //   }).mkString(" ")
  // }
}

object TypeContext {
  /**
    * Creates an empty type context.
    */
  def emptyContext(): TypeContext = new TypeContext(Map())
}

/**
  * Variability context as in lecture slides 8/73.
  */
class VariabilityContext(val featureModel: Formula) {
  override def equals(obj: Any): Boolean = {
    obj match {
      case other: VariabilityContext => featureModel == other.featureModel
      case _ => false
    }
  }
}

object VariabilityContext {
  /**
    * Creates an empty variability context.
    */
  def emptyContext(): VariabilityContext = new VariabilityContext(Formulas.True)
}

/**
  * This exception must be thrown if a type error is detected.
  *
  * @param expr the (sub) expression that is currently checked
  * @param variabilityContext the current variability context
  * @param typeContext the current type context
  * @param message a message describing the type error
  */
class TypeCheckingError(
  val expr: Expression,
  val variabilityContext: VariabilityContext,
  var typeContext: TypeContext,
  message: String
) extends Exception(message)


object TypeChecker {

  import VTypeFunctions.{Theta, join, equality}

  /**
    * Determine the type of an expression given some type and variability
    * context.
    *
    * This function handles the dispatch for the different expression types.
    * You only have to implement the individual type rules as indicated by
    * the TODOs below.
    */
  def checkType(
                 expr: Expression,
                 variabilityContext: VariabilityContext,
                 typeContext: TypeContext
               ): VType = {
    expr match {
      case expr: Const => expr.c match {
        case True => checkTTrue(variabilityContext, typeContext);
        case False => checkTFalse(variabilityContext, typeContext);
        case const: Num => checkTNum(const, variabilityContext, typeContext);
      };
      case expr: Id => checkTId(expr, variabilityContext, typeContext);
      case expr: Smaller => checkTSmaller(expr, variabilityContext, typeContext);
      case expr: If => checkTIf(expr, variabilityContext, typeContext);
      case expr: Let => checkTLet(expr, variabilityContext, typeContext);
      case expr: Choice => checkTChoice(expr, variabilityContext, typeContext);
    }
  }

  def checkTTrue(
                  variabilityContext: VariabilityContext,
                  typeContext: TypeContext
                ): VType = {
    val Psi: Formula = variabilityContext.featureModel
    new VType(Map(BoolTy -> Psi))
  }

  def checkTFalse(
                   variabilityContext: VariabilityContext,
                   typeContext: TypeContext
                 ): VType = {
    val Psi: Formula = variabilityContext.featureModel
    new VType(Map(BoolTy -> Psi))
  }

  def checkTNum(
                 const: Num,
                 variabilityContext: VariabilityContext,
                 typeContext: TypeContext
               ): VType = {
    val Psi: Formula = variabilityContext.featureModel
    new VType(Map(NumTy -> Psi))
  }

  def checkTId(
                expr: Id,
                variabilityContext: VariabilityContext,
                typeContext: TypeContext
              ): VType = {       
    var tau: VType = new VType(Map())         
    val Psi: Formula = variabilityContext.featureModel
    
    // check whether the Id is contained in the Type Context
    typeContext.typeForVar(expr) match  {
      case Some(t) => tau = t 
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                                  s"id '${expr.name}' not present in type context")
    }

    // 'Psi ==> Theta(tau)' must be satisfiable
    Solver.solveForSatisfiability(!Psi || Theta(tau)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                            "'Psi ==> Theta(tau)' Not satisfiable")      
    } 

    // generate the resulting VType
    new VType(tau.types.map({
      case (t: Type, fi: Formula) => (t -> (fi && Psi))
    }))

  }

  def checkTSmaller(
                     expr: Smaller,
                     variabilityContext: VariabilityContext,
                     typeContext: TypeContext
                   ): VType = {    
    var fi1: Formula = Formulas.False
    var fi2: Formula = Formulas.False
    val Psi: Formula = variabilityContext.featureModel
    val tau1: VType = checkType(expr.lhs, variabilityContext, typeContext)
    val tau2: VType = checkType(expr.rhs, variabilityContext, typeContext)
    
    // first argument must have type ('NumTy', fi1)
    tau1.formulaForType(NumTy) match {
      case Some(t) => fi1 = t 
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext,
                                              "e1 doesn't have type 'NumTy'")
    }

    // 'Psi ==> fi1' must be satisfiable
    Solver.solveForSatisfiability(!Psi || fi1) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                            "'Psi ==> fi1' Not satisfiable")      
    }

    // second argument must have type ('NumTy', fi2)
    tau2.formulaForType(NumTy) match {
      case Some(t) => fi2 = t 
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext,
                                              "e2 doesn't have type 'NumTy'")
    }

    // 'Psi ==> fi2' must be satisfiable
    Solver.solveForSatisfiability(!Psi || fi2) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                            "'Psi ==> fi2' Not satisfiable")      
    }
    
    new VType(Map(BoolTy -> Psi))
  }

  def checkTIf(
                expr: If,
                variabilityContext: VariabilityContext,
                typeContext: TypeContext
              ): VType = {
    var fi1: Formula = Formulas.False
    val Psi: Formula = variabilityContext.featureModel

    val tau1: VType = checkType(expr.condition, variabilityContext, typeContext)
    val tau2: VType = checkType(expr.thenExpr, variabilityContext, typeContext)
    val tau3: VType = checkType(expr.elseExpr, variabilityContext, typeContext)
    
    // condition expression must have type ('BoolTy', fi1)
    tau1.formulaForType(BoolTy) match {
      case Some(t) => fi1 = t
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext,
                                              "e1 doesn't have type 'BoolTy'")
    }

    // 'Psi ==> fi1' must be satisfiable
    Solver.solveForSatisfiability(!Psi || fi1) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                              "'Psi ==> fi1' Not satisfiable")      
    }

    // 'Psi ==> Theta(tau2)'' must be satisfiable
    Solver.solveForSatisfiability(!Psi || Theta(tau2)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                              "'Psi ==> Theta(tau2)' Not satisfiable")      
    } 

    
    // 'Psi ==> Theta(tau3)'' must be satisfiable
    Solver.solveForSatisfiability(!Psi || Theta(tau3)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                            "'Psi ==> Theta(tau3)' Not satisfiable")      
    } 

    // tau2 ~ tau3 must be satisfiable 
    Solver.solveForSatisfiability(equality(tau2, tau3, Psi)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                               "'tau2 ~ tau3' Not satisfiable")      
    } 

    join(tau2, tau3)
  }

  def checkTLet(
                 expr: Let,
                 variabilityContext: VariabilityContext,
                 typeContext: TypeContext
               ): VType = {
    val Psi: Formula = variabilityContext.featureModel
    val tau1: VType = checkType(expr.varValue, variabilityContext, typeContext)

    // x mustn't be in typeContext.dom
    typeContext.typeForVar(expr.varName) match {
      case None => {}
      case Some(_) => throw new TypeCheckingError(expr, variabilityContext, typeContext,
                                  s"id '${expr.varName.name}' is already in the type context")
    }

    // 'Psi ==> Theta(tau1)' must be satisfiable
    Solver.solveForSatisfiability(!Psi || Theta(tau1)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                              "'Psi ==> tau1' Not satisfiable")      
    }
    
    val extTypeContext: TypeContext = typeContext.withVar(expr.varName, tau1) // extend type context
    val tau2: VType = checkType(expr.inExpr, variabilityContext, extTypeContext)
    
    // 'Psi ==> Theta(tau2)' must be satisfiable
    Solver.solveForSatisfiability(!Psi || Theta(tau2)) match {
      case Some(_) => {}
      case None => throw new TypeCheckingError(expr, variabilityContext, typeContext, 
                                              "'Psi ==> tau2' Not satisfiable")      
    }

    tau2
  }

  def checkTChoice(
                    expr: Choice,
                    variabilityContext: VariabilityContext,
                    typeContext: TypeContext
                  ): VType = {
    val Psi: Formula = variabilityContext.featureModel
    val fi: Formula = expr.presenceCondition

    val tau1: VType = checkType(
      expr.trueChoice,
      new VariabilityContext(Psi && fi),
      typeContext
    )

    val tau2: VType = checkType(
      expr.falseChoice,
      new VariabilityContext(Psi && !fi),
      typeContext
    )

    join(tau1, tau2)
  }
}

/**
 * Auxiliar functions applied to VType
 */
object VTypeFunctions {

  /**
   * Generates the disjunction of all the VType's range's formulas
   * @param tau a variational type
   */
  def Theta(tau: VType): Formula = { 
    var init: Boolean = false 
    var disjunction: Formula = Formulas.False
    for (fi: Formula <- tau.rng()) {
      if (!init) {
        init = true
        disjunction = fi 
      } else {
        disjunction = disjunction || fi
      }
    }
    disjunction
  }

  /**
   * Joins two VTypes into a single one 
   * @param tau1 first variational type 
   * @param tau2 second variational type
   */
  def join(tau1: VType, tau2: VType): VType = {
    var vtypes: Map[Type, Formula] = Map()
    val domUnion: Set[Type] = tau1.dom ++ tau2.dom

    for (t: Type <- domUnion) {
      var pc1: Option[Formula] = tau1.formulaForType(t)
      var pc2: Option[Formula] = tau2.formulaForType(t)

      if (!pc1.isEmpty && !pc2.isEmpty) {
        vtypes = vtypes + (t -> (pc1.get || pc2.get))
      } else if (!pc1.isEmpty) {
        vtypes = vtypes + (t -> pc1.get)
      } else if (!pc2.isEmpty) {
        vtypes = vtypes + (t -> pc2.get)
      }
    }

    new VType(vtypes)
  }

  /**
   * @param tau1 first variational type 
   * @param tau2 second variational type 
   * @param Psi variational context
   * @return tau1 ~ tau2
   */
  def equality(tau1: VType, tau2: VType, Psi: Formula): Formula = {

    /**
     * @param left the left formula of the biconditional
     * @param right the right formula of the biconditional
     * @return logical biconditional formula
     */
    def bicond(A: Formula, B: Formula): Formula = {
      A.iff(B)
    }
    
    /** 
     * @param t1 first type
     * @param t2 second type
     * @return the two types are equals as formula
     */
    def eqTypes(t1: Type, t2: Type): Formula = {
      (t1 == t2) match {
        case true => Formulas.True 
        case false => Formulas.False
      }       
    }

    var init: Boolean = false
    var eqFormula: Formula = Formulas.True

    for (t1: Type <- tau1.dom ) {
      var pc1: Formula = tau1.formulaForType(t1).get 
      for (t2: Type <- tau2.dom ) {
        var pc2: Formula = tau2.formulaForType(t2).get 
        if (!init) {
          init = true
          eqFormula = bicond(eqTypes(t1, t2), (!Psi || bicond(pc1, pc2)))
        } else {
          eqFormula = eqFormula && bicond(eqTypes(t1, t2), (!Psi || bicond(pc1, pc2)))
        }
      }
    }

    eqFormula
  }
}
