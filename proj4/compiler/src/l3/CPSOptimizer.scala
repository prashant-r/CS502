package l3

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
    /* How many times a symbol is encountered in the Tree. Note: The
     * census for the whole program gets calculated once in the
     * beginning, and passed to the initial state.
     */
    census: Map[Name, Count],
    // Name substitution that needs to be applied to the current tree
    subst: Substitution[Name] = Substitution.empty,
    // Names that have a constant value
    lEnv: Map[Name, Literal] = Map.empty,
    // The inverse of lEnv
    lInvEnv: Map[Literal, Name] = Map.empty,
    // A known block mapped to its tag and length
    bEnv: Map[Name, (Literal, Name)] = Map.empty,
    // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
    // Note: useful for common-subexpression elimination
    eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
    // Continuations that will be inlined
    cEnv: Map[Name, CntDef] = Map.empty,
    // Functions that will be inlined
    fEnv: Map[Name, FunDef] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true
    // Checks whether a symbols is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Addas a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))
    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))
    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))
    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))
    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))
    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))
    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))
    /*
     * The same state, with emply inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {
      

      // Dead code elimination
      case LetL(name, value, body) => { if(s.dead(name)) shrinkT(body)(State(census(body))) else LetL(name, value, shrinkT(body)(State(census(body)))) }
      case LetP(name, prim, args, body) => { if (s.dead(name) && !impure(prim)) shrinkT(body)(State(census(body))) else LetP(name, prim, args, shrinkT(body)(State(census(body)))) }
      case LetF(funcs, body) => {
        val filteredFuncs = funcs.filter(x => !s.dead(x.name))
        val shrunkFuncs   = filteredFuncs.map(f => FunDef(f.name, f.retC, f.args, shrinkT(f.body)(State(census(f.body)))))
        LetF(shrunkFuncs, shrinkT(body)(State(census(body))))
      }
      case LetC(conts, body) => {
        val filteredConts = conts.filter(x => !s.dead(x.name)) 
        val shrunkConts   = filteredConts.map(c => CntDef(c.name, c.args, shrinkT(c.body)(State(census(c.body)))))
        LetC(shrunkConts, shrinkT(body)(State(census(body)))) 
      }

      // Common subexpression elimination
      case LetL(name, value, body) if(s.lInvEnv.contains(value) && s.lInvEnv.get(value).get != name) =>{
           val preimage = name
           val image = s.lInvEnv.get(value).get
           LetL(name, value, body.subst(Substitution(preimage, image)))
      }
      
      case LetP(name, prim, args, body) if(s.eInvEnv.contains((prim, args)) && s.eInvEnv.get((prim, args)).get != name) =>{
           val preimage = name
           val image = s.eInvEnv.get((prim, args)).get
           LetP(name, prim, args, body.subst(Substitution(preimage, image)))
      }
      // case LetF(funcs, body) => ???
      // case LetC(conts, body) => ???

      // Constant folding
      case If(condition, arguments, thenC, elseC)
       if arguments.map((sym : Symbol) => s.lEnv.contains(sym)).foldRight(true)(_ && _) => {
          if(cEvaluator(condition, arguments.map(x => s.lEnv.get(x).get)))
             AppC(thenC, Nil)
          else
             AppC(elseC, Nil)
       }
       
      // Block primitives
      case LetP(name, prim , args, body) => 
        prim match
        {
          case L3BlockAlloc(tag: Int) => {
            tree
          }
          case _ => {
            tree
          }
          
        }
      case _ =>
        // TODO
        tree
    }

    shrinkT(tree)(State(census(tree)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    
    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = Stream.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        
         case LetL(name, value, body) => LetL(name, value, inlineT(body))
         
         case LetP(name, prim, args, body) => LetP(name, prim, args, inlineT(body))
         
         case LetF(funcs, body) if size(tree) < funLimit => {
            def canInline(f: FunDef): Boolean = {
              val copt = State(census(body))
              val funcBodyList = funcs.map(x => State(census(x.body)).dead(f.name))
              val andAllFuncs = funcBodyList.foldLeft(true)(_ && _)
              s.appliedOnce(f.name) && copt.dead(f.name) && andAllFuncs
            }
              val funcsInlineable = funcs.filter(func => (canInline(func)))
              LetF(funcs.filterNot(canInline(_)).map(f => 
              f.copy(body = inlineT(f.body)(s.withFuns(funcsInlineable)))),
              inlineT(body)(s.withFuns(funcsInlineable)))
         }
         case LetF(funcs, body) => {
            val shrunkFuncs   = funcs.map(f => FunDef(f.name, f.retC, f.args, inlineT(f.body)(State(census(f.body)))))
            LetF(shrunkFuncs, inlineT(body)(State(census(body))))
         }
         
         case LetC(continuations, body) if size(tree) < cntLimit => {
            def canInline(c: CntDef): Boolean = {
              val copt = State(census(body))
              val funcBodyList = continuations.map(x => State(census(x.body)).dead(c.name))
              val andAllConts = funcBodyList.foldLeft(true)(_ && _)
              s.appliedOnce(c.name) && copt.dead(c.name) && andAllConts
            }
              val contsInlineable = continuations.filter(cont => (canInline(cont)))
              LetC(continuations.filterNot(canInline(_)).map(c => 
              c.copy(body = inlineT(c.body)(s.withCnts(contsInlineable)))),
              inlineT(body)(s.withCnts(contsInlineable)))
         }
         case LetC(continuations, body) => {
            val shrunkConts = continuations.map(cont => CntDef(cont.name,cont.args, inlineT(cont.body)(State(census(cont.body)))))
            LetC(shrunkConts, inlineT(body)(State(census(body))))
         }
         
         case _ =>
          tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimivite on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: TestPrimitive => Boolean
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(L3BlockSet, L3ByteRead, L3ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case L3BlockAlloc(_) | L3BlockGet | L3ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case L3BlockAlloc(tag) => IntLit(tag)
  }
  protected val blockTag: ValuePrimitive = L3BlockTag
  protected val blockLength: ValuePrimitive = L3BlockLength

  protected val identity: ValuePrimitive = L3Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), L3IntAdd), (IntLit(1), L3IntMul), (IntLit(~0), L3IntBitwiseAnd), (IntLit(0), L3IntBitwiseOr), (IntLit(0), L3IntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((L3IntAdd, IntLit(0)), (L3IntSub, IntLit(0)), (L3IntMul, IntLit(1)), (L3IntDiv, IntLit(1)),
        (L3IntArithShiftLeft, IntLit(0)), (L3IntArithShiftRight, IntLit(0)),
        (L3IntBitwiseAnd, IntLit(~0)), (L3IntBitwiseOr, IntLit(0)), (L3IntBitwiseOr, IntLit(0)))
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), L3IntMul), (IntLit(0), L3IntBitwiseAnd), (IntLit(~0), L3IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((L3IntMul, IntLit(0)), (L3IntBitwiseAnd, IntLit(0)), (L3IntBitwiseOr, IntLit(~0)))
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] = 
    Map(L3IntSub -> IntLit(0), L3IntDiv -> IntLit(1), L3IntMod -> IntLit(0), L3IntBitwiseXOr -> IntLit(0))
  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case L3IntLe | L3IntGe | L3Eq => true
    case L3IntLt | L3IntGt | L3Ne => false
  }
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (L3IntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (L3IntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (L3IntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (L3IntDiv, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorDiv(x, y))
    case (L3IntMod, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorMod(x, y))

    case (L3IntArithShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (L3IntArithShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y)
    case (L3IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (L3IntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y)
    case (L3IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)

    case (L3CharToInt, Seq(CharLit(x))) => IntLit(x>>2)
    case (L3IntToChar, Seq(IntLit(x))) => CharLit((x<<2)+2)
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (L3IntP, Seq(IntLit(_))) => true
    case (L3IntP, Seq(_)) => false

    case (L3BoolP, Seq(BooleanLit(_))) => true
    case (L3BoolP, Seq(_)) => false

    case (L3CharP, Seq(CharLit(_))) => true
    case (L3CharP, Seq(_)) => false

    case (L3UnitP, Seq(UnitLit)) => true
    case (L3UnitP, Seq(_)) => false

    case (L3IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (L3IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (L3Eq, Seq(x, y)) => x == y
    case (L3Ne, Seq(x, y)) => x != y
    case (L3IntGe, Seq(IntLit(x), IntLit(y))) => x >= y
    case (L3IntGt, Seq(IntLit(x), IntLit(y))) => x > y
    case _ => false
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSArithShiftL, 0), (CPSArithShiftR, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
