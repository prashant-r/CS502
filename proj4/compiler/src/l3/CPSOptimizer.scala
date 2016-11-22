package l3
import scala.collection.mutable.{ Map => MutableMap }
import java.io.PrintWriter
import java.io.PrintStream
import java.io.BufferedOutputStream
import scala.Console
abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    val ft = fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
    ft
  }


  
  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Union Find data structure */
  private case class IUnionFind(val size: Int) {
 
    private case class Node(var parent: Option[Int], var treeSize: Int)
    private val nodes = Array.fill[Node](size)(new Node(None, 1))

    def union(t1: Int, t2: Int): IUnionFind = {
      if (t1 == t2) return this
 
      val root1 = root(t1)
      val root2 = root(t2)
      if (root1 == root2) return this
 
      val node1 = nodes(root1)
      val node2 = nodes(root2)
 
      if (node1.treeSize < node2.treeSize) {
        node1.parent = Some(t2)
        node2.treeSize += node1.treeSize
      } else {
        node2.parent = Some(t1)
        node1.treeSize += node2.treeSize
      }
      this
    }
 
    def connected(t1: Int, t2: Int): Boolean = t1 == t2 || root(t1) == root(t2)
    private def root(t: Int): Int = nodes(t).parent match {
      case None => t
      case Some(p) => root(p)
    }
  }


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

    def isAbsorbing(a: Name, prim:ValuePrimitive)(implicit s: State): Boolean =
    (leftAbsorbing.contains((s.lEnv.get(a).get, prim)) || rightAbsorbing.contains((prim, s.lEnv.get(a).get))
             || leftNeutral.contains((s.lEnv.get(a).get, prim)) || rightNeutral.contains((prim, s.lEnv.get(a).get)))

    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {

      // Extra credit
      // Optimize Block primitives extra credit
     case LetP(name, prim, args @ Seq(block, ival), body)
        if unstable(prim) && (s.eInvEnv.map(x => (x._2, x._1)).get(block) match {
          case Some(x) => fixedBlockAlloc(x._1)
          case _ => false
        }) => {

          val toMatch = s.eInvEnv.filter(x => x._1._1 == blockSet && x._1._2(0) == block && x._1._2(1) == ival).toSeq
          if(toMatch.isEmpty){
            return LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)));
          }
          else{ 
              val replace = toMatch(0)._1._2(2)
            return shrinkT(body.subst(Substitution(name, replace)))(s.withSubst(name, replace))
          }
      }
      
      case LetL(name, value, body) if s.dead(name) => {
        shrinkT(body)
      }
      case LetP(name, prim, args, body) if s.eInvEnv.contains((prim, args)) && name != s.eInvEnv.get((prim, args)).get =>
        {
          val preimage2 = name
          val image2  = s.eInvEnv.get((prim,args)).get
          shrinkT(body.subst(Substitution(preimage2, image2))) (s.withSubst(preimage2, image2))
        }

      
     
      case LetL(name, value, body) if s.lInvEnv.contains(value) && name != s.lInvEnv.get(value).get =>
        {
          val preimage = name
          val postimage = s.lInvEnv.get(value).get
          LetL(name, value, body.subst(Substitution(preimage, postimage)))
       }
          
      case LetL(name, value, body) =>{
        LetL(name, value, shrinkT(body)(s.withLit(name, value)))
      }
      
      case LetP(name, prim, args, body) if s.dead(name) && !impure(prim) => {
          shrinkT(body)
      }
      
     // If
     case If(condition, arguments, thenC, elseC)
       if arguments.map((sym : Symbol) => s.lEnv.contains(sym)).foldRight(true)(_ && _) => {
          if(cEvaluator(condition, arguments.map(x => s.lEnv.get(x).get)))
             AppC(thenC, Nil)
          else
             AppC(elseC, Nil)
     }
       
      // Same args reduce
     case LetP(name, prim, args, body) if args.size == 2 && sameArgReduce.isDefinedAt(prim) && args(0) == args(1)  => {
       val value = sameArgReduce(prim)
       LetL(name, value, shrinkT(body)(s.withLit(name, value)))
     }
     // Left/Right absorbing/neutral
     case LetP(name, prim, args, body) if args.exists(a => s.lEnv.contains(a) && isAbsorbing(a, prim)) => {
       
       val value = args.filter(a => s.lEnv.contains(a) &&isAbsorbing(a, prim))
       args match {
         case Seq(x, y) => {if (x == value.head) 
         {return shrinkT(body.subst(Substitution(name, y)))}
         else {return shrinkT(body.subst(Substitution(name, x)))}}
       }
     }
     
     case LetP(name, prim, args, body) if (args.forall(a => s.lEnv.contains(a)) 
          && vEvaluator.isDefinedAt((prim, args.map(a => s.lEnv.get(a).get)))) => {
      val value = vEvaluator((prim, args.map(a => s.lEnv.get(a).get)))
      LetL(name, value, shrinkT(body)(s.withLit(name, value)))
     }
     
     

     case LetP(name, prim, args, body) => prim match {
       case x if prim == identity => {
            shrinkT(body.subst(Substitution(name, args(0))))(s.withSubst(name, args(0)))
       }
       case x if blockLength(x) => 
         s.eInvEnv.map(x => (x._2, x._1)).get(args(0)) match {
           case Some(y) =>
             shrinkT(body.subst(Substitution(name, y._2(0))))
           case None => LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
       }
       case x if blockTag(x) => 
         s.eInvEnv.map(x => (x._2, x._1)).get(args(0)) match {
           case Some(x) =>
             val fresh = Symbol.fresh("tag")
             LetL(fresh,blockAllocTag(x._1), shrinkT(body.subst(Substitution(name, fresh)))(s.withLit(fresh, blockAllocTag(x._1))))
           case None => LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
       }
       
       case _ => LetP(name, prim, args, shrinkT(body))
     }
      
      // Functions
      case LetF(functions, body) => {
        var unionFind = IUnionFind(functions.length + 2);
        var myStatusMap = Map[Object, Int]()
        var v = 1
        val totSeq = functions :+ body
        for(e <- totSeq)
        {
          myStatusMap += (e -> v)
          v = v+1
        }
        for (e <- functions)
          for (f <- totSeq)
            if(e != f)
            {
              if(f.isInstanceOf[FunDef]){
                var state = State(census(f.asInstanceOf[FunDef].body))
                if(!state.dead(e.asInstanceOf[FunDef].name))
                  unionFind.union( myStatusMap.get(e).get, myStatusMap.get(f).get)
              }
              else{
                var state = State(census(f.asInstanceOf[Tree]))
                if(!state.dead(e.asInstanceOf[FunDef].name))
                  unionFind.union( myStatusMap.get(e).get, myStatusMap.get(f).get)
              }
            }
        // DCE
        val fcts = functions.filter(f => unionFind.connected(myStatusMap.get(f).get,functions.length + 1))
      
        fcts match{
          case Nil => shrinkT(body)
          case _ => LetF(fcts.map(f => 
              f.copy(body = shrinkT(f.body)(s.withEmptyInvEnvs))), 
            shrinkT(body))
        }
      }
      
      // Continuations
      case LetC(continuations, body) => {

        // Union-Find 
        var unionFind = IUnionFind(continuations.length + 2);
        var myStatusMap = Map[Object, Int]()
        var v = 1
        val totSeq = continuations :+ body
        for(e <- totSeq)
        {
          myStatusMap += (e -> v)
          v = v+1
        }

        for (e <- continuations)
          for (f <- totSeq)
            if(e != f)
            {
              if(f.isInstanceOf[CntDef]){
                var state = State(census(f.asInstanceOf[CntDef].body))
                if(!state.dead(e.asInstanceOf[CntDef].name))
                  unionFind.union( myStatusMap.get(e).get, myStatusMap.get(f).get)
              }
              else{
                var state = State(census(f.asInstanceOf[Tree]))
                if(!state.dead(e.asInstanceOf[CntDef].name))
                  unionFind.union( myStatusMap.get(e).get, myStatusMap.get(f).get)
              }
            }
        // DCE
        val cnts = continuations.filter(f => unionFind.connected(myStatusMap.get(f).get,continuations.length + 1))
        cnts match{
          case Nil => shrinkT(body)
          case _ => LetC(cnts.map(x => 
            CntDef(x.name, x.args, shrinkT(x.body))), 
            shrinkT(body))
        
        }
      }

      case x =>{
        x
        }
      }
    val t = shrinkT(tree)(State(census(tree)))
    t
    
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    
    val fibonacci = Seq(1, 2, 3, 5, 8, 13)
    val trees = Stream.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i
  
      def freshNames(t: Tree, subst: Map[Name, Name]) : Map[Name, Name] = t match {
        case LetL(name, value, body) => freshNames(body, subst + (Symbol.fresh("inlL") -> name))
        case LetP(name, prim, args, body) => freshNames(body, subst + (Symbol.fresh("inlP") -> name))
        case LetC(continuations, body) => {
          def getFreshNamesCntDef(c: CntDef): Map[Name, Name] = freshNames(c.body, (
            (Symbol.fresh("inlC"), c.name) +:
            c.args.map(a => (Symbol.fresh("cntDefFreshName"), a))
          ).foldLeft(Map[Name,Name]())(_ + _))
          val freshNameMap = continuations.foldLeft(Map[Name,Name]())(
              (r, k) => r ++ getFreshNamesCntDef(k))
          freshNames(body, freshNameMap)
        }
        case LetF(functions, body) => {
          def getFreshNameFunDef(f: FunDef): Map[Name, Name] = freshNames(f.body, (
            (Symbol.fresh("funDefFreshName"), f.name) +:
            (Symbol.fresh("cntDefFreshName"), f.retC) +:
            f.args.map(a => (Symbol.fresh("funDefFreshName"), a))
        ).foldLeft(Map[Name,Name]())(_ + _))
          val freshNameMap = functions.foldLeft(Map[Name,Name]())(
              (r, k) => r ++ getFreshNameFunDef(k))
              
          freshNames(body, freshNameMap)
        }
        case _ => Map[Name,Name]()
      }

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        case LetL(name, value, body) =>
          LetL(name, value, inlineT(body))

        case LetP(name, prim, args, body) =>
          LetP(name, prim, args, inlineT(body))
        
        case LetC(continuations, body) if size(tree) <= cntLimit => {
          def canInline(c: CntDef): Boolean = 
            s.appliedOnce(c.name) && continuations.forall(c2 => {
              State(census(c2.body)).dead(c.name) 
            })
          
          val continuationsToInlineHere = continuations.filter(canInline(_))
          
          val state = s.withCnts(continuationsToInlineHere)

          LetC(continuations.filterNot(canInline(_)).map(c => 
            c.copy(body = inlineT(c.body)(state))), 
            inlineT(body)(state))
        }
        
        case LetC(continuations, body) =>
          LetC(continuations.map(c => c.copy(body = inlineT(c.body))), inlineT(body))
        
        case LetF(functions, body) if size(tree) < funLimit => {
          def canInline(f: FunDef): Boolean = 
            s.appliedOnce(f.name) && functions.forall(f2 => {
              State(census(f2.body)).dead(f.name) 
            })
          val functionsAbleToInline = functions.filter(canInline(_))
          LetF(functions.filterNot(canInline(_)).map(f => 
            f.copy(body = inlineT(f.body)(s.withFuns(functionsAbleToInline)))),
            inlineT(body)(s.withFuns(functionsAbleToInline)))
        }


        case AppC(name, args) if s.cEnv.contains(name) => {
           val theCntDef = s.cEnv.get(name).get
           val freshNamesMap = freshNames(theCntDef.body, Map[Name, Name]())
           val func1 : PartialFunction[Name, Name] = PartialFunction[Name, Name] {
             case x => freshNamesMap.get(x) match {
             case Some(n) => n
             case None => x
             }
           }
           val func2 : PartialFunction[Name, Name] = PartialFunction[Name, Name] {
             case x if theCntDef.args.contains(x) => args(theCntDef.args.indexOf(x))
             case x => x
           }
           val (keys, valuess) = freshNamesMap.unzip
           val freshBody = theCntDef.body.subst(Substitution(keys.toSeq, keys map { key => func1(key) } toSeq))
           inlineT(freshBody.subst(Substitution(theCntDef.args.toSeq, theCntDef.args map { key => func2(key) } toSeq)))
       }
        
        
        case LetF(functions, body) =>
          LetF(functions.map(f => f.copy(body = inlineT(f.body))), inlineT(body))
          
        
        case AppF(name, retC, args) if s.fEnv.contains(name) => {
          val funDef = s.fEnv.get(name).get
          val freshNamesMap = freshNames(funDef.body, Map[Name, Name]())
          val func1 : PartialFunction[Name, Name] = PartialFunction[Name, Name] {
            case x => freshNamesMap.get(x) match {
              case Some(n) => n
              case None => x
            }
          }
          val func2: PartialFunction[Name, Name] = PartialFunction[Name, Name] {
             case x if x == funDef.retC => retC
             case x if funDef.args.contains(x) => args(funDef.args.indexOf(x))
             case x => x
           }
          val (keys, valuess) = freshNamesMap.unzip
          val newBody = funDef.body.subst(Substitution(keys.toSeq, keys map { key => func1(key) } toSeq)) 
          val retcA: Seq[Name] = funDef.retC +: funDef.args.toSeq    
          return inlineT(newBody.subst(Substitution(retcA, retcA map ( key => func2(key) ) toSeq)))
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
  protected val blockSet: ValuePrimitive 
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive => Boolean
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive => Boolean
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive 

  protected val fixedBlockAlloc: ValuePrimitive => Boolean


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
  
  protected val fixedBlockAlloc: ValuePrimitive => Boolean = {
    case L3BlockAlloc(tag) if tag == 202 => true
  case _ => false
  }
  
  protected val blockSet: ValuePrimitive = L3BlockSet
  protected val blockTag: ValuePrimitive => Boolean ={
  case L3BlockTag => true
  case _ =>false
  }
  protected val blockLength: ValuePrimitive => Boolean ={
  case L3BlockLength => true
  case _ =>false
  } 

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

    // case (L3CharToInt, Seq(CharLit(x))) => IntLit(x>>2)
    // case (L3IntToChar, Seq(IntLit(x))) => CharLit((x<<2)+1)
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (L3IntP, Seq(IntLit(_))) => true
    case (L3IntP, Seq(_)) => false

    case (L3CharP, Seq(CharLit(_))) => true
    case (L3CharP, Seq(_)) => false

    case (L3BoolP, Seq(BooleanLit(_))) => true
    case (L3BoolP, Seq(_)) => false

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
  
  protected val fixedBlockAlloc: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(tag) if tag == 202 => true
    case _ => false
  }
  
  protected val blockSet: ValuePrimitive = CPSBlockSet
  protected val blockTag: ValuePrimitive => Boolean ={
    case CPSBlockTag => true
    case _ =>false
  }
  protected val blockLength: ValuePrimitive => Boolean ={
    case CPSBlockLength => true
    case _ =>false
  } 

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

  //discussed solution strategy with karan 
}
