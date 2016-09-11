package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    nonTail(tree) { _ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree): C.Tree = {
    implicit val pos = tree.pos

    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      
      case S.Let(Seq(), body) =>
        nonTail(body)(ctx)
      
      case S.Let((name, value) +: rest, body) =>
        nonTail(value)(v =>
          C.LetP(name, L3Id, Seq(v), nonTail(S.Let(rest, body))(ctx)))
      
      case S.LetRec(funcs, body) => {
            C.LetF(funcs.map(f => {
              val c = Symbol.fresh("continuation")
              C.FunDef(f.name, c, f.args, tail(f.body, c))
            }), nonTail(body)(ctx))
      }
      
       case S.App(funcs, args) => {
        nonTail(funcs)(eHole => {nonTail_*(args)(lambdaHole2 => {
            val retVal = Symbol.fresh("returnVal")
            (tempLetC("contextContinue", Seq(retVal), ctx(retVal))(returnContinuation => C.AppF(eHole, returnContinuation, lambdaHole2)))
          })
        })
      }
      
      case S.Prim(testPrimitive: L3TestPrimitive, args:Seq[S.Tree]) =>
        nonTail(S.If((S.Prim(testPrimitive, args)), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)
        
      
      case S.If(condE: S.Tree, thenE: S.Tree, elseE: S.Tree) =>{
        val r = Symbol.fresh("r")
        tempLetC("cOuter", Seq(r), ctx(r))(cOuter => {
            tempLetC("cTrueBranch", Seq(), tail(thenE, cOuter))(cTrueBranch=>{
                tempLetC("cFalseBranch", Seq(), tail(elseE, cOuter))(cFalseBranch =>{
                    cond(condE, cTrueBranch, cFalseBranch);
                })
              })
            })         
      }
      
     
      case S.Prim(valuePrimitive: L3ValuePrimitive, args:Seq[S.Tree]) =>{
         val n = Symbol.fresh("vP")
         nonTail_*(args)(tempVar=>C.LetP(n,valuePrimitive,tempVar,ctx(n)))
      }
      
      case S.Halt(arg:S.Tree) => {
        nonTail(arg)( haltResult 
            =>C.Halt(haltResult))
      }
      case S.Ident(envVarName) => ctx(envVarName)
      
      case S.Lit(value: CL3Literal) =>{
        val name = Symbol.fresh("Lit")
        C.LetL(name, value, ctx(name))
      }
    }
  }

  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree): C.Tree =
    trees match {
      case Seq() =>
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol): C.Tree = {
    implicit val pos = tree.pos
    (tree: @unchecked) match {
      
      case S.Halt(argument) => {
        tail(argument,c)
      }
     
      case S.Ident(name) => C.AppC(c,Seq(name))
      
      case S.Let((name, value) +: rest, body) =>
        nonTail(value)(v =>
          C.LetP(name, L3Id, Seq(v), tail(S.Let(rest, body), c)))
      
      case S.App(fun: S.Tree, args: Seq[S.Tree]) =>{
        nonTail(fun)(
            funcName => {nonTail_*(args)(
                holesName => {
                    C.AppF(funcName, c, holesName)
          })
        })
       }
      case S.If(condE: S.Tree, thenE: S.Tree, elseE: S.Tree) => {
        tempLetC("cTrue", Seq(), tail(thenE, c))(cTrueBranch=>{
            tempLetC("cFalse", Seq(), tail(elseE, c))(cFalseBranch =>{
                cond(condE, cTrueBranch, cFalseBranch);
           })
         })
      }  
      case S.Prim(testPrimitive: L3TestPrimitive, args:Seq[S.Tree]) => {     
        tail(S.If((S.Prim(testPrimitive, args)), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))),c)
      }
      
      case S.Let(Seq(), body) =>
        tail(body, c)

      case S.LetRec(funcs, body) => {
        C.LetF(funcs.map(f => {
          
        val funcCont = Symbol.fresh("FreshFunctionCont")
        C.FunDef(f.name, funcCont, f.args, tail(f.body, funcCont))
        }), tail(body,c))
      } 
       
      case S.Prim(valuePrimitive: L3ValuePrimitive, args:Seq[S.Tree]) => {
        val valP = Symbol.fresh("valuePrimitive")
        nonTail_*(args)(arguments => {
          C.LetP(valP, valuePrimitive, arguments, C.AppC(c, Seq(valP)))})
      }
      
      case S.Lit(litVal) =>{
        val lit = Symbol.fresh("Lit")
        C.LetL(lit, litVal, C.AppC(c, Seq(lit)))
      }
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CL3Literal): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
      {
        cond(condE, litToCont(tl), litToCont(fl))
      }
      case S.If(cond1, cond2, S.Lit(f1)) =>
      {
         tempLetC("ac", Seq(), cond(cond2,trueC,falseC))(aC =>cond(cond1,aC,litToCont(f1)))
      }
      case S.If(cond1,S.Lit(t1), cond2) =>
      {
         tempLetC("ac", Seq(), cond(cond2,trueC,falseC))(aC =>cond(cond1,litToCont(t1), aC))
      }
      
      case S.Prim(p: L3TestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>{
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(L3Ne, Seq(o, n), trueC, falseC)))
      }
    }
  }

  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}