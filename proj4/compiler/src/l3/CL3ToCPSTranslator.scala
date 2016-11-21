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
      case S.Let((name, value) +: rest, body) =>
        nonTail(value)(v =>
          C.LetP(name, L3Id, Seq(v), nonTail(S.Let(rest, body))(ctx)))

      case S.Let(Seq(), body) =>
        nonTail(body)(ctx)

      case S.LetRec(functions, body) =>
        val funDefs = functions map { f =>
          val rc = Symbol.fresh("rc")
          C.FunDef(f.name, rc, f.args, tail(f.body, rc))
        }
        C.LetF(funDefs, nonTail(body)(ctx))

      case S.If(condE, thenE, elseE) =>
        val v = Symbol.fresh("v")
        tempLetC("ic", Seq(v), ctx(v))(ic =>
          tempLetC("tc", Seq(), tail(thenE, ic))(tc =>
            tempLetC("fc", Seq(), tail(elseE, ic))(fc =>
              cond(condE, tc, fc))))

      case S.App(fun, args) =>
        val r = Symbol.fresh("r")
        nonTail(fun)(f =>
          nonTail_*(args)(as =>
            tempLetC("rc", Seq(r), ctx(r))(rc => C.AppF(f, rc, as))))

      case t @ S.Prim(prim: L3TestPrimitive, _) =>
        nonTail(S.If(t, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(prim: L3ValuePrimitive, args) =>
        val v = Symbol.fresh("v")
        nonTail_*(args)(as => C.LetP(v, prim, as, ctx(v)))

      case S.Halt(arg) =>
        nonTail(arg)(C.Halt(_))

      case S.Ident(name) =>
        ctx(name)

      case S.Lit(value) =>
        val i = Symbol.fresh("i")
        C.LetL(i, value, ctx(i))
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

    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let((name, value) +: rest, body) =>
        nonTail(value)(v =>
          C.LetP(name, L3Id, Seq(v), tail(S.Let(rest, body), c)))

      case S.Let(Seq(), body) =>
        tail(body, c)

      case S.LetRec(functions, body) =>
        val funDefs = functions map { f =>
          val rc = Symbol.fresh("rc")
          C.FunDef(f.name, rc, f.args, tail(f.body, rc))
        }
        C.LetF(funDefs, tail(body, c))

      case S.If(condE, thenE, elseE) =>
        tempLetC("tc", Seq(), tail(thenE, c))(tc =>
          tempLetC("fc", Seq(), tail(elseE, c))(fc =>
            cond(condE, tc, fc)))

      case S.App(fun, args) =>
        nonTail(fun)(f => nonTail_*(args)(as => C.AppF(f, c, as)))

      case t @ S.Prim(prim: L3TestPrimitive, _) =>
        tail(S.If(t, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)

      case S.Prim(prim: L3ValuePrimitive, args) =>
        val v = Symbol.fresh("v")
        nonTail_*(args)(as => C.LetP(v, prim, as, C.AppC(c, Seq(v))))

      case S.Halt(arg) =>
        nonTail(arg)(C.Halt(_))

      case S.Ident(name) =>
        C.AppC(c, Seq(name))

      case S.Lit(value) =>
        val i = Symbol.fresh("i")
        C.LetL(i, value, C.AppC(c, Seq(i)))
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CL3Literal): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      case S.If(condE, thenE, S.Lit(l)) =>
        tempLetC("tc", Seq(), cond(thenE, trueC, falseC))(tc =>
          cond(condE, tc, litToCont(l)))

      case S.If(condE, S.Lit(l), elseE) =>
        tempLetC("ec", Seq(), cond(elseE, trueC, falseC))(ec =>
          cond(condE, litToCont(l), ec))

      case S.Prim(p: L3TestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(L3Ne, Seq(o, n), trueC, falseC)))
    }
  }

  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
