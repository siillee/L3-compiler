package l3

import l3.{SymbolicCL3TreeModule => S}
import l3.{SymbolicCPSTreeModule => C}
import l3.{L3Primitive => L3}

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  class FreshGenerator(mode: String) {
    private val pre = s"${mode}_"
    private def g(k: String) = Symbol.fresh(pre + k)
    def freshRet = g("ret")
    def freshCnt = g("cnt")
    def freshV = g("v")
    def freshPrimOut = g("primOut")
    def freshR = g("r")
    def freshThen = g("thenC")
    def freshElse = g("elseC")
  }

  def apply(tree: S.Tree): C.Tree =
    nonTail(tree) { _ => C.AppC(Symbol.HALT, Seq(C.AtomL(IntLit(L3Int(0))))) }

  private def nonTail(tree: S.Tree)(ctx: C.Atom => C.Tree): C.Tree = {
    implicit val f = new FreshGenerator("NT")
    implicit def pos = tree.pos
    tree match {
      case S.Ident(name) => ctx(C.AtomN(name))

      case S.Lit(value) => ctx(C.AtomL(value))

      case S.Let(bindings, body) =>
        transformLet(bindings)(nonTail(body)(ctx))

      case S.LetRec(functions, body) =>
        transformLetRec(functions)(nonTail(body)(ctx))

      case S.App(fun, args) =>
        nonTail(fun) { fAtom =>
          transformArgs(args) { argAtoms =>
            val cnt = f.freshCnt
            val cntArg = f.freshV
            C.LetC(
              Seq(C.Cnt(cnt, Seq(cntArg), ctx(C.AtomN(cntArg)))),
              C.AppF(fAtom, cnt, argAtoms)
            )
          }
        }

      case S.Prim(prim, args) => {
        prim match {
          case primV: L3ValuePrimitive =>
            transformArgs(args) { argAtoms =>
              val primOut = f.freshPrimOut
              C.LetP(primOut, primV, argAtoms, ctx(C.AtomN(primOut)))
            }

          case _: L3TestPrimitive =>
            nonTail(S.If(tree, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)
        }
      }

      case S.If(condT, thenE, elseE) =>
        val cnt = f.freshCnt
        val cntArg = f.freshR
        val thenCnt = f.freshThen
        val elseCnt = f.freshElse

        C.LetC(
          Seq(
            C.Cnt(cnt, Seq(cntArg), ctx(C.AtomN(cntArg))),
            C.Cnt(thenCnt, Seq(), tail(thenE, cnt)),
            C.Cnt(elseCnt, Seq(), tail(elseE, cnt))
          ),
          cond(condT, thenCnt, elseCnt)
        )

      case S.Halt(expr) => nonTail(expr) { at => C.AppC(Symbol.HALT, Seq(at)) }
    }
  }

  def tail(tree: S.Tree, c: Symbol): C.Tree = {
    implicit val f = new FreshGenerator("T")
    implicit def pos = tree.pos
    tree match {
      case S.Ident(name) => C.AppC(c, Seq(C.AtomN(name)))

      case S.Lit(value) => C.AppC(c, Seq(C.AtomL(value)))

      case S.Let(bindings, body) =>
        transformLet(bindings)(tail(body, c))

      case S.LetRec(functions, body) =>
        transformLetRec(functions)(tail(body, c))

      case S.App(fun, args) => {
        nonTail(fun) { fAtom =>
          transformArgs(args) { argAtoms =>
            C.AppF(fAtom, c, argAtoms)
          }
        }
      }

      case S.Prim(prim, args) =>
        prim match {
          case primV: L3ValuePrimitive =>
            transformArgs(args) { argAtoms =>
              val primOut = f.freshPrimOut
              C.LetP(
                primOut,
                primV,
                argAtoms,
                C.AppC(c, Seq(C.AtomN(primOut)))
              )
            }
          case _: L3TestPrimitive =>
            tail(S.If(tree, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)
        }

      case S.If(condT, thenE, elseE) =>
        val thenCnt = f.freshThen
        val elseCnt = f.freshElse

        C.LetC(
          Seq(
            C.Cnt(thenCnt, Seq(), tail(thenE, c)),
            C.Cnt(elseCnt, Seq(), tail(elseE, c))
          ),
          cond(condT, thenCnt, elseCnt)
        )

      case S.Halt(expr) => nonTail(expr) { at => C.AppC(Symbol.HALT, Seq(at)) }
    }
  }

  def cond(tree: S.Tree, ct: Symbol, cf: Symbol): C.Tree = {
    implicit val f = new FreshGenerator("C")
    tree match {
      case S.Ident(name) =>
        C.If(L3.Eq, Seq(C.AtomN(name), C.AtomL(BooleanLit(false))), cf, ct)

      case S.Lit(literal) =>
        C.If(L3.Eq, Seq(C.AtomL(literal), C.AtomL(BooleanLit(false))), cf, ct)

      case S.Let(bindings, body) =>
        transformLet(bindings)(cond(body, ct, cf))

      case S.LetRec(functions, body) =>
        transformLetRec(functions)(cond(body, ct, cf))

      case S.App(fun, args) =>
        val cnt = f.freshCnt
        val cntArg = f.freshV
        nonTail(fun) { fAtom =>
          transformArgs(args) { argAtoms =>
            C.LetC(
              Seq(
                C.Cnt(
                  cnt,
                  Seq(cntArg),
                  C.If(L3.Eq, Seq(C.AtomN(cntArg), C.AtomL(BooleanLit(false))), cf, ct)
                )
              ),
              C.AppF(fAtom, cnt, argAtoms)
            )
          }
        }

      case S.Prim(prim, args) => {
        transformArgs(args) { argAtoms =>
          prim match {
            case primT: L3TestPrimitive =>
              C.If(primT, argAtoms, ct, cf)
            case primV: L3ValuePrimitive =>
              val primOut = f.freshPrimOut
              C.LetP(
                primOut,
                primV,
                argAtoms,
                C.If(L3.Eq, Seq(C.AtomN(primOut), C.AtomL(BooleanLit(false))), cf, ct)
              )
          }
        }
      }

      case S.If(condT, S.Lit(BooleanLit(thenV)), S.Lit(BooleanLit(elseV))) =>
        val nestedCt = if (thenV) ct else cf
        val nestedCf = if (elseV) ct else cf
        cond(condT, nestedCt, nestedCf)

      case S.If(condT, S.Lit(BooleanLit(thenV)), elseE) =>
        val elseCnt = f.freshElse
        val nestedCt = if (thenV) ct else cf
        C.LetC(
          Seq(C.Cnt(elseCnt, Seq(), cond(elseE, ct, cf))),
          cond(condT, nestedCt, elseCnt)
        )

      case S.If(condT, thenE, S.Lit(BooleanLit(elseV))) =>
        val thenCnt = f.freshThen
        val nestedCf = if (elseV) ct else cf
        C.LetC(
          Seq(C.Cnt(thenCnt, Seq(), cond(thenE, ct, cf))),
          cond(condT, thenCnt, nestedCf)
        )

      case S.If(condT, thenE, elseE) =>
        val thenCnt = f.freshThen
        val elseCnt = f.freshElse
        C.LetC(
          Seq(
            C.Cnt(thenCnt, Seq(), cond(thenE, ct, cf)),
            C.Cnt(elseCnt, Seq(), cond(elseE, ct, cf))
          ),
          cond(condT, thenCnt, elseCnt)
        )

      case S.Halt(expr) => nonTail(expr) { at => C.AppC(Symbol.HALT, Seq(at)) }
    }
  }

  private def transformArgs(argExprs: Seq[S.Tree])(body: Seq[C.Atom] => C.Tree) = {
    def inner(argRest: Seq[S.Tree], argAtoms: Seq[C.Atom]): C.Tree =
      argRest match {
        case Nil => body(argAtoms)
        case expr :: rest =>
          nonTail(expr) { at => inner(rest, argAtoms :+ at) }
      }
    inner(argExprs, Seq())
  }

  private def transformLet(bindings: Seq[(Symbol, S.Tree)])(body: C.Tree) =
    bindings.foldRight(body) { (curr, prev) =>
      val (name, expr) = curr
      nonTail(expr) { at => C.LetP(name, L3.Id, Seq(at), prev) }
    }

  private def transformLetRec(functions: Seq[S.Fun])(body: C.Tree)(implicit f: FreshGenerator) = {
    val funs = functions.map { case S.Fun(name, args, body) =>
      val cnt = f.freshRet
      C.Fun(name, cnt, args, tail(body, cnt))
    }
    C.LetF(funs, body)
  }
}