package l3

import l3.{ SymbolicCPSTreeModule => H }
import l3.{ SymbolicCPSTreeModuleLow => L }

import l3.{ L3Primitive => L3 }
import l3.{ CPSValuePrimitive => CPS }
import l3.{ CPSTestPrimitive => CPST }

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  // A type for the environment, mapping function name to its new name (w) and its free variables.
  type Environment = Map[H.Name, (L.Name, Seq[L.Name])]

  private def freshT = Symbol.fresh("t")
  private def freshW = Symbol.fresh("w")
  private def freshF = Symbol.fresh("f")
  private def freshV = Symbol.fresh("v")
  private def freshEnv = Symbol.fresh("env")

  def apply(tree: H.Tree): L.Tree = translate(tree, Map.empty)

  def translate(tree: H.Tree, env: Environment): L.Tree = {

    tree match {
      case H.LetF(funs, body) => {
        val funNames = funs.map(x => x.name)
        val newFunNames = funNames.map[L.Name](_ => freshW).toSeq

        val freeVars = funs.map(x => freeVariablesFun(x, env).toSeq)
        // pair in this foldLeft below represents the pair (set of free variable names, index)
        val filledEnv = freeVars.zipWithIndex
          .foldLeft(env)((e, pair) => e.updated(funNames(pair._2), (newFunNames(pair._2), pair._1)))

        val closedFuns = funs.zip(newFunNames).zip(freeVars)
          .map(x => closeFun(x._1._1, x._1._2, x._2, filledEnv))

        val translatedBody = translate(body, filledEnv)
        val initializedClosures = funNames.zip(newFunNames).zip(freeVars)
          .foldRight(translatedBody)((x, y) => initClosure(x._1._1, x._1._2, x._2, y))
        val allocatedClosures = funNames.zip(freeVars)
          .foldRight(initializedClosures)((x, y) => allocateClosure(x._1, x._2, y))

        L.LetF(closedFuns, allocatedClosures)
      }
      case H.AppF(fun, retC, args) => {
        val frF = freshF
        L.LetP(frF, CPS.BlockGet, Seq(rewrite(fun), L.AtomL(0)), L.AppF(L.AtomN(frF), retC, rewrite(fun) +: args.map(x => rewrite(x))))
      }
      case H.LetC(cnts, body) => {
        L.LetC(cnts.map(x => L.Cnt(x.name, x.args, translate(x.body, env))), translate(body, env))
      }
      case H.AppC(Symbol.HALT, args) => {
        shiftRightOne(rewrite(args.head)) {
          x1 => L.AppC(Symbol.HALT, Seq(x1))
        }
      }
      case H.AppC(cnt, args) => L.AppC(cnt, args.map(x => rewrite(x)))

      // Translations regarding type Integer start here.
      case H.If(L3.IntP, Seq(value), ct, cf) => {
        val frT = freshT
        L.LetP(frT, CPS.And, Seq(rewrite(value), L.AtomL(1)),
          L.If(CPST.Eq, Seq(L.AtomN(frT), L.AtomL(1)), ct, cf))
      }
      // Integer arithmetic primitives.
      case H.LetP(name, L3.IntAdd, Seq(x, y), body) => {
        subOne(rewrite(x)){
          x1 => L.LetP(name, CPS.Add, Seq(x1, rewrite(y)), translate(body, env))
        }
      }
      case H.LetP(name, L3.IntSub, Seq(x, y), body) => {
        addOne(rewrite(x)) {
          x1 => L.LetP(name, CPS.Sub, Seq(x1, rewrite(y)), translate(body, env))
        }
      }
      case H.LetP(name, L3.IntMul, Seq(x, y), body) => {
        subOne(rewrite(x)) {
          x1 => shiftRightOne(rewrite(y)) {
            x2 => tempLetP(CPS.Mul, Seq(x1, x2)) {
              x3 => addOneLetP(name, x3, translate(body, env))
            }
          }
        }
      }
      case H.LetP(name, L3.IntDiv, Seq(x, y), body) => {
        subOne(rewrite(x)) {
          x1 => subOne(rewrite(y)) {
            x2 => tempLetP(CPS.Div, Seq(x1, x2)) {
              x3 => shiftLeftOne(x3){
                x4 => addOneLetP(name, x4, translate(body, env))
              }
            }
          }
        }
      }
      case H.LetP(name, L3.IntMod, Seq(x, y), body) => {
        subOne(rewrite(x)) {
          x1 => subOne(rewrite(y)) {
            x2 => tempLetP(CPS.Mod, Seq(x1, x2)) {
              x3 => addOneLetP(name, x3, translate(body, env))
            }
          }
        }
      }

      // Bitwise primitives
      case H.LetP(name, L3.IntShiftLeft, Seq(x, y), body) => {
        subOne(rewrite(x)) {
          x1 => shiftRightOne(rewrite(y)){
            x2 => tempLetP(CPS.ShiftLeft, Seq(x1, x2)){
              x3 => addOneLetP(name, x3, translate(body, env))
            }
          }
        }
      }
      case H.LetP(name, L3.IntShiftRight, Seq(x, y), body) => {
        shiftRightOne(rewrite(y)){
          x1 => tempLetP(CPS.ShiftRight, Seq(rewrite(x), x1)){
            x2 => L.LetP(name, CPS.Or, Seq(x2, L.AtomL(1)), translate(body, env))
          }
        }
      }
      case H.LetP(name, L3.IntBitwiseAnd, Seq(x, y), body) => {
        L.LetP(name, CPS.And, Seq(rewrite(x), rewrite(y)), translate(body, env))
      }
      case H.LetP(name, L3.IntBitwiseOr, Seq(x, y), body) => {
        L.LetP(name, CPS.Or, Seq(rewrite(x), rewrite(y)), translate(body, env))
      }
      case H.LetP(name, L3.IntBitwiseXOr, Seq(x, y), body) => {
        tempLetP(CPS.XOr, Seq(rewrite(x), rewrite(y))){
          x1 => addOneLetP(name, x1, translate(body, env))
        }
      }

      // Integer comparisons.
      case H.If(L3.IntLt, Seq(x, y), ct, cf) => {
        L.If(CPST.Lt, Seq(rewrite(x), rewrite(y)), ct, cf)
      }
      case H.If(L3.IntLe, Seq(x, y), ct, cf) => {
        L.If(CPST.Le, Seq(rewrite(x), rewrite(y)), ct, cf)
      }

      // Byte-read and Byte-write
      case H.LetP(name, L3.ByteRead, Seq(), body) => {
        tempLetP(CPS.ByteRead, Seq()) {
          x1 => shiftLeftOne(x1) {
            x2 => addOneLetP(name, x2, translate(body, env))
          }
        }
      }
      case H.LetP(name, L3.ByteWrite, Seq(value), body) => {
        shiftRightOne(rewrite(value)) {
          x1 => L.LetP(name, CPS.ByteWrite, Seq(x1), translate(body, env))
        }
      }

      // Block primitives.
      case H.If(L3.BlockP, Seq(value), ct, cf) => {
        val frT = freshT
        L.LetP(frT, CPS.And, Seq(rewrite(value), L.AtomL(3)),
          L.If(CPST.Eq, Seq(L.AtomN(frT), L.AtomL(0)), ct, cf))
      }
      case H.LetP(name, L3.BlockAlloc(tag), Seq(length), body) => {
        shiftRightOne(rewrite(length)){
          x1 => L.LetP(name, CPS.BlockAlloc(tag), Seq(x1), translate(body, env))
        }
      }
      case H.LetP(name, L3.BlockTag, Seq(block), body) => {
        tempLetP(CPS.BlockTag, Seq(rewrite(block))){
          x1 => shiftLeftOne(x1){
            x2 => addOneLetP(name, x2, translate(body, env))
          }
        }
      }
      case H.LetP(name, L3.BlockLength, Seq(block), body) => {
        tempLetP(CPS.BlockLength, Seq(rewrite(block))){
          x1 => shiftLeftOne(x1){
            x2 => addOneLetP(name, x2, translate(body, env))
          }
        }
      }
      case H.LetP(name, L3.BlockGet, Seq(block, n), body) => {
        shiftRightOne(rewrite(n)){
          x1 => L.LetP(name, CPS.BlockGet, Seq(rewrite(block), x1), translate(body, env))
        }
      }
      case H.LetP(name, L3.BlockSet, Seq(block, n, value), body) => {
        shiftRightOne(rewrite(n)){
          x1 => L.LetP(name, CPS.BlockSet, Seq(rewrite(block), x1, rewrite(value)), translate(body, env))
        }
      }

      // Translations regarding type Character start here.
      case H.If(L3.CharP, Seq(value), ct, cf) => {
        val frT = freshT
        L.LetP(frT, CPS.And, Seq(rewrite(value), L.AtomL(7)),
          L.If(CPST.Eq, Seq(L.AtomN(frT), L.AtomL(6)), ct, cf))
      }
      case H.LetP(name, L3.CharToInt, Seq(value), body) => {
        L.LetP(name, CPS.ShiftRight, Seq(rewrite(value), L.AtomL(2)), translate(body, env))
      }
      case H.LetP(name, L3.IntToChar, Seq(value), body) => {
        tempLetP(CPS.ShiftLeft, Seq(rewrite(value), L.AtomL(2))) {
          x => L.LetP(name, CPS.Add, Seq(x, L.AtomL(2)), translate(body, env))
        }
      }

      // Translations regarding types Boolean and Unit start here.
      case H.If(L3.BoolP, Seq(value), ct, cf) => {
        val frT = freshT
        L.LetP(frT, CPS.And, Seq(rewrite(value), L.AtomL(bitsToIntMSBF(1, 1, 1, 1))),
          L.If(CPST.Eq, Seq(L.AtomN(frT), L.AtomL(bitsToIntMSBF(1, 0, 1, 0))), ct, cf))
      }
      case H.If(L3.UnitP, Seq(value), ct, cf) => {
        val frT = freshT
        L.LetP(frT, CPS.And, Seq(rewrite(value), L.AtomL(bitsToIntMSBF(1, 1, 1, 1))),
          L.If(CPST.Eq, Seq(L.AtomN(frT), L.AtomL(2)), ct, cf))
      }

      // Arbitrary value primitives (Eq and Id)
      case H.If(L3.Eq, Seq(x, y), ct, cf) => {
        L.If(CPST.Eq, Seq(rewrite(x), rewrite(y)), ct, cf)
      }
      case H.LetP(name, L3.Id, Seq(value), body) => {
        L.LetP(name, CPS.Id, Seq(rewrite(value)), translate(body, env))
      }
    }
  }

  // Translating (tagging) literals.
  private def rewrite(a: H.Atom): L.Atom = {

    a match {
      case H.AtomN(n) => L.AtomN(n)
      case H.AtomL(IntLit(value)) => {
        L.AtomL((value.toInt << 1) | bitsToIntMSBF(1))
      }
      case H.AtomL(BooleanLit(value)) => {
        if (value)
          return L.AtomL(bitsToIntMSBF(1, 1, 0, 1, 0))
        L.AtomL(bitsToIntMSBF(0, 1, 0, 1, 0))
      }
      case H.AtomL(UnitLit) => L.AtomL(bitsToIntMSBF(0, 0, 1, 0))
      case H.AtomL(CharLit(value)) => L.AtomL((value << 3) | bitsToIntMSBF(1, 1, 0))
    }
  }

  // Free variables gathering.
  private def freeVariables(tree: H.Tree, env: Environment): Set[H.Name] = {
    tree match {
      case H.LetP(name, _, args, body) => {
        (freeVariables(body, env) - name) | args.map(x => freeVariablesAtoms(x)).fold(Set())((x, y) => x | y)
      }
      case H.LetC(cnts, body) => {
        freeVariables(body, env) | cnts.map(x => freeVariablesCnt(x, env)).fold(Set())((x, y) => x | y)
      }
      case H.LetF(funs, body) => {
        (freeVariables(body, env) |
          funs.map(x => freeVariablesFun(x, env)).fold(Set())((x, y) => x | y)) &~ funs.map(x => x.name).toSet
      }
      case H.AppC(_, args) => args.map(x => freeVariablesAtoms(x)).fold(Set())((x, y) => x | y)
      case H.AppF(fun, _, args) => freeVariablesAtoms(fun) | args.map(x => freeVariablesAtoms(x)).fold(Set())((x, y) => x | y)

      case H.If(_, args, _, _) => args.map(x => freeVariablesAtoms(x)).fold(Set())((x, y) => x | y)
    }
  }

  private def freeVariablesFun(fun: H.Fun, env: Environment): Set[H.Name] = {
    freeVariables(fun.body, env) &~ fun.args.toSet - fun.name
  }

  private def freeVariablesCnt(cnt: H.Cnt, env: Environment): Set[H.Name] = {
    freeVariables(cnt.body, env) &~ cnt.args.toSet
  }

  private def freeVariablesAtoms(atom: H.Atom): Set[H.Name] = {
    atom match {
      case H.AtomN(name) => Set(name)
      case H.AtomL(_) => Set()
    }
  }

  // Substitution function.filledEnv
  private def substitute(tree: L.Tree, s: Subst[Symbol]): L.Tree = {
    def substT(tree: L.Tree): L.Tree = tree match {
      case L.LetP(name, prim, args, body) => L.LetP(name, prim, args map substA, substT(body))
      case L.LetC(cnts, body) => L.LetC(cnts.map(x => substC(x)), substT(body))
      case L.LetF(funs, body) => L.LetF(funs.map(x => substF(x)), substT(body))
      case L.AppC(cnt, args) => L.AppC(cnt, args.map(x => substA(x)))
      case L.AppF(fun, retC, args) => L.AppF(substA(fun), retC, args.map(x => substA(x)))
      case L.If(cond, args, ct, cf) => L.If(cond, args.map(x => substA(x)), ct, cf)
    }

    def substC(cnt: L.Cnt): L.Cnt =
      L.Cnt(cnt.name, cnt.args, substT(cnt.body)) // code for continuation definitions

    def substF(fun: L.Fun): L.Fun =
      L.Fun(fun.name, fun.retC, fun.args, substT(fun.body)) // code for function definitions

    def substA(atom: L.Atom): L.Atom =
      atom match {
        case L.AtomN(name) => L.AtomN(s(name))
        case L.AtomL(value) => L.AtomL(value)
      }// code for atoms

    substT(tree)
  }

  // Some helper functions.

  private def closeFun(fun: H.Fun, w: L.Name, freeVars: Seq[L.Name], env: Environment): L.Fun = {

    val frEnv = freshEnv
    val freshVs = freeVars.map(_ => freshV)
    val translatedBody = translate(fun.body, env)
    val substitution = subst(fun.name +: freeVars, frEnv +: freshVs)

    val newFunBody = freshVs.zipWithIndex
      .foldRight(translatedBody)((x, y) => L.LetP(x._1, CPS.BlockGet, Seq(L.AtomN(frEnv), L.AtomL(x._2+1)), y))
    val substitutedBody = substitute(newFunBody, substitution)

    L.Fun(w, fun.retC, frEnv +: fun.args, substitutedBody)
  }

  private def initClosure(funName: L.Name, w: L.Name, freeVars: Seq[L.Name], body: L.Tree): L.Tree = {
    (w +: freeVars).zipWithIndex
      .foldRight(body)((x, y) =>
        L.LetP(freshT, CPS.BlockSet, Seq(L.AtomN(funName), L.AtomL(x._2), L.AtomN(x._1)), y))
  }

  private def allocateClosure(funName: L.Name, freeVars: Seq[L.Name], body: L.Tree): L.Tree = {
    L.LetP(funName, CPS.BlockAlloc(BlockTag.Function), Seq(L.AtomL(freeVars.size + 1)), body)
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.AtomN => L.Tree): L.Tree = {
    val frT = freshT
    L.LetP(frT, p, args, body(L.AtomN(frT)))
  }

  private def subOne(arg: L.Atom)(body: L.AtomN => L.Tree): L.Tree = {
    val frT = freshT
    L.LetP(frT, CPS.Sub, Seq(arg, L.AtomL(1)), body(L.AtomN(frT)))
  }

  private def addOne(arg: L.Atom)(body: L.AtomN => L.Tree): L.Tree = {
    val frT = freshT
    L.LetP(frT, CPS.Add, Seq(arg, L.AtomL(1)), body(L.AtomN(frT)))
  }

  private def addOneLetP(name: L.Name, arg: L.Atom, body: L.Tree): L.Tree = {
    L.LetP(name, CPS.Add, Seq(arg, L.AtomL(1)), body)
  }

  private def shiftRightOne(arg: L.Atom)(body: L.AtomN => L.Tree): L.Tree = {
    val frT = freshT
    L.LetP(frT, CPS.ShiftRight, Seq(arg, L.AtomL(1)), body(L.AtomN(frT)))
  }

  private def shiftLeftOne(arg: L.Atom)(body: L.AtomN => L.Tree): L.Tree = {
    val frT = freshT
    L.LetP(frT, CPS.ShiftLeft, Seq(arg, L.AtomL(1)), body(L.AtomN(frT)))
  }
}