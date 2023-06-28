package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF = {
    tree match {

      case LetP(name, prim, args, body) => {
        val translated = apply(body)
        LetF(translated.funs, LetP(name, prim, args, translated.body))
      }
      case LetC(cnts, body) => {
        val translatedBody = apply(body)
        val newCnts = cnts.map(x => newCnt(x))
        val funs = (newCnts.map(x => x._1) :+ translatedBody.funs).flatten
        LetF(funs, LetC(newCnts.map(x => x._2), translatedBody.body))
      }
      case LetF(funs, body) => {
        val translatedBody = apply(body)
        val newFuns = funs.map(x => newFun(x))
        val resultFuns = newFuns.map(x => x._2) ++ (newFuns.map(x => x._1) :+ translatedBody.funs).flatten
        LetF(resultFuns, translatedBody.body)
      }
      case otherExpr => LetF(Seq(), otherExpr)
    }
  }

  // Some helper functions.
  private def newCnt(oldCnt: Cnt): (Seq[Fun], Cnt) = {
    val translatedBody = apply(oldCnt.body)
    (translatedBody.funs, Cnt(oldCnt.name, oldCnt.args, translatedBody.body))
  }

  private def newFun(oldFun: Fun): (Seq[Fun], Fun) = {
    val translatedBody = apply(oldFun.body)
    (translatedBody.funs, Fun(oldFun.name, oldFun.retC, oldFun.args, translatedBody.body))
  }
}
