package l3

import collection.mutable.{ Map => MutableMap }

import CPSValuePrimitive._
import RegisterCPSTreeModule._
import LabeledASMInstructionModule._

/**
  * An ASM code generator for CPS/L₃.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object CPSToASMTranslator extends (LetF => LabeledProgram) {
  def apply(prog: LetF): LabeledProgram = {
    implicit val retContArg: Map[Symbol, ASMRegister] = Map()

    val funs = prog.funs map { case Fun(Label(name), _, _, body) =>
      name -> labeled(name, linearize(body, prelude(body))) }

    linearize(prog.body, prelude(prog.body)) ++ glue(funs)
  }

  private def glue(funs: Seq[(Symbol, LabeledProgram)]): LabeledProgram = {
    def loop(w: Seq[Symbol], fs: Map[Symbol, LabeledProgram])
        : Map[Symbol, LabeledProgram] = w match {
      case n +: ns =>
        fs(n).last match {
          case LabeledInstruction(l, JUMP_D(m)) if m != n && fs.contains(m) =>
            val nm = fs(n).init ++ labeled(l, fs(m))
            loop(n +: ns.diff(Seq(m)), fs - m + (n -> nm))
          case _ =>
            loop(ns, fs)
        }
      case Seq() =>
        fs
    }

    val gluedFuns = loop(funs.map(_._1), funs.toMap)
    funs.flatMap(p => gluedFuns.getOrElse(p._1, Seq()))
  }

  private object RAtom {
    def unapply(atom: Atom): Option[ASMRegister] = atom match {
      case AtomN(Reg(r)) => Some(r)
      case _ => None
    }
  }

  private def prelude(body: Tree): LabeledProgram = {
    def usedRegs(tree: Tree): Set[ASMRegister.Local] = {
      def regIn(a: Atom): Set[ASMRegister.Local] = a match {
        case RAtom(r @ ASMRegister.Local(_)) => Set(r)
        case _ => Set.empty
      }

      def regsIn(aa: Seq[Atom]): Set[ASMRegister.Local] =
        aa.flatMap(regIn).toSet

      (tree: @unchecked) match {
        case LetP(_, ByteWrite | BlockSet, args, body) =>
          regsIn(args) | usedRegs(body)
        case LetP(Reg(r @ ASMRegister.Local(_)), _, args, body) =>
          Set(r) | regsIn(args) | usedRegs(body)
        case LetC(cnts, body) =>
          cnts.foldLeft(usedRegs(body)) { case (rs, c) =>
            rs | regsIn(c.args map AtomN) | usedRegs(c.body)
          }
        case AppC(c, args) =>
          regIn(AtomN(c)) | regsIn(args)
        case AppF(f, retC, args) =>
          regIn(f) | regIn(AtomN(retC)) | regsIn(args)
        case If(_, args, tc, ec) =>
          regsIn(args) | regIn(AtomN(tc)) | regIn(AtomN(ec))
      }
    }

    usedRegs(body)
      .map(_.index)
      .maxOption
      .map(maxR => nl(FRAME(maxR + 1)))
      .toSeq
  }

  private val conts = MutableMap[Symbol, Tree]()

  private def linearize(tree: Tree, acc: LabeledProgram = Seq())
                       (implicit retContArg: Map[Symbol, ASMRegister])
      : LabeledProgram = {
    def contOrJump(l: Symbol): LabeledProgram = conts.remove(l)
      .map(b => labeled(l, linearize(b)))
      .getOrElse(Seq(nl(JUMP_D(l))))

    def condJump(p: CPSTestPrimitive,
                 a: ASMRegister,
                 b: ASMRegister,
                 w: Boolean,
                 c: Symbol) = {
      import CPSTestPrimitive._

      (p, w) match {
        case (Lt, true)  => nl(JLT(a, b, LabelC(c)))
        case (Lt, false) => nl(JLE(b, a, LabelC(c)))
        case (Le, true)  => nl(JLE(a, b, LabelC(c)))
        case (Le, false) => nl(JLT(b, a, LabelC(c)))
        case (Eq, true)  => nl(JEQ(a, b, LabelC(c)))
        case (Eq, false) => nl(JNE(a, b, LabelC(c)))
      }
    }

    def pushArgs(args: Seq[Atom]): LabeledProgram =
      if (args.isEmpty)
        Seq(nl(ARGS(ASMRegister.C0, ASMRegister.C0, ASMRegister.C0)))
      else args.grouped(3).toSeq.map {
        case Seq(RAtom(r1), RAtom(r2), RAtom(r3)) => nl(ARGS(r1, r2, r3))
        case Seq(RAtom(r1), RAtom(r2)) => nl(ARGS(r1, r2, ASMRegister.C0))
        case Seq(RAtom(r1)) => nl(ARGS(r1, ASMRegister.C0, ASMRegister.C0))
      }

    tree match {
      case LetP(Reg(a), Add, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(ADD(a, b, c)))
      case LetP(Reg(a), Sub, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(SUB(a, b, c)))
      case LetP(Reg(a), Mul, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(MUL(a, b, c)))
      case LetP(Reg(a), Div, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(DIV(a, b, c)))
      case LetP(Reg(a), Mod, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(MOD(a, b, c)))

      case LetP(Reg(a), ShiftLeft, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(LSL(a, b, c)))
      case LetP(Reg(a), ShiftRight, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(LSR(a, b, c)))
      case LetP(Reg(a), And, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(AND(a, b, c)))
      case LetP(Reg(a), Or, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(OR(a, b, c)))
      case LetP(Reg(a), XOr, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(XOR(a, b, c)))

      case LetP(Reg(a), ByteRead, Seq(), body) =>
        linearize(body, acc :+ nl(BREA(a)))
      case LetP(_, ByteWrite, Seq(RAtom(a)), body) =>
        linearize(body, acc :+ nl(BWRI(a)))

      case LetP(Reg(a), BlockAlloc(t), Seq(RAtom(b)), body) =>
        linearize(body, acc :+ nl(BALO(a, b, t)))
      case LetP(Reg(a), BlockTag, Seq(RAtom(b)), body) =>
        linearize(body, acc :+ nl(BTAG(a, b)))
      case LetP(Reg(a), BlockLength, Seq(RAtom(b)), body) =>
        linearize(body, acc :+ nl(BSIZ(a, b)))
      case LetP(Reg(a), BlockGet, Seq(RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(BGET(a, b, c)))
      case LetP(_, BlockSet, Seq(RAtom(a), RAtom(b), RAtom(c)), body) =>
        linearize(body, acc :+ nl(BSET(c, a, b)))

      case LetP(Reg(a), Id, Seq(AtomL(v)), body) if fitsInNSignedBits(19)(v) =>
        linearize(body, acc :+ nl(LDLO(a, IntC(v))))
      case LetP(Reg(a), Id, Seq(AtomL(v)), body) =>
        val lsb16: Int = v & 0xFFFF
        val msb16: Int = v >>> 16
        linearize(body, acc :+ nl(LDLO(a, IntC(lsb16))) :+ nl(LDHI(a, msb16)))

      case LetP(Reg(a), Id, Seq(RAtom(b)), body) if a == b =>
        linearize(body, acc)
      case LetP(Reg(a), Id, Seq(RAtom(b)), body) =>
        linearize(body, acc :+ nl(MOVE(a, b)))
      case LetP(Reg(a), Id, Seq(AtomN(Label(l))), body) =>
        linearize(body, acc :+ nl(LDLO(a, LabelC(l))))

      case LetC(cnts, body) =>
        conts ++= cnts map { case Cnt(Label(name), _, body) => name -> body }
        val retContArg1 = cnts.foldLeft(retContArg) {
          case (rca, Cnt(Label(name), Seq(Reg(a)), _)) => rca + (name -> a)
          case (rca, _) => rca }
        linearize(body, acc)(retContArg1)

      case AppC(Label(Symbol.HALT), Seq(RAtom(arg))) =>
        acc :+ nl(HALT(arg))
      case AppC(Label(c), _) =>
        acc ++ contOrJump(c)
      case AppC(Reg(ASMRegister.Link), Seq(RAtom(r))) =>
        acc :+ nl(RET(r))

      case AppF(RAtom(fun), Label(rc), args) =>
        val r = retContArg(rc)
        (acc ++ pushArgs(args) :+ nl(CALL_I(r, fun))) ++ contOrJump(rc)
      case AppF(AtomN(Label(fun)), Label(rc), args) =>
        val r = retContArg(rc)
        (acc ++ pushArgs(args) :+ nl(CALL_D(r, fun))) ++ contOrJump(rc)
      case AppF(RAtom(fun), Reg(ASMRegister.Link), _) =>
        acc :+ nl(JUMP_I(fun))
      case AppF(AtomN(Label(fun)), Reg(ASMRegister.Link), _) =>
        acc :+ nl(JUMP_D(fun))

      case If(p, Seq(RAtom(a), RAtom(b)), Label(thenC), Label(elseC)) =>
        (conts remove thenC, conts remove elseC) match {
          case (Some(thenT), Some(elseT)) =>
            val thenP = labeled(thenC, linearize(thenT))
            val elseP = labeled(elseC, linearize(elseT))
            (acc :+ condJump(p, a, b, false, elseC)) ++ thenP ++ elseP
          case (Some(thenT), None) =>
            val thenP = labeled(thenC, linearize(thenT))
            (acc :+ condJump(p, a, b, false, elseC)) ++ thenP
          case (None, Some(elseT)) =>
            val elseP = labeled(elseC, linearize(elseT))
            (acc :+ condJump(p, a, b, true, thenC)) ++ elseP
          case (None, None) =>
            acc :+ condJump(p, a, b, true, thenC) :+ nl(JUMP_D(elseC))
        }
    }
  }
}
