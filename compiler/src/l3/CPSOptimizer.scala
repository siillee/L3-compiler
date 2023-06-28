package l3

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class Block(name: Name, values: Map[Atom, Atom], tag: Literal, size: Atom, immutable: Boolean)

  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
    cEnv: Map[Name, Cnt] = Map.empty,
    fEnv: Map[Name, Fun] = Map.empty,
    bEnv: Map[Name, Block] = Map.empty) {

    def dead(s: Name): Boolean =
      ! census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
    def withBlock(blockName: Name, block: Block): State =
      copy(bEnv = bEnv + (blockName -> block))
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  private def shrink(tree: Tree, s: State): Tree = {
    tree match {
      case LetP(name, prim, _, body) if s.dead(name) && !impure(prim) => {
        shrink(body, s)
      }
      case LetP(name, prim, args, body)  if s.eInvEnv.contains((prim, args))
          && !impure(prim) && !unstable(prim) => {
        shrink(body, s.withASubst(name, s.eInvEnv((prim, args))))
      }
      case LetP(name, prim, args, body) if args.forall(x => x.asLiteral.nonEmpty)
          && vEvaluator.isDefinedAt(prim, args.map(x => x.asLiteral.get)) => {
        shrink(body, s.withASubst(name, vEvaluator(prim, args.map(x => x.asLiteral.get))))
      }
      case LetP(name, prim, args, body) if args.nonEmpty && args.forall(x => x == args.head)
          && sameArgReduce.isDefinedAt(prim, args.head)=> {
        shrink(body, s.withASubst(name, sameArgReduce(prim, args.head)))
      }
      case LetP(name, prim, Seq(AtomL(value), y), body) if leftNeutral.contains((value, prim)) => {
        shrink(body, s.withASubst(name, y))
      }
      case LetP(name, prim, Seq(x, AtomL(value)), body) if rightNeutral.contains((prim, value)) => {
        shrink(body, s.withASubst(name, x))
      }
      case LetP(name, prim, Seq(AtomL(value), _), body) if leftAbsorbing.contains((value, prim)) => {
        shrink(body, s.withASubst(name, value))
      }
      case LetP(name, prim, Seq(_, AtomL(value)), body) if rightAbsorbing.contains((prim, value)) => {
        shrink(body, s.withASubst(name, value))
      }
      case LetP(name, prim, args, body) if blockAllocTag.isDefinedAt(prim) => {
        if (s.dead(name)) {
          shrink(body, s)
        }
        val tag = blockAllocTag(prim)
        val immutable = tag == BlockTag.Function || tag == BlockTag.String
        val updatedState = s.withBlock(name, Block(name, Map.empty, tag, args.head, immutable))

        LetP(name, prim, args.map(x => s.aSubst(x)), shrink(body, updatedState))
      }
      case LetP(name, prim, Seq(b, i, a), body) if prim == blockSet && s.bEnv.contains(b.asName.get) => {
        val block = s.bEnv(b.asName.get)
        val newBlock = Block(block.name, block.values + (i -> a), block.tag, block.size, block.immutable)
        LetP(name, prim, Seq(b, i, a).map(x => s.aSubst(x)), shrink(body, s.withBlock(name, newBlock)))
      }
      case LetP(name, prim, Seq(b, i), body) if prim == blockGet
          && s.bEnv.contains(b.asName.get) && s.bEnv(b.asName.get).immutable && s.bEnv(b.asName.get).values.contains(i) => {
        shrink(body, s.withASubst(name, s.bEnv(b.asName.get).values(i)))
      }
      case LetP(name, prim, Seq(blockName), body) if prim == blockLength && s.bEnv.contains(blockName.asName.get) => {
        shrink(body, s.withASubst(name, s.bEnv(blockName.asName.get).size))
      }
      case LetP(name, prim, Seq(blockName), body) if prim == blockTag && s.bEnv.contains(blockName.asName.get) => {
        shrink(body, s.withASubst(name, s.bEnv(blockName.asName.get).tag))
      }
      case LetP(name, prim, args, body) if prim == identity => {
        shrink(body, s.withASubst(name, args.head))
      }
      case LetP(name, prim, args, body) => {
        LetP(name, prim, args.map(x => s.aSubst(x)), shrink(body, s.withExp(name, prim, args.map(x => s.aSubst(x)))))
      }
      case LetF(funs, body) => {
        val nonDeadFuns = funs.filterNot(x => s.dead(x.name))
        val appliedOnceFuns = nonDeadFuns.filter(x => s.appliedOnce(x.name))
        val normalFuns = nonDeadFuns.filterNot(x => s.appliedOnce(x.name))
        val updatedState = s.withFuns(appliedOnceFuns)
        if (normalFuns.nonEmpty) {
          LetF(normalFuns.map(x => Fun(x.name, x.retC, x.args, shrink(x.body, updatedState))), shrink(body, updatedState))
        }else {
          shrink(body, updatedState)
        }
      }
      case LetC(cnts, body) => {
        val nonDeadCnts = cnts.filterNot(x => s.dead(x.name))
        val appliedOnceCnts = nonDeadCnts.filter(x => s.appliedOnce(x.name))
        val normalCnts = nonDeadCnts.filterNot(x => s.appliedOnce(x.name))
        val updatedState = s.withCnts(appliedOnceCnts)
        if (normalCnts.nonEmpty) {
          LetC(normalCnts.map(x => Cnt(x.name, x.args, shrink(x.body, updatedState))), shrink(body, updatedState))
        }else {
          shrink(body, updatedState)
        }
      }
      case If(cond, args, ct, cf) => {
        if (args.size > 1 && args.forall(x => x == args.head)) { // in case all arguments are equal
          if (sameArgReduceC(cond)) {
            AppC(ct, Seq())
          } else {
            AppC(cf, Seq())
          }
        }else if (args.forall(x => x.asLiteral.nonEmpty)) { // the other case of evaluating the condition
          if (cEvaluator.isDefinedAt(cond, args.map(x => x.asLiteral.get)) && cEvaluator(cond, args.map(x => x.asLiteral.get))) {
            AppC(ct, Seq())
          } else {
            AppC(cf, Seq())
          }
        }else {
          If(cond, args.map(x => s.aSubst(x)), s.cSubst(ct), s.cSubst(cf))
        }
      }
      case AppF(fun, retC, args) => {
        if (s.fEnv.contains(fun.asName.get)) {
          val funToInline = s.fEnv(fun.asName.get)
          shrink(funToInline.body, s.withCSubst(funToInline.retC, retC).withASubst(funToInline.args, args))
        }else {
          AppF(s.aSubst(fun), s.cSubst(retC), args.map(x => s.aSubst(x)))
        }
      }
      case AppC(cnt, args) => {
        if (s.cEnv.contains(cnt)) {
          val cntToInline = s.cEnv(cnt)
          shrink(cntToInline.body, s.withASubst(cntToInline.args, args))
        }else {
          AppC(s.cSubst(cnt), args.map(x => s.aSubst(x)))
        }
      }
    }
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy()
          LetP(name1, prim, args map subV,
               copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC))
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy())
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy())
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def sameLen[T,U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
        formalArgs.length == actualArgs.length

      def inlineT(tree: Tree)(implicit s: State): Tree = {
        tree match {
          case LetP(name, prim, args, body) => LetP(name, prim, args.map(x => s.aSubst(x)), inlineT(body))
          case LetF(funs, body) => {
            val smallFuns = funs.filter(x => size(x.body) <= funLimit)
            val updatedState = s.withFuns(smallFuns)
            LetF(funs.map(x => Fun(x.name, x.retC, x.args, inlineT(x.body)(updatedState))), inlineT(body)(updatedState))
          }
          case LetC(cnts, body) => {
            val smallCnts = cnts.filter(x => size(x.body) <= cntLimit)
            val updatedState = s.withCnts(smallCnts)
            LetC(cnts.map(x => Cnt(x.name, x.args, inlineT(x.body)(updatedState))), inlineT(body)(updatedState))
          }
          case AppF(fun, retC, args) => {
            if (s.fEnv.contains(fun.asName.get)) {
              val funToInline = s.fEnv(fun.asName.get)
              val updatedState = s.withCSubst(funToInline.retC, retC).withASubst(funToInline.args, args)
              copyT(funToInline.body, updatedState.aSubst, updatedState.cSubst)
            } else {
              AppF(s.aSubst(fun), s.cSubst(retC), args.map(x => s.aSubst(x)))
            }
          }
          case AppC(cnt, args) => {
            if (s.cEnv.contains(cnt)) {
              val cntToInline = s.cEnv(cnt)
              val updatedState = s.withASubst(cntToInline.args, args)
              copyT(cntToInline.body, updatedState.aSubst, s.cSubst)
            } else {
              AppC(s.cSubst(cnt), args.map(x => s.aSubst(x)))
            }
          }
          case If(cond, args, ct, cf) => If(cond, args.map(x => s.aSubst(x)), s.cSubst(ct), s.cSubst(cf))
        }
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val blockSet: ValuePrimitive
  protected val blockGet: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {

  import treeModule._
  import L3Primitive._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions

  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)

  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean = {
    Set(BlockSet, ByteRead, ByteWrite)
  }

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, IntAdd), (1, IntMul), (~0, IntBitwiseAnd), (0, IntBitwiseOr), (0, IntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((IntAdd, 0), (IntSub, 0), (IntMul, 1), (IntDiv, 1),
      (IntShiftLeft, 0), (IntShiftRight, 0),
      (IntBitwiseAnd, ~0), (IntBitwiseOr, 0), (IntBitwiseXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, IntMul), (0, IntDiv),
      (0, IntShiftLeft), (0, IntShiftRight),
      (0, IntBitwiseAnd), (~0, IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, 0), (IntBitwiseAnd, 0), (IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => AtomL(0)
    case (IntDiv, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case IntLe | Eq => true
    case IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (IntAdd, Seq(IntLit(x), IntLit(y))) => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y))) => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y))) => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y

    case (IntShiftLeft, Seq(IntLit(x), IntLit(y))) => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr, Seq(IntLit(x), IntLit(y))) => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y

    case (IntToChar, Seq(IntLit(L3Int(value)))) => CharLit(value)
    case (CharToInt, Seq(CharLit(value))) => value
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (Eq, Seq(IntLit(x), IntLit(y))) => x == y

    case (IntP, Seq(IntLit(_))) => true
    case (IntP, _) => false
    case (CharP, Seq(CharLit(_))) => true
    case (CharP, _) => false
    case (BoolP, Seq(BooleanLit(_))) => true
    case (BoolP, _) => false
    case (UnitP, Seq(UnitLit)) => true
    case (UnitP, _) => false
    case (BlockP, _) => false
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree @ LetF(_, _) => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
        (ShiftLeft, 0), (ShiftRight, 0),
        (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
        (0, ShiftLeft), (0, ShiftRight),
        (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => AtomL(0)
    case (Div, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (Add, Seq(x, y)) => x + y
    case (Sub, Seq(x, y)) => x - y
    case (Mul, Seq(x, y)) => x * y
    case (Div, Seq(x, y)) if y.toInt != 0 => x / y
    case (Mod, Seq(x, y)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x, y)) => x << y
    case (ShiftRight, Seq(x, y)) => x >> y
    case (And, Seq(x, y)) => x & y
    case (Or,  Seq(x, y)) => x | y
    case (XOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (Lt, Seq(x, y)) => x < y
    case (Le, Seq(x, y)) => x <= y
    case (Eq, Seq(x, y)) => x == y
  }
}
