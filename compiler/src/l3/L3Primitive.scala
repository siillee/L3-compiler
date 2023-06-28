package l3

/**
  * A class for L₃ primitives.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class L3Primitive(val name: String, val arity: Int) {
  override def toString: String = name
}

sealed abstract class L3ValuePrimitive(name: String, arity: Int)
    extends L3Primitive(name, arity)
sealed abstract class L3TestPrimitive(name: String, arity: Int)
    extends L3Primitive(name, arity)

object L3Primitive {
  // Primitives on blocks
  case class BlockAlloc(tag: L3BlockTag)
      extends L3ValuePrimitive(s"${blockAllocPrefix}${tag}", blockAllocArity)
  case object BlockP extends L3TestPrimitive("block?", 1)
  case object BlockTag extends L3ValuePrimitive("block-tag", 1)
  case object BlockLength extends L3ValuePrimitive("block-length", 1)
  case object BlockGet extends L3ValuePrimitive("block-get", 2)
  case object BlockSet extends L3ValuePrimitive("block-set!", 3)

  // Primitives on integers
  case object IntP extends L3TestPrimitive("int?", 1)

  case object IntAdd extends L3ValuePrimitive("+", 2)
  case object IntSub extends L3ValuePrimitive("-", 2)
  case object IntMul extends L3ValuePrimitive("*", 2)
  case object IntDiv extends L3ValuePrimitive("/", 2)
  case object IntMod extends L3ValuePrimitive("%", 2)

  case object IntShiftLeft extends L3ValuePrimitive("shift-left", 2)
  case object IntShiftRight extends L3ValuePrimitive("shift-right", 2)
  case object IntBitwiseAnd extends L3ValuePrimitive("and", 2)
  case object IntBitwiseOr extends L3ValuePrimitive("or", 2)
  case object IntBitwiseXOr extends L3ValuePrimitive("xor", 2)

  case object IntLt extends L3TestPrimitive("<", 2)
  case object IntLe extends L3TestPrimitive("<=", 2)

  case object ByteRead extends L3ValuePrimitive("byte-read", 0)
  case object ByteWrite extends L3ValuePrimitive("byte-write", 1)

  case object IntToChar extends L3ValuePrimitive("int->char", 1)

  // Primitives on characters
  case object CharP extends L3TestPrimitive("char?", 1)

  case object CharToInt extends L3ValuePrimitive("char->int", 1)

  // Primitives on booleans
  case object BoolP extends L3TestPrimitive("bool?", 1)

  // Primitives on unit
  case object UnitP extends L3TestPrimitive("unit?", 1)

  // Primitives on arbitrary values

  case object Eq extends L3TestPrimitive("=", 2)
  case object Id extends L3ValuePrimitive("id", 1)

  def isDefinedAt(name: String): Boolean =
    isBlockAlloc(name) || byName.isDefinedAt(name)

  def isDefinedAt(name: String, arity: Int): Boolean =
    ((isBlockAlloc(name) && arity == blockAllocArity)
       || (byName.isDefinedAt(name) && byName(name).arity == arity))

  def apply(name: String): L3Primitive =
    if (isBlockAlloc(name))
      blockAllocators(l3.BlockTag.resolve(blockAllocTag(name)))
    else
      byName(name)

  private[this] val blockAllocPrefix = "block-alloc-"
  private[this] val blockAllocArity = 1

  private[this] def isBlockAlloc(name: String): Boolean =
    name.startsWith(blockAllocPrefix)

  private[this] def blockAllocTag(name: String): String = {
    assume(isBlockAlloc(name))
    name.drop(blockAllocPrefix.length)
  }

  private val blockAllocators =
    for (i <- 0 to l3.BlockTag.MAX_TAG) yield BlockAlloc(i)

  // Note: private primitives (only "id" for now) are ommitted from
  // this map, as they are not meant to be used by user code.
  private val byName: Map[String, L3Primitive] =
    Map((Seq(BlockP, BlockTag, BlockLength, BlockGet, BlockSet,
             IntP, IntAdd, IntSub, IntMul, IntDiv, IntMod,
             IntShiftLeft, IntShiftRight,
             IntBitwiseAnd, IntBitwiseOr, IntBitwiseXOr,
             IntLt, IntLe, Eq, IntToChar,
             CharP, ByteRead, ByteWrite, CharToInt,
             BoolP,
             UnitP) ++ blockAllocators)
          map { p => (p.name, p) } : _*)
}
