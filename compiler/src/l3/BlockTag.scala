package l3

import scala.collection.mutable.{Map => MutableMap}

/**
  * Tags for blocks.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object BlockTag {
  private[this] val tagValue = MutableMap[String, Int]()

  val MAX_TAG = 0xFF

  def resolve(tagName: String): Int =
    if (tagValue.contains(tagName)) {
      tagValue(tagName)
    } else {
      val tag = tagValue.size
      assume(tag <= MAX_TAG)
      tagValue.put(tagName, tag)
      tag
    }

  val FreeBlock = resolve("_free-block")         // 0 (must be!)
  val RegisterFrame = resolve("_register-frame") // 1
  val Function = resolve("_function")            // 2
  val String = resolve("_string")                // 3
}
