package tip.lattices

import scala.language.implicitConversions

/**
 * Abstract domain for variable sizes using stepped intervals.
 */
object VariableSizeLattice extends LatticeWithOps {
  /** Abstract intervals corresponding to variable size categories */
  sealed trait SizeInterval
  case object Bottom     extends SizeInterval  // ⊥
  case object NegByte    extends SizeInterval  // [-2^7; -1]
  case object B0         extends SizeInterval  // [0; 0]
  case object B1         extends SizeInterval  // [1; 1]
  case object PosByte    extends SizeInterval  // [2; 2^7 - 1]
  case object NegInt     extends SizeInterval  // [-2^31; -1]
  case object CharRange  extends SizeInterval  // [2; 2^16 - 1]
  case object PosInt     extends SizeInterval  // [2; 2^31 - 1]
  case object NegBigInt  extends SizeInterval  // [-inf; -1]
  case object PosBigInt  extends SizeInterval  // [2; +inf]
  case object Any        extends SizeInterval  // ⊤

  /** Total order of intervals for join and widening */
  private val order: List[SizeInterval] = List(
    Bottom,
    NegByte, B0, B1, PosByte,
    NegInt,
    CharRange, PosInt,
    NegBigInt, PosBigInt,
    Any
  )

  // Lattice type
  type Element = SizeInterval

  /** Bottom element */
  val bottom: Element = Bottom

  /** Top element */
  override val top: Element = Any

  /** Lift an integer constant into the lattice */
  def num(i: Int): Element = i match {
    case x if x >= -128   && x <= -1        => NegByte
    case 0                                   => B0
    case 1                                   => B1
    case x if x >= 2      && x <= 127       => PosByte
    case x if x >= Int.MinValue && x <= -1  => NegInt
    case x if x >= 2      && x <= Char.MaxValue => CharRange
    case x if x >= 2      && x <= Int.MaxValue  => PosInt
    case x if x <  Int.MinValue             => NegBigInt
    case x if x >  Int.MaxValue             => PosBigInt
  }

  /** Join (least upper bound) */
  def lub(a: Element, b: Element): Element = {
    order(math.max(order.indexOf(a), order.indexOf(b)))
  }

  /** Widening (same as lub for finite lattice) */
  def widen(a: Element, b: Element): Element = lub(a, b)

  // Helper: map SizeInterval to concrete bounds
  private def bounds(si: SizeInterval): (Long, Long) = si match {
    case NegByte   => (-128, -1)
    case B0        => (0, 0)
    case B1        => (1, 1)
    case PosByte   => (2, 127)
    case NegInt    => (Int.MinValue.toLong, -1)
    case CharRange => (2, Char.MaxValue.toLong)
    case PosInt    => (2, Int.MaxValue.toLong)
    case NegBigInt => (Long.MinValue, -1)
    case PosBigInt => (2, Long.MaxValue)
    case Bottom    => (Long.MaxValue, Long.MinValue)
    case Any       => (Long.MinValue, Long.MaxValue)
  }

  // Map a concrete interval to the smallest SizeInterval covering it
  private def fromBounds(low: Long, high: Long): Element = {
    // check each category in order and return first covering
    order.find {
      case NegByte   => low >= -128 && high <= -1
      case B0        => low == 0 && high == 0
      case B1        => low == 1 && high == 1
      case PosByte   => low >= 2 && high <= 127
      case NegInt    => low >= Int.MinValue && high <= -1
      case CharRange => low >= 2 && high <= Char.MaxValue
      case PosInt    => low >= 2 && high <= Int.MaxValue
      case NegBigInt => low >= Long.MinValue && high <= -1
      case PosBigInt => low >= 2 && high <= Long.MaxValue
      case Any       => true
      case Bottom    => false
    }.getOrElse(Any)
  }

  /** Abstract plus: combine bounds then map back */
  def plus(a: Element, b: Element): Element = {
    val (l1, h1) = bounds(a); val (l2, h2) = bounds(b)
    fromBounds(l1 + l2, h1 + h2)
  }

  /** Abstract minus: subtract bounds then map back */
  def minus(a: Element, b: Element): Element = {
    val (l1, h1) = bounds(a); val (l2, h2) = bounds(b)
    fromBounds(l1 - h2, h1 - l2)
  }

  /** Abstract times: multiply bounds then map back */
  def times(a: Element, b: Element): Element = {
    val (l1, h1) = bounds(a); val (l2, h2) = bounds(b)
    val products = Seq(l1 * l2, l1 * h2, h1 * l2, h1 * h2)
    fromBounds(products.min, products.max)
  }

  /** Abstract division: divide bounds (ignoring zero divide) then map back */
  def div(a: Element, b: Element): Element = {
    val (l1, h1) = bounds(a); val (l2, h2) = bounds(b)
    val quotients = Seq(
      if (l2 != 0) l1 / l2 else Long.MinValue,
      if (h2 != 0) l1 / h2 else Long.MinValue,
      if (l2 != 0) h1 / l2 else Long.MinValue,
      if (h2 != 0) h1 / h2 else Long.MinValue
    )
    fromBounds(quotients.min, quotients.max)
  }

  /** Abstract equality: precise B1 if same, else Any */
  def eqq(a: Element, b: Element): Element = if (a == b) B1 else B0

  /** Abstract greater-than: precise B1 if lower bound of a > upper of b, B0 if upper of a <= lower of b, else Any */
  def gt(a: Element, b: Element): Element = {
    val (_, hB) = bounds(b); val (lA, _) = bounds(a)
    if (lA > hB) B1
    else if (bounds(a)._2 <= bounds(b)._1) B0
    else Any
  }
}
