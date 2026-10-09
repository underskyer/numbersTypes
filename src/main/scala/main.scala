import numberTypes.*

@main
def main() =

  given commutation: [A, B] => (A × B) ~ (B × A) = (
    to   = (a, b) => (b, a),
    from = (b, a) => (a, b),
  )

  def func(strInt: String × Int) = s"${strInt._1}: ${strInt._2}"

  import Iso.given

  val a: Int × String = 42 -> "jndtn"
  //println(func(a))

  type Magma[A] = A + Magma[A] × Magma[A]

  enum Number[A]:
    case Zero(a: A)
    case Sum (left: Number[A], right: Number[A])
    case Prod(left: Number[A], right: Number[A])

  def add[A](a1: Magma[A], a2: Magma[A]): Magma[A] =
    Right((a1, a2))

  //given intStr: Int =:= String =

  //println(summon[Int =:= Int] == summon[String =:= String])

  natural.test
  recNatural.test
  chirchNatural.test
  indNatural.test
  wellFounded.test
