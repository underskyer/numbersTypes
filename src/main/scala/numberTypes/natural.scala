package numberTypes

import com.sun.net.httpserver.Authenticator.Success

object natural:
  enum Nat:                          // formation
    case Zero            extends Nat // introduction (1-й конструктор)
    case Succ(prev: Nat) extends Nat // introduction (2-й конструктор)

  val rec: [C] => (C, Nat => C => C) => Nat => C = // elimination
    [C] => (z, succ) =>                            // computation
      case Nat.Zero    => z
      case Nat.Succ(p) => succ(p)(rec(z, succ)(p))

  object test:

    type FactState = (index: Int, result: Long)

    val factorial = rec[FactState](
      (index = 0, result = 1L),
      _ => (currentLong, currentFact) =>
        val nextLong = currentLong + 1
        (nextLong, currentFact * nextLong)
    ).andThen(_.result)

    import Nat.*
    val five: Nat = Succ(Succ(Succ(Succ(Succ(Zero)))))

    println("натуральный факториал: " + factorial(five))
