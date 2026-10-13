package numberTypes

import numberTypes.sigmaPi.*

object indNatural:
  
  type Bool = Boolean & Singleton

  type NatFamily[Prev] = [B] =>> B match
    case false  => Zero
    case true => Succ[Prev]

  type NatFunctor[Prev] = ∑[NatFamily[Prev]]

  type Nat = Fix[NatFunctor]

  val zero: Nat =
    Fix(in[NatFamily[Nat], false](Zero))

  def succ(n: Nat): Nat =
    Fix(in[NatFamily[Nat], true](Succ(n)))

  def ind[C[_ <: Nat]](
    default: C[zero.type],
    next: (p: Nat) => C[p.type] => C[Nat]//Succ[p.type]]
  )(n: Nat): C[n.type] =
    (n.unfix: @unchecked) match
      case ∑.In(_, tag: false) =>
        default.asInstanceOf[C[n.type]]
  
      case ∑.In(value, tag: true) =>
        val p = value.asInstanceOf[Succ[Nat]].prev
        next(p)(ind[C](default, next)(p)).asInstanceOf[C[n.type]]
      
  def rec[C] = ind[Const[C]]

  object test:

    val z: NatFamily[Nothing][false]  = Zero
    val one:  NatFamily[Zero][true ]  = Succ(Zero)
    //val str:  NatFamily[Bool][Zero]   = "Succ(Zero)"

    summon[true <:< Bool]
    summon[false <:< Bool]
    //summon[Singleton <:< Bool]

    private type FactState = (Long, Long)

    // 2. Оптимизированный рекурсор факториала со сложностью O(n)
    private val factStateRec: Nat => FactState = rec[FactState](
      (0L, 1L), // Для нуля: число = 0L, 0! = 1L
      _ => {
        case (currentLong, currentFact) =>
          val nextLong = currentLong + 1L
          val nextFact = currentFact * nextLong
          (nextLong, nextFact)
      }
    )

    // 3. Финальная функция вычисления факториала
    val factorial: Nat => Long = n => factStateRec(n)._2

    val five: Nat = succ(succ(succ(succ(succ(zero)))))
    println(s"индуктивный факториал: ${factorial(five)}")
