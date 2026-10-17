package numberTypes.inductor

import numberTypes.sigmaTypes.*
import numberTypes.*

object indNatural:
  
  type NatFamily[Prev] = [B] =>> B match
    case false => Zero
    case true  => Succ[Prev]

  type NatFunctor[Prev] = Σɢᴀᴅᴛ[Bool, NatFamily[Prev]]

  type Nat = Fix[NatFunctor]

  type Z = Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], false]
  type S = Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true]

  val zero: Nat =
    Fix(Σin[Bool, NatFamily[Nat], false](Zero))

  def succ(n: Nat): Nat =
    Fix(Σin[Bool, NatFamily[Nat], true](Succ(n)))

  def ind[C[+_ <: Nat]](
    default: C[zero.type],
    next: (p: Nat) => C[p.type] => C[Nat]
  )(n: Nat): C[n.type] =
    (n.unfix: @unchecked) match
      case Σɢᴀᴅᴛ.ΣIn(false, _   ) => default.asInstanceOf[C[n.type]]
      case Σɢᴀᴅᴛ.ΣIn(true, value) =>
        val p = value.asInstanceOf[Succ[Nat]].prev
        next(p)(ind[C](default, next)(p)).asInstanceOf[C[n.type]]

  
  def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("                НАТРУАЛЬНАЯ ИНДУКЦИЯ              ")
    println("==================================================")

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


    type TupleFamily[I <: Nat] <: Tuple = I match
      case Zero.type => EmptyTuple
      case Succ[prev] => Int *: TupleFamily[prev]

    // не работает!!
//    val myInductor = ind[TupleFamily](
//      default = EmptyTuple,
//      next = (prev: Nat, prevP: TupleFamily[prev.type]) =>
//        (42 *: prevP).asInstanceOf[TupleFamily[Succ[prev.type]]]
//    )
//    
//    val n0: Nat = zero
//    val n1: Nat = succ(n0)
//    val n2: Nat = succ(n1)
//    
//    val r0 = myInductor(n0)
//    val r1 = myInductor(n1)
//    val r2 = myInductor(n2)
//    
//    println(s"r0 = $r0")
//    println(s"r1 = $r1")
//    println(s"r2 = $r2")
    println("==================================================")
