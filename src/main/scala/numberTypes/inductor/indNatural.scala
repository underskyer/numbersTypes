package numberTypes.inductor

import numberTypes.*
import numberTypes.sigmaTypes.Σɢᴀᴅᴛ


object indNatural:



  type NatFamily[+Prev] = [B] =>> B match
    case false => Zero.type
    case true  => Succ[Prev]

  type NatFunctor[Prev] = Σɢᴀᴅᴛ[Bool, NatFamily[Prev]]
  type ZeroΣ = Σɢᴀᴅᴛ.In[Bool, NatFamily[Nat], false]
  type SuccΣ = Σɢᴀᴅᴛ.In[Bool, NatFamily[Nat], true]


  type Nat = μᵢ[NatFunctor]
  type NatZero =           μᵢ.In[NatFunctor, ZeroΣ]
  type NatSucc[P <: Nat] = μᵢ.In[NatFunctor, SuccΣ]

  val zero: NatZero = μᵢ.In(Σɢᴀᴅᴛ.In[Bool, NatFamily[Nat], false](false, Zero))

  def succ[N <: Nat](n: N): Nat =
    μᵢ.In[NatFunctor, SuccΣ](
      Σɢᴀᴅᴛ.In[Bool, NatFamily[Nat], true](true, Succ(n))
    )

  //type IndexedNatNext[P[_ <: NatIdx]] = [I <: NatIdx] => (prev: Nat[I], prevP: P[I]) => P[SuccIdx[I]]
  type NatInductor = [C[_ <: Nat]]
    => C[NatZero] => ((p: Nat) => C[p.type ] => C[Nat])
    => (n: Nat) => C[n.type]


  def ind[C[_ <: Nat]](
    default: C[zero.type],
    next: (p: Nat) => C[p.type] => C[Nat]
  )(n: Nat): C[n.type] = n match
      case μᵢ.In(Σɢᴀᴅᴛ.In(false, _   )) => default.asInstanceOf[C[n.type]]
      case μᵢ.In(Σɢᴀᴅᴛ.In(true, value)) =>
        val p = value.asInstanceOf[Succ[Nat]].prev
        next(p)(ind[C](default, next)(p)).asInstanceOf[C[n.type]]

  def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("                НАТУРАЛЬНАЯ ИНДУКЦИЯ              ")
    println("==================================================")

    private type FactState = (Long, Long)

    private val factStateRec: Nat => FactState = rec[FactState](
      (0L, 1L),
      _ => pair =>
          val (currentLong, currentFact) = pair
          val nextLong = currentLong + 1L
          (nextLong, currentFact * nextLong)
    )

    val factorial: Nat => Long = n => factStateRec(n)._2

    val five = succ(succ(succ(succ(succ(zero)))))
    println(s"индуктивный факториал: ${factorial(five)}")



    type TupleFamily[I <: Nat] <: Tuple = I match
      case NatZero    => EmptyTuple
      case NatSucc[p] => Int *: TupleFamily[p]

    val myInductor = ind[TupleFamily](
      default = EmptyTuple,
      next = prev => prevP => (42 *: prevP).asInstanceOf[TupleFamily[Nat]]
    )

    val n0 = zero
    val n1 = succ(n0)
    val n2 = succ(n1)

    val r0 = myInductor(n0)
    val r1 = myInductor(n1)
    val r2 = myInductor(n2)

    println(s"r0 = $r0") // EmptyTuple
    println(s"r1 = $r1") // (42)
    println(s"r2 = $r2") // (42, 42)
    println("==================================================")
