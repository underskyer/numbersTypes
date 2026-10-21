package numberTypes.inductor

import numberTypes.*
import numberTypes.piTypes.ℿ


object natInductor:

  object Zero
  type Zero = Zero.type
  final case class Succ[+P](prev: P)

  type NatFunctor[+Prev] = Zero + Succ[Prev]

  type Nat = μᵢ[NatFunctor]
  type NatZero =           μᵢ.In[NatFunctor, Left [Zero,    Nothing]]
  type NatSucc[N <: Nat] = μᵢ.In[NatFunctor, Right[Nothing, Succ[N]]]

  val zero: NatZero =                    μᵢ.In[NatFunctor, Left [Zero,    Nothing]](Left(Zero))
  def succ[N <: Nat](n: N): NatSucc[N] = μᵢ.In[NatFunctor, Right[Nothing, Succ[N]]](Right(Succ(n)))

  // ℿ[Nat <: Nat, [X] =>> R[X] => R[NatSucc[X]]]
  type NatInductor = [R[_ <: Nat]]
    => R[NatZero] => ((p: Nat) => R[p.type] => R[NatSucc[p.type]]) // зависимая алгебра
    => ℿ[Nat, R]

  val ind: NatInductor =
    [R[_ <: Nat]] => default => next => n => n match
      case μᵢ.In(Left(_)) => default.asInstanceOf[R[n.type]]
      case μᵢ.In(Right(value)) =>
        val p = value.asInstanceOf[Succ[Nat]].prev
        next(p)(ind(default)(next)(p)).asInstanceOf[R[n.type]]

  def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("          ПРОСТАЯ НАТУРАЛЬНАЯ ИНДУКЦИЯ            ")
    println("==================================================")

    type FactState = (Long, Long)

    val factStateRec = rec[FactState]((0L, 1L))(
      n => (pair: FactState) =>
        val (currentLong, currentFact) = pair
        val nextLong = currentLong + 1L
        (nextLong, currentFact * nextLong)
    )

    val factorial: Nat => Long = n => factStateRec(n)._2

    val five = succ(succ(succ(succ(succ(zero)))))
    println(s"индуктивный факториал: ${factorial(five)}")



    type TupleFamily[N <: Nat] <: Tuple = N match
      case μᵢ.In[NatFunctor, Left [Zero,    Nothing]] => EmptyTuple
      case μᵢ.In[NatFunctor, Right[Nothing, Succ[p]]] => Int *: TupleFamily[p]
//      case NatZero    => EmptyTuple
//      case NatSucc[p] => Int *: TupleFamily[p]

    // : (n: Nat) => TupleFamily[n.type]
    val cloneTheAnswer: ℿ[Nat, TupleFamily] =
      ind[TupleFamily](EmptyTuple)(_ => prevP => 42 *: prevP)

    val n1 = succ(zero)
    val n2 = succ(n1)
    val n3 = succ(succ(succ(zero)))

    summon[NatZero <:< Nat]
    summon[NatSucc[NatZero] <:< Nat]

    val r0: EmptyTuple  = cloneTheAnswer(zero)
    val r1: Tuple1[Int] = cloneTheAnswer(n1)
    val r2: (Int, Int)  = cloneTheAnswer(n2)

    println(s"r0 = $r0") // EmptyTuple
    println(s"r1 = $r1") // (42)
    println(s"r2 = $r2") // (42, 42)
    println(s"r3 = ${cloneTheAnswer(n3)}") // (42, 42, 42)
    println("==================================================")
