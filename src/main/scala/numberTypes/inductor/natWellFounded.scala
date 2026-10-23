package numberTypes.inductor

import numberTypes.*
import numberTypes.piTypes.ℿ
import numberTypes.sigmaTypes.{InΣ, ⅀}
import numberTypes.wellFounded.*

object natWellFounded:

  type NatArity[I <: 𝔹] = I match
    case false => Nothing
    case true  => Unit
  type ℕ = 𝕎[𝔹, NatArity]

  type NatZero         = μᵢ.In[ℙ[𝔹, NatArity], InΣ[𝔹, Brn[𝔹, NatArity, Nothing], false]]
  type NatSucc[N <: ℕ] = μᵢ.In[ℙ[𝔹, NatArity], InΣ[𝔹, Brn[𝔹, NatArity, N      ], true ]]

  // todo не работает!!
  type NatPrev[N <: ℕ] <: ℕ = N match
    case NatZero => Nothing
    case μᵢ.In[ℙ[𝔹, NatArity], InΣ[𝔹, Brn[𝔹, NatArity, p], true]] => p & ℕ

  object ℕ:
    val zero:               NatZero    = 𝕎.sup[𝔹, NatArity, Nothing](false, identity[Nothing])
    def succ[N <: ℕ](n: N): NatSucc[N] = 𝕎.sup[𝔹, NatArity, N](true, _ => n)

    def ind[R[_ <: ℕ]](
      default: R[NatZero],
      next: (w: ℕ) => (p: ℕ) => R[p.type] => R[w.type]
    ): ℿ[ℕ, R] = 𝕎.ind1[𝔹, NatArity, R]: w =>
      case InΣ(false, _) => _ => default.asInstanceOf[R[w.type]]
      case InΣ(true, branches: Brn[𝔹, NatArity, ℕ][true])  =>
        val pred = branches(())
        ih => next(w)(pred)(ih(pred)).asInstanceOf[R[w.type]]


    def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("         ФУНДИРОВАННЫЕ НАТУРАЛЬНЫЕ ЧИСЛА          ")
    println("==================================================")

    type TupleFamily[I <: ℕ] <: Tuple = I match
//      case μᵢ.In[
//        _,
//        ⅀.InΣ[𝔹, [i <: 𝔹] =>> Nothing => Nothing, false]
//      ] => EmptyTuple
//      case μᵢ.In[
//        _,
//        ⅀.InΣ[𝔹, [i <: 𝔹] =>> Unit => p, true]
//      ] => Int *: TupleFamily[p]
//      case μᵢ.In[
//        pp, 
//        InΣ[𝔹, [J <: 𝔹] =>> (i: J) => NatArity[i.type] => Nothing, false]
//      ] => EmptyTuple
//      case μᵢ.In[
//        pp,//ℙ[𝔹, NatArity],
//        InΣ[𝔹, [J <: 𝔹] =>> (i: J) => NatArity[i.type] => p      , true ]
//      ] => Int *: TupleFamily[p]
      case NatZero => EmptyTuple
      case NatSucc[p] => Int *: TupleFamily[p]


    val myInductor = ℕ.ind[TupleFamily](
      default = EmptyTuple,
      next = w => p => prevP => (42 *: prevP).asInstanceOf[TupleFamily[w.type]]
    )

    val n0 = ℕ.zero
    val n1 = ℕ.succ(n0)
    val n2: NatSucc[NatSucc[NatZero]] = ℕ.succ(n1)

    summon[NatSucc[NatZero] <:< ℕ]
    summon[NatSucc[NatSucc[NatZero]] <:< ℕ]

//    val r0 = myInductor(n0)
//    val r1 = myInductor(n1: ℕ)
//    val r2 = myInductor(n2: ℕ)
//
//    println(s"r0 = $r0") // EmptyTuple
//    println(s"r1 = $r1") // (42)
//    println(s"r2 = $r2") // (42, 42)

    println("--------------------------------------------------")

    // ===== Числа Фибоначчи =====
    // Состояние: (fib(k), fib(k+1), накопленный кортеж длины k)
    type FibState[N <: ℕ] = (Int, Int, TupleFamily[N])

    val fibInductor = ℕ.ind[FibState](
      default = (0, 1, EmptyTuple),
      next = w => prev =>
        case (a, b, tup) => (b, a + b, (b *: tup).asInstanceOf[TupleFamily[w.type]])
    )

    // Печать кортежа в естественном порядке (разворачиваем накопленный)
    def showTupleNatural(t: Tuple): String =
      t.productIterator.toList.reverse.mkString("(", ", ", ")")

    val n3 = ℕ.succ(n2)
    val n4 = ℕ.succ(n3)
    val n5 = ℕ.succ(n4)
    val n6 = ℕ.succ(n5)

    println("--- Числа Фибоначчи ---")
    println(s"f0 = ${showTupleNatural(fibInductor(n0)._3)}") // ()
    println(s"f1 = ${showTupleNatural(fibInductor(n1)._3)}") // (1)
    println(s"f2 = ${showTupleNatural(fibInductor(n2: ℕ)._3)}") // (1, 1)
    println(s"f3 = ${showTupleNatural(fibInductor(n3: ℕ)._3)}") // (1, 1, 2)
    println(s"f4 = ${showTupleNatural(fibInductor(n4: ℕ)._3)}") // (1, 1, 2, 3)
    println(s"f5 = ${showTupleNatural(fibInductor(n5: ℕ)._3)}") // (1, 1, 2, 3, 5)
    println(s"f6 = ${showTupleNatural(fibInductor(n6: ℕ)._3)}") // (1, 1, 2, 3, 5, 8)

    println("==================================================")

  end test