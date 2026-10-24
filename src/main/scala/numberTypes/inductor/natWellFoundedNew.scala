package numberTypes.inductor

import numberTypes.*
import numberTypes.piTypes.ℿ
import numberTypes.wellFoundedNew.*

object natWellFoundedNew:

  type NatArity[I <: 𝔹] = I match
    case false => Nothing
    case true  => Unit
  type ℕ = 𝕎[𝔹, NatArity]

  type NatZero         = 𝕎.sup[𝔹, NatArity, false, Nothing]
  type NatSucc[P <: ℕ] = 𝕎.sup[𝔹, NatArity, true, P]

//  // todo не работает!!
//  type NatPrev[N <: ℕ] <: ℕ = N match
//    case NatZero => Nothing
//    case μᵢ.In[ℙ[𝔹, NatArity], InΣ[𝔹, Brn[𝔹, NatArity, p], true]] => p & ℕ

  object ℕ:
    val zero:               NatZero    = 𝕎.sup[𝔹, NatArity, false, Nothing](false, identity[Nothing])
    def succ[P <: ℕ](p: P): NatSucc[P] = 𝕎.sup[𝔹, NatArity,  true, P      ](true, _ => p)

    def ind[R[_ <: ℕ]](
      default: R[NatZero],
      next: [P <: ℕ] => (p: P) => R[P] => R[NatSucc[P]]
    ): ℿ[ℕ, R] =
      𝕎.ind[𝔹, NatArity, R](
        [J <: 𝔹] => (w: ℕ) =>
          case false => _ => _ => default.asInstanceOf[R[w.type]]
          case true => subtrees => ih =>
            val p: ℕ = subtrees.asInstanceOf[Unit => ℕ](())
            // w = sup(true, s), p = s(()). R[NatSucc[p.type]] и R[w.type]
            // описывают одно и то же натуральное число, но интенсионально
            // — разные типы.
            next(p)(ih(p)).asInstanceOf[R[w.type]]

      )

    def indw[R[_ <: ℕ]](
      default: R[NatZero],
      next: (w: ℕ) => (p: ℕ) => R[p.type] => R[w.type]
    ): ℿ[ℕ, R] = 𝕎.ind[𝔹, NatArity, R](
      [J <: 𝔹] => w => i => s => ih =>
        if i.asInstanceOf[Boolean] then
          val p = s.asInstanceOf[Unit => ℕ](())
          next(w)(p)(ih(p))
        else default.asInstanceOf[R[w.type]]
    )

    def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("         ФУНДИРОВАННЫЕ НАТУРАЛЬНЫЕ ЧИСЛА          ")
    println("==================================================")

    type TupleFamily[I <: ℕ] <: Tuple = I match
      case 𝕎.sup[𝔹, NatArity, false, Nothing] => EmptyTuple
      case 𝕎.sup[𝔹, NatArity, true, p] => Int *: TupleFamily[p]


    val n0 = ℕ.zero
    val n1 = ℕ.succ(n0)
    val n2: NatSucc[NatSucc[NatZero]] = ℕ.succ(n1)

    summon[NatSucc[NatZero] <:< ℕ]
    summon[NatSucc[NatSucc[NatZero]] <:< ℕ]

    // ===== Числа Фибоначчи =====
    // Состояние: (fib(k), fib(k+1), накопленный кортеж длины k)
    type FibState[N <: ℕ] = (Int, Int, TupleFamily[N])

    val fibInductor = ℕ.ind[FibState](
      default = (0, 1, EmptyTuple),
      next = [_ <: ℕ] => prev =>
        case (a, b, tup) => (b, a + b, b *: tup)
    )
//    val fibInductor = ℕ.indw[FibState](
//      default = (0, 1, EmptyTuple),
//      next = w => prev =>
//        case (a, b, tup) => (b, a + b, (b *: tup).asInstanceOf[TupleFamily[w.type]])
//    )

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