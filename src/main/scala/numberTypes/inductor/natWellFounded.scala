package numberTypes.inductor

import numberTypes.*
import numberTypes.sigmaTypes.Σɢᴀᴅᴛ
import numberTypes.wellFounded.*

object natWellFounded:

  type NatArity[A <: Bool] = A match
    case false => Nothing
    case true  => Unit
  type Nat = W[Bool, NatArity]

  type NatZero           = μᵢ.In[PolynomialFunctor[Bool, NatArity], Σɢᴀᴅᴛ.In[Bool, Branches[Bool, NatArity, Nothing], false]]
  type NatSucc[N <: Nat] = μᵢ.In[PolynomialFunctor[Bool, NatArity], Σɢᴀᴅᴛ.In[Bool, Branches[Bool, NatArity, N      ], true ]]

  // todo не работает!!
  type NatPrev[N <: Nat] <: Nat = N match
    case NatZero => Nothing
    case μᵢ.In[PolynomialFunctor[Bool, NatArity], Σɢᴀᴅᴛ.In[Bool, Branches[Bool, NatArity, p], true]] => p & Nat

  object Nat:
    val zero: NatZero = W.sup[Bool, NatArity, Nothing, false](false, _ => identity[Nothing])
    def succ[N <: Nat](n: N): NatSucc[N] = W.sup[Bool, NatArity, N, true ](true, _ => _ => n)

    def ind[C[_ <: Nat]](
      default: C[NatZero],
      next: (p: Nat) => C[p.type] => C[Nat]
    ): (n: Nat) => C[n.type] = W.ind[Bool, NatArity, C](
      [I <: Bool] => i => branches => ih => i match
        case false => default.asInstanceOf[C[Nat]]
        case true  =>
          val pred = branches(i)(().asInstanceOf[NatArity[i.type]])
          val predIH = ih(pred)
          next(pred)(predIH)
    )

    def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("         ФУНДИРОВАННЫЕ НАТУРАЛЬНЫЕ ЧИСЛА          ")
    println("==================================================")

    type TupleFamily[I <: Nat] <: Tuple = I match
      case NatZero => EmptyTuple
      case NatSucc[p] => Int *: TupleFamily[p]

    // рабочий индуктор!!
    def myInductor1 = W.ind[Bool, NatArity, TupleFamily](
      [I <: Bool] => b => branches => ih => b match
        //case false => EmptyTuple
        //case true  => 42 *: ih(branches(b)(()))
        case false => EmptyTuple.asInstanceOf[TupleFamily[Nat]]
        case true  =>
          val prevNat = branches(b)(().asInstanceOf[NatArity[b.type]])
          val prevP = ih(prevNat)
          (42 *: prevP).asInstanceOf[TupleFamily[Nat]]
    ).asInstanceOf[(n: Nat) => TupleFamily[n.type]]

    val myInductor = Nat.ind[TupleFamily](
      default = EmptyTuple,
      next = prev => prevP => (42 *: prevP).asInstanceOf[TupleFamily[Nat]]
    )

    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2: NatSucc[NatSucc[NatZero]] = Nat.succ(n1)

    summon[NatSucc[NatZero] <:< Nat]
    summon[NatSucc[NatSucc[NatZero]] <:< Nat]
    summon[NatSucc[NatSucc[NatZero]] <:< Nat]

    val r0 = myInductor(n0)
    val r1 = myInductor(n1: Nat)
    val r2 = myInductor(n2: Nat)

    println(s"r0 = $r0") // EmptyTuple
    println(s"r1 = $r1") // (42)
    println(s"r2 = $r2") // (42, 42)

    println("--------------------------------------------------")

    // ===== Числа Фибоначчи =====
    // Состояние: (fib(k), fib(k+1), накопленный кортеж длины k)
    type FibState[N <: Nat] = (Int, Int, TupleFamily[N])

    val fibInductor = Nat.ind[FibState](
      default = (0, 1, EmptyTuple),
      next = prev => prevState =>
        val a = prevState._1 // fib(k)
        val b = prevState._2 // fib(k+1)
        val tup = prevState._3 // кортеж длины k (в обратном порядке)
        // следующий шаг: (fib(k+1), fib(k)+fib(k+1), fib(k+1) *: tup)
        (b, a + b, (b *: tup).asInstanceOf[TupleFamily[Nat]])
    )

    // Печать кортежа в естественном порядке (разворачиваем накопленный)
    def showTupleNatural(t: Tuple): String =
      t.productIterator.toList.reverse.mkString("(", ", ", ")")

    val n3 = Nat.succ(n2)
    val n4 = Nat.succ(n3)
    val n5 = Nat.succ(n4)
    val n6 = Nat.succ(n5)

    println("--- Числа Фибоначчи ---")
    println(s"f0 = ${showTupleNatural(fibInductor(n0)._3)}") // ()
    println(s"f1 = ${showTupleNatural(fibInductor(n1)._3)}") // (1)
    println(s"f2 = ${showTupleNatural(fibInductor(n2: Nat)._3)}") // (1, 1)
    println(s"f3 = ${showTupleNatural(fibInductor(n3: Nat)._3)}") // (1, 1, 2)
    println(s"f4 = ${showTupleNatural(fibInductor(n4: Nat)._3)}") // (1, 1, 2, 3)
    println(s"f5 = ${showTupleNatural(fibInductor(n5: Nat)._3)}") // (1, 1, 2, 3, 5)
    println(s"f6 = ${showTupleNatural(fibInductor(n6: Nat)._3)}") // (1, 1, 2, 3, 5, 8)

    println("==================================================")

  end test