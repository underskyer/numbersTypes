package numberTypes.inductor

// Эмуляция внешних импортов для автономности примера
object DummyImports:
  type Bool = Boolean
  object Zero
  case class Succ[+P](prev: P)
  type Const[A] = [X] =>> A

import DummyImports.*

object indNatural:

  enum Fix1[F[_]]:
    case InFIx[G[_], V <: G[Fix1[G]]](unfix: V) extends Fix1[G]

  enum Σɢᴀᴅᴛ[IndexType, G[_ <: IndexType]]:
    case ΣIn[I, F[_ <: I], i <: I](index: i, fi: F[i]) extends Σɢᴀᴅᴛ[I, F]

  type NatFamily[+Prev] = [B] =>> B match
    case false => Zero.type
    case true  => Succ[Prev]

  type NatFunctor[Prev] = Σɢᴀᴅᴛ[Bool, NatFamily[Prev]]

  type Nat = Fix1[NatFunctor]

  // Алиас для типа "следующее число" на уровне типов, чтобы Match Type мог его разобрать
  type SuccNat[P <: Nat] = Fix1.InFIx[NatFunctor, Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true]]

  val zero: Nat =
    Fix1.InFIx[NatFunctor, Σɢᴀᴅᴛ[Bool, NatFamily[Nat]]](
      Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], false](false, Zero)
    )

  // Улучшаем сигнатуру типа возвращаемого значения, чтобы сохранить информацию о типе N
  def succ[N <: Nat](n: N): Fix1.InFIx[NatFunctor, Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true]] =
    Fix1.InFIx[NatFunctor, Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true]](
      Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true](true, Succ(n))
    )

  // Исправлена сигнатура: next теперь возвращает C[Nat] (или более точный тип),
  // а внутренняя логика приведена в соответствие с каррированием.
  def ind[C[_ <: Nat]](
    default: C[zero.type],
    next: (p: Nat) => C[p.type] => C[Nat]
  )(n: Nat): C[n.type] =
    n match
      case Fix1.InFIx(Σɢᴀᴅᴛ.ΣIn(false, _   )) => default.asInstanceOf[C[n.type]]
      case Fix1.InFIx(Σɢᴀᴅᴛ.ΣIn(true, value)) =>
        val p = value.asInstanceOf[Succ[Nat]].prev
        // Вызываем каррированную функцию next
        next(p)(ind[C](default, next)(p)).asInstanceOf[C[n.type]]

  def rec[C] = ind[Const[C]]

  object test:

    println("==================================================")
    println("                НАТУРАЛЬНАЯ ИНДУКЦИЯ              ")
    println("==================================================")

    private type FactState = (Long, Long)

    private val factStateRec: Nat => FactState = rec[FactState](
      (0L, 1L),
      p => state => {
        val (currentLong, currentFact) = state
        val nextLong = currentLong + 1L
        val nextFact = currentFact * nextLong
        (nextLong, nextFact)
      }
    )

    val factorial: Nat => Long = n => factStateRec(n)._2

    val five = succ(succ(succ(succ(succ(zero)))))
    println(s"индуктивный факториал: ${factorial(five)}")

    // ИСПРАВЛЕННЫЙ MATCH TYPE:
    // Вместо разбора внутренних внутренностей GADT, мы проверяем,
    // является ли тип синглтоном нуля, либо "разворачиваем" его структуру.
    type TupleFamily[I <: Nat] <: Tuple = I match
      case zero.type => EmptyTuple
      // Если это тип, возвращенный функцией succ, мы можем безопасно извлечь его составные части
      case Fix1.InFIx[NatFunctor, Σɢᴀᴅᴛ.ΣIn[Bool, NatFamily[Nat], true]] =>
        Int *: TupleFamily[Nat]

    // ИСПРАВЛЕННЫЙ ВЫЗОВ: Применяем каррирование в `next` (p => prevP => ...)
    val myInductor = ind[TupleFamily](
      default = EmptyTuple,
      next = (prev: Nat) => (prevP: TupleFamily[prev.type]) =>
        (42 *: prevP).asInstanceOf[TupleFamily[Nat]]
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
