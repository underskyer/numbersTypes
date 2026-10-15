package numberTypes

object natSigma:

  // ============================================================================
  // 1. Индексы и Зависимый Сигма-тип
  // ============================================================================

  enum NatIdx:
    case ZeroIdx extends NatIdx
    case SuccIdx[I <: NatIdx]() extends NatIdx

  import NatIdx.{ZeroIdx, SuccIdx}
  type ZeroIdx = ZeroIdx.type

  type Bool = Boolean & Singleton

  trait Sigma[IndexType, TypeFamily[_ <: IndexType]]:
    type Tag <: IndexType
    val tag: Tag
    val value: TypeFamily[Tag]

  object Sigma:
    def apply[IndexType, TypeFamily[_ <: IndexType], T <: IndexType](t: T, v: TypeFamily[T]): Sigma[IndexType, TypeFamily] { type Tag = T } =
      new Sigma[IndexType, TypeFamily]:
        type Tag = T
        val tag: T = t
        val value: TypeFamily[T] = v

  // ============================================================================
  // 2. Индексированная Неподвижная Точка
  // ============================================================================

  case class Mu[IndType, F[Self[_ <: IndType], _ <: IndType], I <: IndType](
    unfix: F[[X <: IndType] =>> Mu[IndType, F, X], I]
  )

  type μ[IndType] = [F[Self[_ <: IndType], _ <: IndType]] =>> [I <: IndType] =>> Mu[IndType, F, I]

  // ============================================================================
  // 3. Чистый Натуральный Тип без ООП-надстроек (NatFunctor & NatTerm API)
  // ============================================================================

  // Переименовали R в NextLayer для понятности структуры
  type NatFamily[NextLayer[_ <: NatIdx], I <: NatIdx] = [b <: Bool] =>> b match
    case true  => Unit
    case false => NextLayer[I]

  // Переименовали NatForm в NatFunctor
  type NatFunctor[NextLayer[_ <: NatIdx], O <: NatIdx] = Sigma[Bool, [b <: Bool] =>>
    NatFamily[NextLayer, O match
      case ZeroIdx => ZeroIdx
      case SuccIdx[prev] => prev
    ][b]
  ]

  type Nat = μ[NatIdx][NatFunctor]

  object Nat:
    def zero: Nat[ZeroIdx] =
      Mu[NatIdx, NatFunctor, ZeroIdx](
        Sigma[Bool, [b <: Bool] =>> NatFamily[Nat, ZeroIdx][b], true](true, ())
          .asInstanceOf[Sigma[Bool, [b <: Bool] =>> NatFamily[Nat, ZeroIdx][b]]]
      )

    def succ[I <: NatIdx](n: Nat[I]): Nat[SuccIdx[I]] =
      Mu[NatIdx, NatFunctor, SuccIdx[I]](
        Sigma[Bool, [b <: Bool] =>> NatFamily[Nat, I][b], false](false, n)
          .asInstanceOf[Sigma[Bool, [b <: Bool] =>> NatFamily[Nat, I][b]]]
      )
  end Nat

  // ============================================================================
  // 4. Зависимый Элиминатор (Индуктор) работает напрямую с NatTerm
  // ============================================================================

  def ind[P[_ <: NatIdx]](
    vZero: P[ZeroIdx],
    vSucc: [I <: NatIdx] => (prev: Nat[I], prevP: P[I]) => P[SuccIdx[I]]
  ): [I <: NatIdx] => (n: Nat[I]) => P[I] =
    [I <: NatIdx] => (n: Nat[I]) =>
      def loop[K <: NatIdx](m: Nat[K]): P[K] = m.unfix.tag match
        case _: true => vZero.asInstanceOf[P[K]]
        case _: false =>
          val prevTerm = m.unfix.value.asInstanceOf[Nat[NatIdx]]
          val prevP = loop(prevTerm)
          vSucc(prevTerm, prevP).asInstanceOf[P[K]]
      loop(n)

  // ============================================================================
  // 5. Наглядный тест
  // ============================================================================

  object test:
    type TupleFamily[I <: NatIdx] <: Tuple = I match
      case ZeroIdx => EmptyTuple
      case SuccIdx[prev] => Int *: TupleFamily[prev]

    val myInductorBase = ind[TupleFamily](
      vZero = EmptyTuple,
      vSucc = [I <: NatIdx] => (prev: Nat[I], prevP: TupleFamily[I]) =>
        (42 *: prevP).asInstanceOf[TupleFamily[SuccIdx[I]]]
    )

    // Принимает чистый NatTerm[I] и возвращает зависимый TupleFamily[I]
    inline def myInductor[I <: NatIdx](n: Nat[I]): TupleFamily[I] =
      myInductorBase[I](n)

    // Конструируем термы напрямую через фабрику NatTerm
    val n0 = Nat.zero
    val n1 = Nat.succ(n0)
    val n2 = Nat.succ(n1)

    val r0: EmptyTuple = myInductor(n0)
    val r1: Int *: EmptyTuple = myInductor(n1)
    val r2: Int *: Int *: EmptyTuple = myInductor(n2)

    println("==================================================")
    println("ЗАПУСК: Чистый NatTerm API без лишних Трейтов")
    println("==================================================")
    println(s"Аргумент n0 (Zero)             -> Результат r0: $r0")
    println(s"Аргумент n1 (Succ(Zero))       -> Результат r1: $r1")
    println(s"Аргумент n2 (Succ(Succ(Zero))) -> Результат r2: $r2")
    println("==================================================")

