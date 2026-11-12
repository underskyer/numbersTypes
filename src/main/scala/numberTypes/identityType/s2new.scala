package numberTypes.identityType

object s2new:

  // ===== Path-инфраструктура (та же, что у S¹) =====
  sealed trait Path[A, X <: A, Y <: A]
  object Path:
    final case class Refl[A, X <: A]() extends Path[A, X, X]
    final case class Sym[A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P) extends Path[A, Y, X]
    final case class Trans[A, X <: A, Y <: A, Z <: A,
      P <: Path[A, X, Y], Q <: Path[A, Y, Z]](p: P, q: Q)
      extends Path[A, X, Z]

  extension [A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P)
    def inverse: Path.Sym[A, X, Y, P] = Path.Sym(p)
    def andThen[Z <: A, Q <: Path[A, Y, Z]](q: Q): Path.Trans[A, X, Y, Z, P, Q] =
      Path.Trans(p, q)

  /** 2-клетка (2-путь) при значении V в слое L:
   * это путь между двумя «рефлексивностями» refl_V, т.е. элемент Ω²(L, V).
   */
  type Coherence2[L, V <: L] =
    Path[Path[L, V, V], Path.Refl[L, V], Path.Refl[L, V]]

  // =====================================================================
  // S²: HIT с точкой Base и 2-клеткой Surf : refl_Base = refl_Base
  // =====================================================================
  sealed trait S2:
    def ind[P[_ <: S2]](b: P[S2.Base.type])(
      s: Coherence2[P[S2.Base.type], b.type]
    ): P[this.type]

  object S2:
    case object Base extends S2:
      def ind[P[_ <: S2]](b: P[Base.type])(
        s: Coherence2[P[Base.type], b.type]
      ): P[this.type] = b

    /** 2-клетка surf: refl_Base = refl_Base. */
    case object Surf extends Path[
      Path[S2, Base.type, Base.type],
      Path.Refl[S2, Base.type],
      Path.Refl[S2, Base.type]
    ]

    // ---- Сечение зависимого мотива P : S² → Type ----
    trait Section[P[_ <: S2]]:
      type BaseValue <: P[Base.type] & Singleton
      val baseValue: BaseValue
      def apply(x: S2): P[x.type]
      /** apd(section) вдоль Surf — 2-клетка в слое над Base. */
      def surfCoherence: Coherence2[P[Base.type], baseValue.type]

    // ---- Зависимый индуктор S² ----
    // Для мотива P : S² → Type нужно задать:
    //   • b : P(Base)                               — значение в точке,
    //   • s : refl_b = refl_b  в слое P(Base)       — «заполнение» 2-клетки.
    def ind[P[_ <: S2]](b: P[Base.type])(
      s: Coherence2[P[Base.type], b.type]
    ): Section[P] { type BaseValue = b.type } =
      new Section[P]:
        type BaseValue = b.type
        val baseValue: BaseValue & P[Base.type] & Singleton = b
        def apply(x: S2): P[x.type] = x.ind[P](b)(s)
        def surfCoherence: Coherence2[P[Base.type], b.type] = s

  // =====================================================================
  // БЛОК 1. Тривиальный мотив: постоянный слой Unit
  // базовый случай — тривиальный слой, единственная возможная 2-когерентность.
  // =====================================================================
  object trivialTest:
    type UnitFiber[X <: S2] = Unit

    val b: UnitFiber[S2.Base.type] = ()                 // = Unit
    val s: Coherence2[UnitFiber[S2.Base.type], b.type] =
      Path.Refl[Path[UnitFiber[S2.Base.type], b.type, b.type],
                Path.Refl[UnitFiber[S2.Base.type], b.type]]()

    val section = S2.ind[UnitFiber](b)(s)
    val atBase: Unit = section(S2.Base)

    println(s"[S²/trivial] section(Base) = $atBase")
    println(s"[S²/trivial] surfCoherence = ${section.surfCoherence}")


  // показывает, что индуктор S² действительно требует 2-клетку.
  // Два разных значения s (Refl vs Sym(Refl)) дают разные сечения:
  // совпадают на точках, но различаются как 2-когерентности.
  // Это прямой аналог того, как в S¹ разные stepLoop давали разные «накрутки».
  object boolTest:
    type BoolFiber[X <: S2] = Boolean

    val b: BoolFiber[S2.Base.type] = true                // = true
    type B = b.type                                      // true

    // (a) тривиальная когерентность
    val sTrivial: Coherence2[BoolFiber[S2.Base.type], B] =
      Path.Refl[Path[BoolFiber[S2.Base.type], B, B],
                Path.Refl[BoolFiber[S2.Base.type], B]]()

    // (b) Sym(Refl) — синтаксически другая 2-клетка
    val sSym: Coherence2[BoolFiber[S2.Base.type], B] =
      Path.Sym(
        Path.Refl[Path[BoolFiber[S2.Base.type], B, B],
                  Path.Refl[BoolFiber[S2.Base.type], B]]()
      )

    val sectionTrivial = S2.ind[BoolFiber](b)(sTrivial)
    val sectionSym     = S2.ind[BoolFiber](b)(sSym)

    println(s"[S²/bool] trivial: point = ${sectionTrivial(S2.Base)}, coherence = ${sectionTrivial.surfCoherence}")
    println(s"[S²/bool] sym:     point = ${sectionSym(S2.Base)},     coherence = ${sectionSym.surfCoherence}")


  // слой с собственной 1- и 2-структурой;
  // демонстрирует, что surfCoherence живёт именно в слое над Base.
  object pathTest:
    type PathFiber[X <: S2] = Path[Int, 0, 0]

    val b: PathFiber[S2.Base.type] = Path.Refl[Int, 0]()
    type B = b.type

    val s: Coherence2[PathFiber[S2.Base.type], B] =
      Path.Refl[Path[PathFiber[S2.Base.type], B, B],
                Path.Refl[PathFiber[S2.Base.type], B]]()

    val section = S2.ind[PathFiber](b)(s)
    val baseVal: Path[Int, 0, 0] = section(S2.Base)

    println(s"[S²/path] section(Base) = $baseVal")
    println(s"[S²/path] surfCoherence = ${section.surfCoherence}")


  // рекурсор в «множественный» тип —
  // 2-когерентность вынужденно тривиальна
  // (у Int нет нетривиальных 2-клеток в нашем кодировании),
  // поэтому сечение — просто константа.
  object recTest:
    type IntFiber[X <: S2] = Int

    val n: IntFiber[S2.Base.type] = 42
    type N = n.type                                          // 42

    val s: Coherence2[IntFiber[S2.Base.type], N] =
      Path.Refl[Path[IntFiber[S2.Base.type], N, N],
                Path.Refl[IntFiber[S2.Base.type], N]]()

    val section = S2.ind[IntFiber](n)(s)
    val value: Int = section(S2.Base)

    println(s"[S²/rec] S² → Int: значение в Base = $value (ожидается 42)")

  // =====================================================================
  // БЛОК 5. π₁(S²) = 0  и  π₂(S²) ≅ ℤ
  // Прямой аналог "winding : Ω¹(S¹) → ℤ" из S¹-кода,
  // но на одну размерность выше.
  // =====================================================================
  object piTest:

    // ---------- ЧАСТЬ 1. π₁(S²) = 0 ----------
    // В S² нет нетривиальных 1-петель: единственный "1-путь" — Refl.
    // Поэтому транспорт над Int-слоем вдоль любого 1-пути даёт 0.
    // (Ср. S¹: winding(Loop^n) = n ≠ 0.)

    // ---------- ЧАСТЬ 2. π₂(S²) ≅ ℤ ----------

    // Ω²(S², Base) = 2-петли в Base: 2-пути refl_Base ⇒ refl_Base.
    type TwoLoop =
      Path[Path[S2, S2.Base.type, S2.Base.type],
        Path.Refl[S2, S2.Base.type],
        Path.Refl[S2, S2.Base.type]]

    // winding2 : Ω²(S², Base) → ℤ  — структурная рекурсия,
    // точно как IntTransportPath, но по 2-клеткам (Surf вместо Loop).
    def winding2(c: Path[Path[S2, S2.Base.type, S2.Base.type], ?, ?]): Int =
      c match
        case Path.Refl() => 0
        case S2.Surf => 1 // Surf — образующая
        case Path.Sym(inner) => -winding2(inner)
        case Path.Trans(a, b) => winding2(a) + winding2(b)

    // Обратное отображение  ℤ → Ω²(S², Base):  n ↦ Surf^n
    def surfPow(n: Int): TwoLoop =
      if n >= 0 then
        (1 to n).foldLeft[TwoLoop](Path.Refl())((acc, _) => acc.andThen(S2.Surf))
      else
        (1 to -n).foldLeft[TwoLoop](Path.Refl())((acc, _) => acc.andThen(S2.Surf.inverse))

    // Проверка: winding2 ∘ surfPow = id_ℤ
    // (Обратное равенство surfPow ∘ winding2 = id_Ω² — «с точностью до гомотопии»,
    //  т.к. π₂(S²) свободна от Surf; в нашей строгой кодировке это не проверяется.)

    println("[π₂(S²) ≅ ℤ] Проверка winding2(surfPow(n)) == n:")
    for n <- -3 to 3 do
      val w = winding2(surfPow(n))
      println(f"  n = $n%3d  →  winding2(surfPow(n)) = $w%3d   ${if w == n then "✓" else "✗"}")

    // Базовые значения, аналогичные v0/v1/v2/vM4 из S¹-тестов
    val w_refl = winding2(Path.Refl()) // 0
    val w_surf = winding2(S2.Surf) // 1
    val w_surf2 = winding2(S2.Surf.andThen(S2.Surf)) // 2
    val w_surf3 = winding2(surfPow(3)) // 3
    val w_inv1 = winding2(S2.Surf.inverse) // -1
    val w_inv2 = winding2(surfPow(-2)) // -2
    val w_cancel = winding2(S2.Surf.andThen(S2.Surf.inverse)) // 0

    println(s"[π₂(S²)] w(refl)          = $w_refl")
    println(s"[π₂(S²)] w(Surf)          = $w_surf")
    println(s"[π₂(S²)] w(Surf·Surf)     = $w_surf2")
    println(s"[π₂(S²)] w(Surf³)         = $w_surf3")
    println(s"[π₂(S²)] w(Surf⁻¹)        = $w_inv1")
    println(s"[π₂(S²)] w(Surf⁻²)        = $w_inv2")
    println(s"[π₂(S²)] w(Surf·Surf⁻¹)   = $w_cancel  (сокращение, как Surf⁰)")

    // ---------- ЧАСТЬ 3 (бонус). 2-фибрация с действием Surf ↦ +1 ----------
    // Прямой аналог shiftFibration из S¹-кода: там transport(Loop) = +1,
    // здесь transport2(Surf) = +1.  walk по 2-пути, шаг stepSurf = +1.

    def transport2(v: Int, c: Path[Path[S2, S2.Base.type, S2.Base.type], ?, ?]): Int =
      c match
        case Path.Refl() => v
        case S2.Surf => v + 1 // действие Surf
        case Path.Sym(inner) => transport2Inv(v, inner)
        case Path.Trans(a, b) => transport2(transport2(v, a), b)

    def transport2Inv(v: Int, c: Path[Path[S2, S2.Base.type, S2.Base.type], ?, ?]): Int =
      c match
        case Path.Refl() => v
        case S2.Surf => v - 1
        case Path.Sym(inner) => transport2(v, inner)
        case Path.Trans(a, b) => transport2Inv(transport2Inv(v, b), a)

    val t0 = transport2(0, Path.Refl()) // 0
    val t1 = transport2(0, S2.Surf) // 1
    val t2 = transport2(0, surfPow(2)) // 2
    val t3 = transport2(0, surfPow(3)) // 3
    val tM1 = transport2(0, surfPow(-1)) // -1
    val tM2 = transport2(0, surfPow(-2)) // -2

    println(s"[2-transport] 0 → over refl = $t0,  Surf = $t1,  Surf² = $t2,  Surf³ = $t3,  Surf⁻¹ = $tM1,  Surf⁻² = $tM2")

  // =====================================================================
  // Запуск всех примеров
  // =====================================================================
  def runS2(): Unit =
    println("=== S² (2-сфера) ===")
    trivialTest
    boolTest
    pathTest
    recTest
    piTest