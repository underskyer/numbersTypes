package numberTypes.identityType

import scala.compiletime.ops.int.{+, -}
import scala.compiletime.ops.boolean.!

object s1new:

  // 1. Индуктивный тип путей с точными синглтон-концами (полностью полиморфный)
  sealed trait Path[A, X <: A, Y <: A]

  object Path:
    final case class Refl[A, X <: A]() extends Path[A, X, X]
    final case class Sym[A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P) extends Path[A, Y, X]
    final case class Trans[A, X <: A, Y <: A, Z <: A, P <: Path[A, X, Y], Q <: Path[A, Y, Z]](p: P, q: Q)
      extends Path[A, X, Z]

    final case class IntShift[X <: Int, Y <: Int](delta: Int) extends Path[Int, X, Y]

  extension [A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P)
    def inverse: Path.Sym[A, X, Y, P] = Path.Sym(p)
    def andThen[Z <: A, Q <: Path[A, Y, Z]](q: Q): Path.Trans[A, X, Y, Z, P, Q] = Path.Trans(p, q)

  // 2. ЧИСТАЯ окружность S¹: знает ТОЛЬКО про Base, Loop и абстрактное расслоение Fibration.
  // Никаких Int, Winding или Fiber внутри S1 больше нет!
  sealed trait S1:
    def ind[P[_ <: S1]](b: P[S1.Base.type]): P[this.type]

  object S1:
    case object Base extends S1:
      def ind[P[_ <: S1]](b: P[Base.type]): P[this.type] = b

    case object Loop extends Path[S1, Base.type, Base.type]

    // Абстрактный мотив индукции (Расслоение) над S¹
    trait Fibration[P[_ <: S1]]:
      type Layer
      type Transport[V <: Layer & Singleton] <: Layer
      type TransportPath[V <: Layer & Singleton, Q <: Path[S1, Base.type, Base.type]] <: Layer

      def transportValue[V <: Layer & Singleton](v: V): Transport[V]
      def stepLoop(v: Layer): Layer
      def stepLoopInverse(v: Layer): Layer

      // Универсальный транспорт вдоль любого пути Q на S¹,
      // опирающийся только на структуру Path и шаги расслоения
      def transport[V <: Layer & Singleton, Q <: Path[S1, Base.type, Base.type]](
        v: V,
        path: Q
      ): TransportPath[V, Q] =
        def loop(curr: Path[S1, ?, ?], acc: Layer): Layer = curr match
          case Path.Refl()      => acc
          case S1.Loop          => stepLoop(acc)
          case Path.Sym(inner)  => loopInverse(inner, acc)
          case Path.Trans(a, b) => loop(b, loop(a, acc))

        def loopInverse(curr: Path[S1, ?, ?], acc: Layer): Layer = curr match
          case Path.Refl()      => acc
          case S1.Loop          => stepLoopInverse(acc)
          case Path.Sym(inner)  => loop(inner, acc)
          case Path.Trans(a, b) => loopInverse(a, loopInverse(b, acc))

        loop(path, v).asInstanceOf[TransportPath[V, Q]]

    trait Section[P[_ <: S1]]:
      val fib: Fibration[P]
      val baseValue: fib.Layer & Singleton
      def apply(x: S1): P[x.type]
      def apd[Q <: Path[S1, Base.type, Base.type]](path: Q): fib.TransportPath[baseValue.type, Q]

    type SectionAux[P[_ <: S1], F <: Fibration[P], B] = Section[P] {
      val fib: F
      val baseValue: B & fib.Layer & Singleton
    }

    // Зависимый индуктор HoTT
    def ind[P[_ <: S1]](using F: Fibration[P])(
      b: F.Layer & Singleton & P[Base.type]
    )(
      l: Path[F.Layer, F.Transport[b.type], b.type]
    ): SectionAux[P, F.type, b.type] =
      new Section[P]:
        val fib: F.type = F
        val baseValue: b.type & fib.Layer & Singleton = b
        def apply(x: S1): P[x.type] = x.ind[P](b)
        def apd[Q <: Path[S1, Base.type, Base.type]](path: Q): fib.TransportPath[baseValue.type, Q] =
          fib.transport(baseValue, path)

    // Зависимый от пути мотив P[X, Q] на честной одноточечной S¹
    trait PathFibration[P[X <: S1, Q <: Path[S1, Base.type, X]]]:
      def overLoop[Q <: Path[S1, Base.type, Base.type]](
        current: P[Base.type, Q]
      ): P[Base.type, Path.Trans[S1, Base.type, Base.type, Base.type, Q, Loop.type]]

      def overLoopInv[Q <: Path[S1, Base.type, Base.type]](
        current: P[Base.type, Q]
      ): P[Base.type, Path.Trans[S1, Base.type, Base.type, Base.type, Q, Path.Sym[S1, Base.type, Base.type, Loop.type]]]

      def evalAlong[Q <: Path[S1, Base.type, Base.type]](
        baseVal: P[Base.type, Path.Refl[S1, Base.type]],
        path: Q
      ): P[Base.type, Q]

    trait PathDependentSection[P[X <: S1, Q <: Path[S1, Base.type, X]]]:
      def apply[Q <: Path[S1, Base.type, Base.type]](x: Base.type, path: Q): P[x.type, path.type]

    def depInd[P[X <: S1, Q <: Path[S1, Base.type, X]]](using PF: PathFibration[P])(
      b: P[Base.type, Path.Refl[S1, Base.type]]
    ): PathDependentSection[P] =
      new PathDependentSection[P]:
        def apply[Q <: Path[S1, Base.type, Base.type]](x: Base.type, path: Q): P[x.type, path.type] =
          PF.evalAlong(b, path).asInstanceOf[P[x.type, path.type]]
  // =========================================================================
  // БЛОК 1: Первоначальный test (вся логика Int вынесена из S1 сюда!)
  // =========================================================================
  object test:

    type IntFiber[X <: S1] = Int

    // Рекурсивный транспорт вдоль составного пути на уровне типов Int
    type IntTransportPath[V <: Int, Q <: Path[S1, S1.Base.type, S1.Base.type]] <: Int = Q match
      case Path.Refl[S1, ?]              => V
      case S1.Loop.type                  => V + 1
      case Path.Sym[S1, _, _, inner]     => IntTransportPathInv[V, inner]
      case Path.Trans[S1, _, _, _, p, q] => IntTransportPath[IntTransportPath[V, p], q]

    type IntTransportPathInv[V <: Int, Q <: Path[S1, S1.Base.type, S1.Base.type]] <: Int = Q match
      case Path.Refl[S1, ?]              => V
      case S1.Loop.type                  => V - 1
      case Path.Sym[S1, _, _, inner]     => IntTransportPath[V, inner]
      case Path.Trans[S1, _, _, _, p, q] => IntTransportPathInv[IntTransportPathInv[V, q], p]

    given shiftFibration: S1.Fibration[IntFiber] with
      type Layer = Int
      type Transport[V <: Int] = V + 1
      type TransportPath[V <: Int, Q <: Path[S1, S1.Base.type, S1.Base.type]] =
        IntTransportPath[V, Q]

      def transportValue[V <: (Int & Singleton)](v: V): Transport[V] = (v + 1).asInstanceOf[V + 1]
      def stepLoop(v: Int): Int = v + 1
      def stepLoopInverse(v: Int): Int = v - 1

    val p0 = Path.Refl[S1, S1.Base.type]()
    val p1 = S1.Loop
    val p2 = S1.Loop.andThen(S1.Loop)
    val pMinus4 = S1.Loop.inverse
      .andThen(S1.Loop.inverse)
      .andThen(S1.Loop.inverse)
      .andThen(S1.Loop.inverse)

    val zero: 0 = 0
    val v0: 0 = shiftFibration.transport(zero, p0)
    val v1: 1 = shiftFibration.transport(zero, p1)
    val v2: 2 = shiftFibration.transport(zero, p2)
    val vM4: -4 = shiftFibration.transport(zero, pMinus4)

    final case class IntStep[X <: Int, Y <: Int]() extends Path[Int, X, Y]

    val afterLoop: 1 = shiftFibration.transportValue(zero)

    val stepFromOneToZero: Path[Int, 1, 0] = IntStep()
    val section = S1.ind[IntFiber](zero)(stepFromOneToZero)

    val minusFour: -4 = -4
    val stepFromMinusThreeToMinusFour: Path[Int, -3, -4] = IntStep[-3, -4]()
    val sectionNegative = S1.ind[IntFiber](minusFour)(stepFromMinusThreeToMinusFour)

    println(s"v0 = $v0 (тип 0), v1 = $v1 (тип 1), v2 = $v2 (тип 2), vM4 = $vM4 (тип -4)")
    println(s"Значение в Base (0): ${section(S1.Base)}, после транспорта вдоль Loop: $afterLoop")
    println(s"Значение в Base (-4): ${sectionNegative(S1.Base)}")

  // =========================================================================
  // БЛОК 2: Двулистное накрытие (Лента Мёбиуса / Переключатель чётности)
  // =========================================================================
  object mobiusTest:
    type BoolFiber[X <: S1] = Boolean

    given mobiusFibration: S1.Fibration[BoolFiber] with
      type Layer = Boolean
      type Transport[V <: Boolean] = ![V]
      type TransportPath[V <: Boolean, Q <: Path[S1, S1.Base.type, S1.Base.type]] <: Boolean = Q match
        case Path.Refl[S1, ?]              => V
        case S1.Loop.type                  => ![V]
        case Path.Sym[S1, _, _, inner]     => TransportPath[V, inner]
        case Path.Trans[S1, _, _, _, p, q] => TransportPath[TransportPath[V, p], q]

      def transportValue[V <: (Boolean & Singleton)](v: V): Transport[V] = (!v).asInstanceOf[![V]]
      def stepLoop(v: Boolean): Boolean = !v
      def stepLoopInverse(v: Boolean): Boolean = !v

    val startFalse: false = false
    val after1Loop: true = mobiusFibration.transport(startFalse, S1.Loop)

    val doubleLoop = S1.Loop.andThen(S1.Loop)
    val after2Loops: false = mobiusFibration.transport(startFalse, doubleLoop)

    println(s"[Лента Мёбиуса] Старт: $startFalse -> 1 оборот: $after1Loop -> 2 оборота: $after2Loops")

  // =========================================================================
  // БЛОК 3: Спираль над окружностью и поднятие составных путей (apd)
  // =========================================================================
  object spiralTest:
    type IntFiber[X <: S1] = Int

    // Используем структурную рекурсию IntTransportPath из test вместо Winding внутри S1
    given spiralFibration: S1.Fibration[IntFiber] with
      type Layer = Int
      type Transport[V <: Int] = V + 1
      type TransportPath[V <: Int, Q <: Path[S1, S1.Base.type, S1.Base.type]] =
        test.IntTransportPath[V, Q]

      def transportValue[V <: (Int & Singleton)](v: V): Transport[V] = (v + 1).asInstanceOf[V + 1]
      def stepLoop(v: Int): Int = v + 1
      def stepLoopInverse(v: Int): Int = v - 1

    val zero: 0 = 0
    val minusFour: -4 = -4

    val glue0: Path[Int, 1, 0] = Path.IntShift(-1)
    val glueM4: Path[Int, -3, -4] = Path.IntShift[-3, -4](-1)

    val section0 = S1.ind[IntFiber](zero)(glue0)
    val sectionM4 = S1.ind[IntFiber](minusFour)(glueM4)

    val complexPath = S1.Loop.andThen(S1.Loop).andThen(S1.Loop.inverse)

    val liftedFrom0: 1 = section0.apd(complexPath)
    val liftedFromM4: -3 = sectionM4.apd(complexPath)

    println(s"[Спираль] Значение в Base: ${section0(S1.Base)}, поднятие пути (+2 - 1): $liftedFrom0")
    println(s"[Спираль] Значение в Base: ${sectionM4(S1.Base)}, поднятие пути (+2 - 1): $liftedFromM4")

  // =========================================================================
  // БЛОК 4: Зависимый индуктор на честной S¹ с мотивом, зависящим от пути
  // =========================================================================
  object pathDependentTest:

    // Число оборотов вычисляется локально здесь, а не внутри S1
    type LocalWinding[P <: Path[S1, ?, ?]] <: Int = P match
      case Path.Refl[S1, ?]              => 0
      case S1.Loop.type                  => 1
      case Path.Sym[S1, _, _, inner]     => 0 - LocalWinding[inner]
      case Path.Trans[S1, _, _, _, p, q] => LocalWinding[p] + LocalWinding[q]

    type WindingTypedFiber[X <: S1, Q <: Path[S1, S1.Base.type, X]] = LocalWinding[Q] match
      case 0 => Int
      case 1 => String
      case 2 => Boolean
      case _ => List[Int]

    private def valueForWinding(start: Int, w: Int): Any = w match
      case 0 => start
      case 1 => s"Оборот #1 (старт = $start)"
      case 2 => (start % 2 == 0)
      case n => List(start, n)

    private def countWinding(p: Path[S1, ?, ?]): Int = p match
      case Path.Refl()      => 0
      case S1.Loop          => 1
      case Path.Sym(inner)  => -countWinding(inner)
      case Path.Trans(a, b) => countWinding(a) + countWinding(b)

    given windingFibration: S1.PathFibration[WindingTypedFiber] with
      def overLoop[Q <: Path[S1, S1.Base.type, S1.Base.type]](
        current: WindingTypedFiber[S1.Base.type, Q]
      ): WindingTypedFiber[S1.Base.type, Path.Trans[S1, S1.Base.type, S1.Base.type, S1.Base.type, Q, S1.Loop.type]] =
        val nextW = current match
          case _: Int      => 1
          case _: String   => 2
          case _: Boolean  => 3
          case xs: List[?] => xs.asInstanceOf[List[Int]](1) + 1
        val base = current match
          case n: Int => n
          case _      => 10
        valueForWinding(base, nextW)
          .asInstanceOf[WindingTypedFiber[S1.Base.type, Path.Trans[S1, S1.Base.type, S1.Base.type, S1.Base.type, Q, S1.Loop.type]]]

      def overLoopInv[Q <: Path[S1, S1.Base.type, S1.Base.type]](
        current: WindingTypedFiber[S1.Base.type, Q]
      ): WindingTypedFiber[S1.Base.type, Path.Trans[S1, S1.Base.type, S1.Base.type, S1.Base.type, Q, Path.Sym[S1, S1.Base.type, S1.Base.type, S1.Loop.type]]] =
        valueForWinding(10, -1)
          .asInstanceOf[WindingTypedFiber[S1.Base.type, Path.Trans[S1, S1.Base.type, S1.Base.type, S1.Base.type, Q, Path.Sym[S1, S1.Base.type, S1.Base.type, S1.Loop.type]]]]

      def evalAlong[Q <: Path[S1, S1.Base.type, S1.Base.type]](
        baseVal: WindingTypedFiber[S1.Base.type, Path.Refl[S1, S1.Base.type]],
        path: Q
      ): WindingTypedFiber[S1.Base.type, Q] =
        val w = countWinding(path)
        valueForWinding(baseVal, w).asInstanceOf[WindingTypedFiber[S1.Base.type, Q]]

    val section = S1.depInd[WindingTypedFiber](10)

    val path0 = Path.Refl[S1, S1.Base.type]()
    val path1 = S1.Loop
    val path2 = S1.Loop.andThen(S1.Loop)
    val path3 = path2.andThen(S1.Loop)

    val res0: Int = section(S1.Base, path0)
    val res1: String = section(S1.Base, path1)
    val res2: Boolean = section(S1.Base, path2)
    val res3: List[Int] = section(S1.Base, path3)

    println(s"[Path-Dependent S1] 0 оборотов (Int):       ${res0 + 5}")
    println(s"[Path-Dependent S1] 1 оборот   (String):    '$res1' (длина = ${res1.length})")
    println(s"[Path-Dependent S1] 2 оборота  (Boolean):   $res2 (инверсия = ${!res2})")
    println(s"[Path-Dependent S1] 3 оборота  (List[Int]): $res3 (сумма = ${res3.sum})")
