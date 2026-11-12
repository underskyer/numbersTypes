package numberTypes.identityType

import scala.compiletime.ops.int.-


object s1new:

  import scala.compiletime.ops.int.+

  // 1. Индуктивный тип путей с точными синглтон-концами
  sealed trait Path[A, X <: A, Y <: A]

  object Path:
    final case class Refl[A, X <: A]() extends Path[A, X, X]
    final case class Sym[A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P) extends Path[A, Y, X]
    final case class Trans[A, X <: A, Y <: A, Z <: A, P <: Path[A, X, Y], Q <: Path[A, Y, Z]](p: P, q: Q)
      extends Path[A, X, Z]
    
  extension [A, X <: A, Y <: A, P <: Path[A, X, Y]](p: P)
    def inverse: Path.Sym[A, X, Y, P] = Path.Sym(p)
    def andThen[Z <: A, Q <: Path[A, Y, Z]](q: Q): Path.Trans[A, X, Y, Z, P, Q] = Path.Trans(p, q)

  // 2. Тип окружности S¹
  sealed trait S1:
    def ind[P[_ <: S1]](b: P[S1.Base.type]): P[this.type]

  object S1:
    case object Base extends S1:
      def ind[P[_ <: S1]](b: P[Base.type]): P[this.type] = b

    case object Loop extends Path[S1, Base.type, Base.type]

    // 3. МОТИВ ИНДУКЦИИ (Расслоение) на уровне типов:
    // Задаёт слой над базовой точкой (с типом значений Layer)
    // и типовую функцию Transport[V], вычисляющую новый синглтон-тип после обхода Loop!
    trait Fibration[P[_ <: S1]]:
      type Layer
      type Transport[V <: Layer & Singleton] <: Layer

      def transportValue[V <: Layer & Singleton](v: V): Transport[V]

    // Зависимый индуктор HoTT:
    // Принимает конкретный элемент b типа F.Layer (например, литерал 0: 0)
    // и требует путь в типе F.Layer МЕЖДУ ВЫЧИСЛЕННЫМ ТИПОМ F.Transport[b.type] (то есть 1) И ТИПОМ b.type (то есть 0)!
    def ind[P[_ <: S1]](using F: Fibration[P])(
      b: F.Layer & P[Base.type]
    )(
      l: Path[F.Layer, F.Transport[b.type], b.type]
    ): (x: S1) => P[x.type] =
      (x: S1) => x.ind[P](b)

    trait Section[P[_ <: S1]]:
      def apply(x: S1): P[x.type]

    type Fiber[P <: Path[S1, ?, ?]] <: Int = P match
      case Path.Refl[S1, ?] => 0
      case S1.Loop.type => 1
      case Path.Sym[S1, _, _, inner] => 0 - Fiber[inner]
      case Path.Trans[S1, _, _, _, p, q] => Fiber[p] + Fiber[q]

    def transport(p: Path[S1, S1.Base.type, S1.Base.type]): Fiber[p.type] =
      def eval(curr: Path[S1, ?, ?]): Int = curr match
        case Path.Refl() => 0
        case S1.Loop => 1
        case Path.Sym(inner) => -eval(inner)
        case Path.Trans(a, b) => eval(a) + eval(b)
      eval(p).asInstanceOf[Fiber[p.type]]


    def ind1(
      b: Fiber[Path.Refl[S1, Base.type]]
    )(
      l: Path[Int, Fiber[Loop.type], Fiber[Path.Refl[S1, Base.type]]]
    ): Section[[X <: S1] =>> Fiber[Path.Refl[S1, X]]] =
      (x: S1) => x.ind[[X <: S1] =>> Fiber[Path.Refl[S1, X]]](b)

  // 4. Проверка работы на литеральных типах Int (0, 1, -4)
  object test:

    // Строим пути на окружности (значения с точными синглтон-типами):
    val p0 = Path.Refl[S1, S1.Base.type]()
    val p1 = S1.Loop
    val p2 = S1.Loop.andThen(S1.Loop)
    val pMinus4 = S1.Loop.inverse
      .andThen(S1.Loop.inverse)
      .andThen(S1.Loop.inverse)
      .andThen(S1.Loop.inverse)

    // Компилятор САМ выводит точные синглтон-типы 0, 1, 2, -4 из типов путей!
    val v0: 0 = S1.transport(p0)
    val v1: 1 = S1.transport(p1)
    val v2: 2 = S1.transport(p2)
    val vM4: -4 = S1.transport(pMinus4)

    // Попытка передать Path.Refl() в S1.ind не скомпилируется,
    // так как Fiber[Loop.type] = 1, а Fiber[Refl] = 0:
    final case class IntStep[X <: Int, Y <: Int]() extends Path[Int, X, Y]

    val step1to0: Path[Int, 1, 0] = IntStep()

    val section = S1.ind(v0)(step1to0)

    println(s"v0 = $v0 (тип 0), v1 = $v1 (тип 1), v2 = $v2 (тип 2), vM4 = $vM4 (тип -4)")
    println(s"Значение сечения в Base: ${section(S1.Base)}")
    



    // Мотив расслоения: в каждой точке X <: S1 живёт синглтон-тип Int
    type IntFiber[X <: S1] = Int

    // Определяем нетривиальное накрытие (сдвиг на +1 при обходе вокруг окружности)
    // с вычислением на уровне типов через scala.compiletime.ops.int.+
    given shiftFibration: S1.Fibration[IntFiber] with
      type Layer = Int
      type Transport[V <: Int] = V + 1

      def transportValue[V <: (Int & Singleton)](v: V): Transport[V] = (v + 1).asInstanceOf[V + 1]

    // Выбираем точку b = 0 (имеющую точный литеральный тип 0)
    val zero: 0 = 0

    // Посмотрим, какой тип компилятор выводит для результата транспорта вдоль Loop:
    val afterLoop: 1 = shiftFibration.transportValue(zero)

    // ПОПЫТКА 1: Попытаемся обмануть индуктор и передать Path.Refl()
    // КОМПИЛЯТОР ВЫДАСТ ОШИБКУ:
    // Found:    Path[Int, 1, 1] (или Path[Int, 0, 0])
    // Required: Path[Int, 1, 0]
    // Компилятор САМ вычислил 0 + 1 = 1 на уровне типов и увидел, что 1 != 0!
    /*
    val impossible = S1.ind[IntFiber](zero)(Path.Refl())
    */

    // ПОПЫТКА 2: Зададим явный шаг в слое Int (переход между конкретными литералами X и Y)
    //final case class IntStep[X <: Int, Y <: Int]() extends Path[Int, X, Y]

    // Здесь компилятор строго требует путь ИЗ ТИПА 1 В ТИП 0: Path[Int, 1, 0]!
    val stepFromOneToZero: Path[Int, 1, 0] = IntStep[1, 0]()

//    val section: (x: S1) => IntFiber[x.type] = x =>
//      S1.ind[IntFiber](zero)(stepFromOneToZero).asInstanceOf[IntFiber[x.type]]

    // Проверим для отрицательного числа -4:
    val minusFour: -4 = -4
    // Компилятор автоматически вычисляет -4 + 1 = -3 и требует Path[Int, -3, -4]:
    val stepFromMinusThreeToMinusFour: Path[Int, -3, -4] = IntStep[-3, -4]()
    val sectionNegative = S1.ind[IntFiber](minusFour)(stepFromMinusThreeToMinusFour)

//    println(s"Значение в Base (0): ${section(S1.Base)}, после транспорта вдоль Loop: $afterLoop")
//    println(s"Значение в Base (-4): ${sectionNegative(S1.Base)}")
