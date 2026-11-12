package numberTypes.identityType

// https://share.google/aimode/7y9No4glqqgmehCmL
//  π₁(S¹) ≃ ℤ


object s1:

  // 1. Индуктивный тип путей в произвольном типе A
  sealed trait Path[A, X <: A, Y <: A]

  object Path:
    final case class Refl[A, X <: A]() extends Path[A, X, X]
    final case class Sym[A, X <: A, Y <: A](p: Path[A, X, Y]) extends Path[A, Y, X]
    final case class Trans[A, X <: A, Y <: A, Z <: A](p: Path[A, X, Y], q: Path[A, Y, Z]) extends Path[A, X, Z]

  extension [A, X <: A, Y <: A](p: Path[A, X, Y])
    def inverse: Path[A, Y, X] = Path.Sym(p)
    def andThen[Z <: A](q: Path[A, Y, Z]): Path[A, X, Z] = Path.Trans(p, q)

  // 2. Тип окружности S¹: одна точка Base и один конструктор пути Loop
  enum S1:
    case Base

  object S1:
    // Каноническая образующая петля как обычный case object в иерархии Path
    case object loop extends Path[S1, S1.Base.type, S1.Base.type]

    // Элиминатор (рекурсор rec_S1):
    // Переводит любую петлю на S¹ (составленную из Loop, Refl, Sym, Trans) в петлю в типе A
    def rec[A](b: A)(l: Path[A, A, A]): (S1 => A, Path[S1, S1.Base.type, S1.Base.type] => Path[A, A, A]) =
      val onPoint: S1 => A = {
        case S1.Base => b
      }

      def onPath[X <: S1, Y <: S1](p: Path[S1, X, Y]): Path[A, A, A] = p match
        case S1.loop => l
        case Path.Refl() => Path.Refl()
        case Path.Sym(inner) => onPath(inner).inverse
        case Path.Trans(p, q) => onPath(p).andThen(onPath(q))

      (onPoint, onPath)

    // 3. ЗАВИСИМЫЙ ЭЛИМИНАТОР (Принцип индукции ind_S1):
    // P[_ <: S1] — зависимое семейство типов над окружностью.
    // tr — правило транспорта вдоль петли Loop в слое P[Base].
    // b  — значение функции в базовой точке: P[Base].
    // l  — зависимый путь (PathOver): доказательство, что transport(Loop, b) совпадает с b в слое P[Base].
    // Возвращает зависимую функцию (x: S1) => P[x.type] и действие на петлях apd_f.
    def ind[P[_ <: S1]](
      tr: (Path[S1, S1.Base.type, S1.Base.type], P[S1.Base.type]) => P[S1.Base.type]
    )(
      b: P[S1.Base.type]
    )(
      l: Path[P[S1.Base.type], P[S1.Base.type], P[S1.Base.type]]
    ): (
        (x: S1) => P[x.type],
        Path[S1, S1.Base.type, S1.Base.type] => Path[P[S1.Base.type], P[S1.Base.type], P[S1.Base.type]]
      ) =
      // Зависимая функция на точках: возвращаемый тип P[x.type] зависит от аргумента x
      val onPoint: (x: S1) => P[x.type] = (x: S1) =>
        x match
          case S1.Base =>
          // Свидетельство равенства типов S1.Base.type =:= x.type
          summon[S1.Base.type =:= S1.Base.type]
            .asInstanceOf[S1.Base.type =:= x.type]
            .substituteCo[[X] =>> P[X & S1.Base.type]](b)
            .asInstanceOf[P[x.type]]

      // Зависимое действие на путях (apd_f):
      // Для любого пути p в S1 строит зависимый путь над p в слое P[Base]
      def apd[X <: S1, Y <: S1](p: Path[S1, X, Y]): Path[P[S1.Base.type], P[S1.Base.type], P[S1.Base.type]] =
        p match
          case S1.loop => l
          case Path.Refl() => Path.Refl()
          case Path.Sym(inner) => apd(inner).inverse
          case Path.Trans(p, q) => apd(p).andThen(apd(q))

      (onPoint, apd)

  // 3. Канонический код типа во Вселенной
  sealed trait TypeCode[T]

  object TypeCode:
    private final case class Instance[T]() extends TypeCode[T]:
      override def toString: String = "TypeCode"

    given universal[T]: TypeCode[T] = Instance[T]()

    def apply[T](using tc: TypeCode[T]): TypeCode[T] = tc

  // Автоморфизм на типе T как петля в TypeCode[T]
  final case class AutoEquiv[T](to: T => T, from: T => T)
    extends Path[TypeCode[T], TypeCode[T], TypeCode[T]]

  // 4. Единый интерпретатор пути (без evalInverse):
  // сворачивает любой составной путь в итоговую биекцию AutoEquiv[T]
  def eval[T, C1 <: TypeCode[T], C2 <: TypeCode[T]](path: Path[TypeCode[T], C1, C2]): AutoEquiv[T] = path match
    case Path.Refl() => AutoEquiv(identity, identity)
    case eq@AutoEquiv(_, _) => eq
    case Path.Sym(p) =>
      val AutoEquiv(to, from) = eval(p)
      AutoEquiv(from, to)
    case Path.Trans(p, q) =>
      val AutoEquiv(to1, from1) = eval(p)
      val AutoEquiv(to2, from2) = eval(q)
      AutoEquiv(to1.andThen(to2), from2.andThen(from1))

  // 5. ОБРАТНОЕ ПРЕОБРАЗОВАНИЕ (decode): строит каноническую петлю Loop^n по целому числу n
  def decode(n: Int): Path[S1, S1.Base.type, S1.Base.type] =
    if n == 0 then Path.Refl()
    else if n > 0 then (1 to n).foldLeft[Path[S1, S1.Base.type, S1.Base.type]](Path.Refl())((acc, _) => acc.andThen(S1.loop))
    else (1 to -n).foldLeft[Path[S1, S1.Base.type, S1.Base.type]](Path.Refl())((acc, _) => acc.andThen(S1.loop.inverse))

  
  // 5. Проверка работы
  object test:
    val succ: AutoEquiv[Int] = AutoEquiv(_ + 1, _ - 1)

    val (code, transport) = S1.rec(TypeCode[Int])(succ)

    // Строим сложный путь напрямую через общие extension-методы Path:
    val complexLoop =
      S1.loop
        .andThen(S1.loop)
        .andThen(S1.loop.inverse)
        .andThen(S1.loop)

    val resultEquiv: AutoEquiv[Int] = eval(transport(complexLoop))
    val windingNumber: Int = resultEquiv.to(0)

    val decodedPath = decode(-3)
    val encodedNumber = eval(transport(decodedPath)).to(0)
    println(s"decode(-3) -> encode: $encodedNumber") // Выведет: -3

    println(s"Значение в базовой точке: ${code(S1.Base)}")
    println(s"Число оборотов для сложного пути: $windingNumber")


    // Пример использования зависимого элиминатора S1.ind:
    // Задаём зависимое семейство типов P(x) = Path[S1, x, x] (тип петель в каждой точке x окружности)
    type LoopSpace[X <: S1] = Path[S1, X, X]

    // Транспорт петли q вдоль пути p по формуле конъюгации: p⁻¹ ∙ q ∙ p
    val conjugationTransport: (Path[S1, S1.Base.type, S1.Base.type], LoopSpace[S1.Base.type]) => LoopSpace[S1.Base.type] =
      (p, q) => p.inverse.andThen(q).andThen(p)

    // В базовой точке Base выбираем каноническую петлю S1.Loop : LoopSpace[Base].
    // Поскольку в фундаментальной группе S¹ выполнено loop⁻¹ ∙ loop ∙ loop = loop (коммутативность),
    // зависимый путь над Loop тривиален (Refl).
    val (canonicalLoops, apdLoops) = S1.ind[LoopSpace](conjugationTransport)(S1.loop)(Path.Refl())

    // Получаем зависимую функцию (x: S1) => LoopSpace[x.type]
    val loopAtBase: LoopSpace[S1.Base.type] = canonicalLoops(S1.Base)
    println(s"Каноническая петля в точке Base из индуктора: $loopAtBase")
