package numberTypes.identityType

object s1:

  // 1. Честный 1-тип (группоид) над пространством A
  trait Groupoid[A]:
    // Семейство типов путей между точками x и y пространства A
    type Path[x <: A, y <: A]
    def refl[x <: A]: Path[x, x]
    def sym[x <: A, y <: A](p: Path[x, y]): Path[y, x]
    def trans[x <: A, y <: A, z <: A](p: Path[x, y], q: Path[y, z]): Path[x, z]

  // 2. Тип окружности S¹
  enum S1:
    case Base

  object S1:
    // Абстрактная петля на S¹:
    // Для любого группоида A, любой точки b: A и любой петли l: Path[b.type, b.type]
    // вычисляет результирующий путь в A.
    trait Loop:
      def apply[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]): G.Path[b.type, b.type]
    // S¹ сам является группоидом
    given Groupoid[S1] with
      type Path[x <: S1, y <: S1] = Loop
      def refl[x <: S1]: Loop = new Loop:
        def apply[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]) = G.refl[b.type]
      def sym[x <: S1, y <: S1](p: Loop): Loop = new Loop:
        def apply[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]) = G.sym(p(b)(l))
      def trans[x <: S1, y <: S1, z <: S1](p: Loop, q: Loop): Loop = new Loop:
        def apply[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]) = G.trans(p(b)(l), q(b)(l))

    // Каноническая образующая петля: loop : Base = Base
    val loop: Loop = new Loop:
      def apply[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]) = l

    // 3. УНИВЕРСАЛЬНЫЙ РЕКУРСОР (rec_S1)
    // Обратите внимание на зависимый возвращаемый тип G.Path[b.type, b.type]:
    // компилятор сохраняет точную связь с переданной точкой b!
    def rec[A](using G: Groupoid[A])(b: A)(l: G.Path[b.type, b.type]): (S1 => A, Loop => G.Path[b.type, b.type]) =
      val onPoint: S1 => A = {
        case S1.Base => b
      }
      val onLoop: Loop => G.Path[b.type, b.type] = p => p(b)(l)
      (onPoint, onLoop)

  // Эквивалентность типов X ≃ Y
  case class Equiv[X, Y](to: X => Y, from: Y => X)

  // Вселенная типов, представленная индексированными кодами типов (GADT / Tarski-style Universe)
  trait TypeCode[T]

  // УНИВЕРСАЛЬНЫЙ GIVEN ДЛЯ ВСЕЛЕННОЙ ТИПОВ (Унивалентность по Тарскому):
  // Для любого типа T, представленного кодом TypeCode[T],
  // путями между объектами этого кода являются эквивалентности Equiv[T, T].
  given univalence[T]: Groupoid[TypeCode[T]] with
    type Path[x <: TypeCode[T], y <: TypeCode[T]] = Equiv[T, T]

    def refl[x <: TypeCode[T]]: Equiv[T, T] = Equiv(identity, identity)
    def sym[x <: TypeCode[T], y <: TypeCode[T]](p: Equiv[T, T]): Equiv[T, T] = Equiv(p.from, p.to)
    def trans[x <: TypeCode[T], y <: TypeCode[T], z <: TypeCode[T]](
      p: Equiv[T, T],
      q: Equiv[T, T]
    ): Equiv[T, T] = Equiv(p.to.andThen(q.to), q.from.andThen(p.from))

  object test:

    val G_S1 = summon[Groupoid[S1]]

    // Создаём точку во Вселенной, представляющую тип Int
    val intType = new TypeCode[Int] {}

    // Автоморфизм (x => x + 1) : Equiv[Int, Int]
    val succEquiv: Equiv[Int, Int] = Equiv(_ + 1, _ - 1)

    // Применяем универсальный рекурсор S1.rec к точке intType!
    // Компилятор автоматически находит given univalence[Int]
    // и выводит точный тип transport: S1.Loop => Equiv[Int, Int]
    val (code, transport) = S1.rec(intType)(succEquiv)

    // Строим путь на окружности: p = loop ∙ loop ∙ loop⁻¹ ∙ loop
    val p: S1.Loop = G_S1.trans(
      G_S1.trans(G_S1.trans(S1.loop, S1.loop), G_S1.sym(S1.loop)),
      S1.loop
    )

    // Никаких приведений типов! transport(p) имеет статический тип Equiv[Int, Int]
    val equivAtP: Equiv[Int, Int] = transport(p)
    val windingNumber: Int = equivAtP.to(0)

    println(s"Число оборотов: $windingNumber") // Выведет: 2
