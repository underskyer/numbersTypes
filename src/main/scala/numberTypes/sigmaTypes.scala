package numberTypes

object sigmaTypes:


  type Σʙᴏᴜɴᴅ [IndexType, F[_ <: IndexType]] = F[IndexType]

  //• Преимущества:
  //	• Идеальная инкапсуляция типов:
  //    	Индекс и значение не хранятся в полях,
  //    	а лениво «передаются» в колбэк в момент вызова.
  //    	Это классический чистофункциональный подход,
  //    	не зависящий от особенностей реализации ООП в компиляторе.
  //	• Отсутствие промежуточного рантайм-выделения памяти под поля:
  //    	Нет необходимости создавать объекты-контейнеры
  //    	для хранения tag и value по отдельности —
  //    	они живут внутри замыкания полиморфной функции.
  //• Недостатки:
  //	• Экстремальная сложность для тайпчекера:
  //    	Scala 3 пасует перед попыткой редуцировать сложные Match Types (вроде NatFamily)
  //    	внутри абстрактных полиморфных функций.
  //    	Как результат — в индукторе приходится полностью скрывать типы за asInstanceOf и Any.
  //	• Сложность отладки и чтения:
  //    	Код становится инвертированным (Continuation-Passing Style).
  //    	Вместо того чтобы взять данные из Сигмы,
  //    	вы должны передать в Сигму функцию, которая эти данные обработает.
  //    	Это сильно усложняет чтение кода.
  //	• Рантайм-накладные расходы (Аллокация лямбд):
  //    	На каждом шаге рекурсии создается объект полиморфной функции,
  //    	что в рантайме JVM может приводить к высокой нагрузке на Garbage Collector при больших числах.
  type Σᴄʜɪʀᴄʜ[IndexType, F[_ <: IndexType]] = [Y] => ([I <: IndexType] => F[I] => Y) => Y

  //• Преимущества:
  //	• Максимальная прозрачность для Match Types:
  //    	Компилятор Scala 3 лучше всего умеет редуцировать типы,
  //    	когда точный индекс закреплен как открытый тип-член (type Tag).
  //    	Это минимизирует зависания тайпчекера.
  //	• Прямой доступ к полям:
  //    	Значения tag и value доступны напрямую без распаковки,
  //    	что упрощает написание логики (например, можно сделать sigma.tag match).
  //• Недостатки:
  //	• Сложный синтаксис создания:
  //    	Требуется явное создание анонимных классов через new Sigma { ... } (или сложные смарт-конструкторы),
  //    	что загромождает код.
  //	• Размытие типов (Type Erasure / Widening):
  //    	Если случайно передать такое значение в метод,
  //    	не сохранив refinement (например, апкастнуть до базового Sigma),
  //    	компилятор мгновенно «забудет» точный индекс,
  //    	и восстановить его без явных кастов будет невозможно.
  trait Σᴏᴏᴘ[IndexType, F[_ <: IndexType]]:
    type I <: IndexType // первая проекция
    //def index: I
    val value: F[I]        // вторая проекция

  object Σᴏᴏᴘ :
    case class OOP[IndexType, F[_ <: IndexType], In <: IndexType](value: F[In]) extends Σᴏᴏᴘ[IndexType, F]:
      type I = In
      
    def apply[
      IndexType,
      TypeFamily[_ <: IndexType],
      In <: IndexType
    ](v: TypeFamily[In]): Σᴏᴏᴘ[IndexType, TypeFamily] =
      OOP[IndexType, TypeFamily, In](v)
//      new:
//        type I = In
//        //def index: In = valueOf[In]
//        val value: TypeFamily[In] = v

  // • Преимущества:
  //	• Самый лаконичный и идиоматичный синтаксис:
  //    	Создание элементов через SigmaEnum.In(value, tag) выглядит чисто,
  //    	привычно для Scala-разработчиков и не требует бойлерплейта.
  //	• Безопасный паттерн-матчинг:
  //    	Конструкция case In(fi, index) => позволяет
  //    	извлекать компоненты стандартным для языка способом.
  //• Недостатки:
  //	• Проблема стирания литералов в GADT:
  //    	Scala 3 при паттерн-матчинге по кейсу GADT-enum
  //    	часто обобщает типы-литералы (например, true превращается в Boolean).
  //    	Из-за этого внутри индуктора нам пришлось делать двойной матч:
  //    	сначала по структуре In, а затем по рантайм-значению index.
  //	• Тяжело для Match Types:
  //    	Компилятору сложнее протащить точную связь
  //    	между параметрами типа кейса In и внешним match-type,
  //    	из-за чего приходится использовать asInstanceOf.
  enum Σɢᴀᴅᴛ[IndexType, G[_ <: IndexType]]: //
    case In[I, F[_ <: I], i <: I](index: i, fi: F[i]) extends Σɢᴀᴅᴛ[I, F]

  inline def inΣ[I, F[_ <: I], i <: I: ValueOf](fi: F[i]): Σɢᴀᴅᴛ[I, F] =
    Σɢᴀᴅᴛ.In[I, F, i](summon[ValueOf[i]].value, fi)

  type ∑ = Σɢᴀᴅᴛ


  object test:

    println()
    println("sigma pi:")

    type Sum[A, B] = ∑[Bool, Pair[A, B]]

    def sumIso[A, B]: (A + B) ≅ Sum[A, B] = (
      forward = _.fold[Sum[A, B]](
        inΣ[Bool, Pair[A, B], false],
        inΣ[Bool, Pair[A, B], true]
      ),
      backward =
        case Σɢᴀᴅᴛ.In(false, a: A) => Left(a)
        case Σɢᴀᴅᴛ.In(true,  b: B) => Right(b)
    )

    val iso = sumIso[Int, String]
    println("sum iso left : " + iso.backward(iso.forward(Left[Int, String](42))))
    println("sum iso right: " + iso.backward(iso.forward(Right[Int, String]("str: 42"))))

    type ProdΣ[A, B] = ∑[A, Const[B]]
    def prodΣIso[A, B]: (A × B) ≅ ProdΣ[A, B] = (
      forward = Σɢᴀᴅᴛ.In[A, Const[B], A].tupled,
      backward = { case Σɢᴀᴅᴛ.In(a: A, b: B) => a -> b }
    )


    val optUsage: [X] => Option[X] => String =
      [X] => x => x.map(_.asInstanceOf[Matchable]).fold("???"): // .map(_.asInstanceOf[Matchable])
        case str: String => "Str " + str
        case int: Int => "Int " + int
        case x => "??? " + x


    val d: Σᴄʜɪʀᴄʜ[Bool, Option] = [_] => x => x(Some(true))
    val dd = d(optUsage)
    println("∑: " + dd)

//    val dSS: ∑[Option] = in(Some(42))(using ValueOf[Int](24))
//    val ddSS = dSS match {
//      case ∑.In(fa, _) => optUsage(fa)
//    }
//    println("∑∑: " + ddSS)

//    val dSSS: Σᴏᴏᴘ[Bool, Option] = Σᴏᴏᴘ[Bool, Option, true]()
//    val ddSSS = optUsage(dSSS.fi)
//    println("∑∑∑: " + ddSSS)
