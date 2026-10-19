package numberTypes

object piTypes:

  // ℿ
  type ∏[Index, F[_ <: Index]] = (i: Index) => F[i.type]
  type Π[Index, F[_ <: Index]] = [I <: Index] => () => F[I]

  extension [Index, F[_ <: Index]](f: Π[Index, F])
    def apply[I <: Index] = f[I]()


  object testPi:
    // Пример использования:
    // 1. Определяем семейство типов (GADT)
    sealed trait Shape

    case class Circle(radius: Double) extends Shape

    case class Square(side: Double) extends Shape

    // 2. Определяем тип контента F[_ <: Shape]
    type AreaResult[S <: Shape] = S match
      case Circle => Double
      case Square => Float

    // 3. Реализация Пи-функции
    val calculateArea: ∏[Shape, AreaResult] = (s: Shape) => s match
      case c: Circle => c.radius * c.radius * Math.PI
      case s: Square => (s.side * s.side).toFloat

    // Проверка типов компилятором:
    val circleArea: Double = calculateArea(Circle(5.0))
    val squareArea: Float = calculateArea(Square(4.0))

  end testPi


  object testPiIso:


    type ProdΠ[A, B] = ∏[𝔹, Pair[A, B]]
    def prodΠIso[A, B]: (A × B) ~ ProdΠ[A, B] = (
      forward = ab =>
        case _: false => ab._1
        case _: true  => ab._2,
      backward = p => p(false) -> p(true)
    )

    type Exp[A, B] = ∏[A, Const[B]]
    def expIso[A, B]: (A => B) ~ Exp[A, B] = (
      forward = identity,
      backward = f => f(_)
    )


    println("==================================================")
    println("                 testPiType                       ")
    println("==================================================")

  end testPiIso

