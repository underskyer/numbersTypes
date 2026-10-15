package numberTypes

object piTypes:

  // Класс-оболочка (по желанию, для явного именования типа)
  type ∏[Index, F[_ <: Index]] = (i: Index) => F[i.type]

  // Настоящий Пи-тип на уровне типов (принимает тип I и возвращает F[I])
  type Π[Index, F[_ <: Index]] = [I <: Index] =>> F[I]


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


  object testPiType:
    sealed trait Role
    final class Admin extends Role
    final class User  extends Role

    // Семейство типов (B(x)), сопоставляющее Role с типом прав
    type Permissions[R <: Role] = R match
      case Admin => List[String]
      case User => String

    // Демонстрация работы: компилятор строго проверяет соответствие типов
    val adminPerms: Π[Role, Permissions][Admin] = List("delete_user", "ban")
    val userPerms:  Π[Role, Permissions][User]  = "read_only"

    // Ошибка компиляции (Type Mismatch):
    // val wrong: PiType[Role, Permissions][Admin] = "just a string"
  end testPiType

