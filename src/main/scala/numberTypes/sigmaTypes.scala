package numberTypes

object sigmaTypes:


  type Σʙᴏᴜɴᴅ [IndexType, F[_ <: IndexType]] = F[IndexType]

  type Σᴄʜɪʀᴄʜ[IndexType, F[_ <: IndexType]] = [Y] => ([I <: IndexType] => F[I] => Y) => Y

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

  enum Σɢᴀᴅᴛ[IndexType, +G[_ <: IndexType]]: //
    case In[I, +F[_ <: I], i <: I](index: i, fi: F[i]) extends Σɢᴀᴅᴛ[I, F]

  inline def inΣ[I, F[_ <: I], i <: I: ValueOf](fi: F[i]): Σɢᴀᴅᴛ[I, F] =
    Σɢᴀᴅᴛ.In[I, F, i](summon[ValueOf[i]].value, fi)

  trait ⅀[Index, F[_ <: Index]]:
    type I <: Index
    val index: I
    val value: F[index.type]

  final case class InΣ[Index, F[_ <: Index], J <: Index](index: J, value: F[index.type]) extends ⅀[Index, F]:
    type I = J

  //⅀
  type ∑ = Σɢᴀᴅᴛ


  object test:

    println()
    println("sigma pi:")

    type Sum[A, B] = ⅀[𝔹, Pair[A, B]]

    def sumIso[A, B]: (A + B) ~ Sum[A, B] = (
      forward = _.fold[Sum[A, B]](
        InΣ[𝔹, Pair[A, B], false](false, _),
        InΣ[𝔹, Pair[A, B], true](true, _)
      ),
      backward =
        case InΣ(false, a: A) => Left(a)
        case InΣ(true,  b: B) => Right(b)
    )

    val iso = sumIso[Int, String]
    println("sum iso left : " + iso.backward(iso.forward(Left[Int, String](42))))
    println("sum iso right: " + iso.backward(iso.forward(Right[Int, String]("str: 42"))))

    type ProdΣ[A, B] = ∑[A, Const[B]]
    def prodΣIso[A, B]: (A × B) ~ ProdΣ[A, B] = (
      forward = Σɢᴀᴅᴛ.In[A, Const[B], A].tupled,
      backward = { case Σɢᴀᴅᴛ.In(a: A, b: B) => a -> b }
    )


    val optUsage: [X] => Option[X] => String =
      [X] => x => x.map(_.asInstanceOf[Matchable]).fold("???"): // .map(_.asInstanceOf[Matchable])
        case str: String => "Str " + str
        case int: Int => "Int " + int
        case x => "??? " + x


    val d: Σᴄʜɪʀᴄʜ[𝔹, Option] = [_] => x => x(Some(true))
    val dd = d(optUsage)
    println("∑: " + dd)


