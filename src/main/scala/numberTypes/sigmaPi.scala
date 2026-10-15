package numberTypes

import numberTypes.indNatural.Bool

object sigmaPi:


  type Σʙᴏᴜɴᴅ [IndexType, F[_ <: IndexType]] = F[IndexType]
  type Σᴄʜɪʀᴄʜ[IndexType, F[_ <: IndexType]] = [Y] => ([I <: IndexType] => F[I] => Y) => Y

  trait Σᴏᴏᴘ[IndexType, F[_ <: IndexType]]:
    type I <: IndexType // первая проекция
    val fi: F[I]        // вторая проекция

  enum ∑[IndexType, G[_ <: IndexType]]: // Σɪɴᴅ
    case In[I, F[_ <: I], i <: I](fi: F[i], index: i) extends ∑[I, F]

  inline def in[I, F[_ <: I], i <: I: ValueOf](fi: F[i]): ∑[I, F] =
    ∑.In[I, F, i](fi, summon[ValueOf[i]].value)



  type ∏ = [F[_]] =>> [A] => () => F[A]
  extension [F[_]](pif: ∏[F])
    inline def apply[A] = pif[A]()


  object test:
    println()
    println("sigma pi:")

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

    val dSSS: Σᴏᴏᴘ[Bool, Option] = new:
      type I = Bool
      val fi = Some(true)
    val ddSSS = optUsage(dSSS.fi)
    println("∑∑∑: " + ddSSS)

    val ll: ∏[Option] = [A] => () => None
    println("∏ " + ll[String]())


