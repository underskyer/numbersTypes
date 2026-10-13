package numberTypes

object sigmaPi:

  type `∑₀` = [F[_]] =>> F[Any] // теряется сведение о типе
  type Σᴄʜɪʀᴄʜ = [F[_]] =>> [Y] => ([X] => F[X] => Y) => Y

  enum ∑[G[_ <: Singleton]]: // Σɪɴᴅ
    case In[F[_], A <: Singleton](fa: F[A], tag: A) extends ∑[F]

  inline def in[F[_], A <: Singleton : ValueOf as a](fa: F[A]) =
    ∑.In[F, A](fa, a.value)

  trait Σᴏᴏᴘ[F[_]]:
    type A
    val fa: F[A]


  type ∏ = [F[_]] =>> [A] => () => F[A]
  extension [F[_]](pif: ∏[F])
    inline def apply[A] = pif[A]()


  object test:
    println()
    println("ends test:")

    val optUsage: [X] => Option[X] => String =
      [X] => x => x.map(_.asInstanceOf[Matchable]).fold("???"): // .map(_.asInstanceOf[Matchable])
        case str: String => "Str " + str
        case int: Int => "Int " + int
        case x => "??? " + x


    val d: Σᴄʜɪʀᴄʜ[Option] = [_] => x => x(Some(42))
    val dd = d(optUsage)
    println("∑: " + dd)

//    val dSS: ∑[Option] = in(Some(42))(using ValueOf[Int](24))
//    val ddSS = dSS match {
//      case ∑.In(fa, _) => optUsage(fa)
//    }
//    println("∑∑: " + ddSS)

    val dSSS: Σᴏᴏᴘ[Option] = new:
      type A = Int
      val fa = Some(42)
    val ddSSS = optUsage(dSSS.fa)
    println("∑∑∑: " + ddSSS)

    val ll: ∏[Option] = [A] => () => None
    println("∏ " + ll[String]())


