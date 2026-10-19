package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ
import numberTypes.wellFounded.{Branches, PolynomialFunctor}

object mTrees:

  enum Σɢᴀᴅᴛ[IndexType, +G[_ <: IndexType]]: //
    case In[I, +F[_ <: I], i <: I](index: i, fi: F[i]) extends Σɢᴀᴅᴛ[I, F]

  type Branches[Index, F[_ <: Index], +Y] = [I <: Index] =>>
    (i: I) => F[i.type] => Y

  type PolynomialFunctor[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, Branches[Index, F, Y]]

  type Functor[F[+_]] = [A, B] => (A => B) => (F[A] => F[B])

  trait 𝛎[+F[+_]]:
    def out: F[𝛎[F]]

  object 𝛎:
    def unfold[F[+_]: Functor as fmap, S](f: Coalgebra[F][S]): S => 𝛎[F] =
      s => new:
        def out: F[𝛎[F]] = fmap(unfold(f))(f(s))

  type 𝕄[Index, F[_ <: Index]] = 𝛎[PolynomialFunctor[Index, F]]



  object 𝕄:

    // Конструктор (ко-интродукция): из «шапки» (index, branches) строим элемент ν
    def sup[Index, F[_ <: Index], I <: Index](
      i: I,
      br: Branches[Index, F, 𝕄[Index, F]][I]
    ): 𝕄[Index, F] =
      new 𝛎[PolynomialFunctor[Index, F]]:
        val out = Σɢᴀᴅᴛ.In[Index, Branches[Index, F, 𝕄[Index, F]], I](i, br)

    // Элиминатор (наблюдатель / ко-паттерн)
    def out[Index, F[_ <: Index]](m: 𝕄[Index, F]): PolynomialFunctor[Index, F][𝕄[Index, F]] =
      m.out

    // Коитерация (терминальность ν): анаморфизм из любого coalgebra
    def unfold[Index, F[_ <: Index], X](
      step: X => PolynomialFunctor[Index, F][X]
    ): X => 𝕄[Index, F] =
      lazy val go: X => 𝕄[Index, F] = step(_) match
        case Σɢᴀᴅᴛ.In(i, br) => sup[Index, F, i.type](i, (k: i.type) => (b: F[k.type]) => go(br(k)(b)))
      go


    def coind[Index, F[_ <: Index], S, P[_ <: S]](
      step: (s: S) => P[s.type] =>
        Σɢᴀᴅᴛ[Index, Branches[Index, F, Σɢᴀᴅᴛ[S, P]]]
    ): (s: S) => P[s.type] => 𝕄[Index, F] = ???

//    // коалгебра над состоянием (s, p)
//    val γ: Coalgebra[PolynomialFunctor[Index, F]][Σɢᴀᴅᴛ[S, [I <: S] =>> [i <: I] =>> P[i]]] =
//      case Σɢᴀᴅᴛ.In(s, p) =>
//        step(s)(p) match
//          case Σɢᴀᴅᴛ.In(i, fi) =>
//            Σɢᴀᴅᴛ.In(i, (a: F[i.type]) => fi(a))
//    // и развёртка:
//    (s, p) => 𝛎.unfold(γ)(Σɢᴀᴅᴛ.In(s, p))

//    def coind[Index, F[_ <: Index], X, P[_ <: X]](
//      step: (x: X) => P[x.type] => Σɢᴀᴅᴛ[Index, Branches[Index, F, Σɢᴀᴅᴛ[X, P]]]
//    ): (x: X) => P[x.type] => 𝕄[Index, F] =
//      (x: X) => (p: P[x.type]) =>
//        new 𝛎[PolynomialFunctor[Index, F]]:
//          def out = step(x)(p) match
//            case in @ Σɢᴀᴅᴛ.In(_, _) =>
//              in match
//                case Σɢᴀᴅᴛ.In(y, q) =>
//                  // здесь y уже имеет синглтон-тип y.typ e, и q : P[y.type]
//                  Σɢᴀᴅᴛ.In(in.index, (j: in.index.type) => (b: F[j.type]) =>
//                    val pair = next(j)(b)          // : ΣɢᴀᴅT[X, P]
//                    pair match
//                      case Σɢᴀᴅᴛ.In(y2, q2) =>      // y2 : X, q2 : P[y2.type]  ← уже согласовано
//                        coind(step)(y2)(q2)
//                  )
//asInstanceOf