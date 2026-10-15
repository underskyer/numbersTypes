package numberTypes

import numberTypes.sigmaPi.*
import numberTypes.indNatural.*

import scala.compiletime.{erasedValue, summonInline}

object finit:

  enum Nat:
    case Zero            extends Nat
    case Succ[Prev <: Nat](prev: Prev) extends Nat

  import Nat.*

  type Fin[N <: Nat] = N match
    case Nat.Zero.type => Nothing
    case Succ[prev] => prev | Fin[prev]



  object test:



    //summon[∑[[N <: Nat] =>> Rep[N][Mul[A]][EmptyTuple]] =:= Lst[Int]]

//    val empty: Lst[Int] =
//      in[[N <: Nat] =>> Rep[N][Mul[Int]][EmptyTuple], Nat, Nat.Zero.type](EmptyTuple)

//    val one: Lst[Int] =
//      ∑.In[[N <: Nat] =>> Rep[N][ *:[Int, *]][EmptyTuple], Nat.Succ[Nat.Zero.type]](
//        42 *: EmptyTuple, // fa: Rep[Succ[Zero]][Int *: _][EmptyTuple] = Int *: Rep[Zero][...] = Int *: EmptyTuple
//        Nat.Succ(Nat.Zero) // tag: Succ[Zero]
//      )


    type Three = Succ[Succ[Succ[Zero.type]]]

//    summonInline[Lst[Int] =:= Nothing]
//    summon[Rep[Three][Option][String] =:= Option[Option[Option[String]]]]

//    summon[(Int, None.type) <:< Lst[Int]]

