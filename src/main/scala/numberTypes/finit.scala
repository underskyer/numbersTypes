package numberTypes

import numberTypes.recNatural.*

object finit:

  type Fin[N <: Nat] = N match
    case Fix(Nat.Zero.type   => Nothing
    case Nat.Succ[n] => Either[Unit, Fin[n]]