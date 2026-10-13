package numberTypes

import numberTypes.recNatural.*

object finit:

  type Fin[T <: Nat] = T match
    case Zero => Nothing
    case Succ[p] => p | Fin[p] // либо сам p, либо меньше

end finit