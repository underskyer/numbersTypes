package numberTypes

import numberTypes.sigmaTypes.Σɢᴀᴅᴛ

object wellFounded:


  type PolynomialFunctor[Index, F[_ <: Index]] =
    [Y] =>> Σɢᴀᴅᴛ[Index, [I <: Index] =>> (i: I) => F[i.type] => Y]

  type W[Index, F[_ <: Index]] = μᵢ[PolynomialFunctor[Index, F]]

  object test:


  end test