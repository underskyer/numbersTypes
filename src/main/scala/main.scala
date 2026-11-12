import numberTypes.*
import numberTypes.inductor.*

@main
def main() =

  natural.test
  recNatural.test
  chirchNatural.test
  indNatural.test

  sigmaTypes.test
  //finit.test
  vec.test
  vec.test.flatteners
  natSigma.test
  natSigmaGADT.test
  natSigmaChirch.test
  natPathDep.test
  piTypes.testPiIso
  //recursor.test
  //natFixPathDep.test
  natWellFounded.test
//  mTrees.test
  natInductor.test
  natWellFoundedNew.test
  bTree.test

  identityType.test
  identityType.s1.test
  identityType.s1new.mobiusTest
  identityType.s1new.spiralTest
  identityType.s1new.pathDependentTest



