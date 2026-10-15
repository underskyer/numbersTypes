import numberTypes.finit.Lst

import scala.compiletime.summonInline

val dff: Lst[Int] = null

summonInline[Lst[Int] =:= Nothing]
