import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def bool_impl(p: Boolean, q: Boolean): Boolean = { choose { (out:Boolean) => 

   if ((p == T) && (q == F))
   {
     out == F
   } else {
     out == T
   }

} }

}