import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def bool_impl(p: Boolean, q: Boolean): Boolean = { choose { (out:Boolean) => 

   ((p != q) ==> (out == T)) && ((out == T) ==> (p != q))

} }

}