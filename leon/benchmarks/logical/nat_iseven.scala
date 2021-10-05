import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def nat_iseven(n: Nat): Boolean = { choose { (out:Boolean) => 

   n match {
    case Z => out == T
    case S(t1) => t1 match {
                    case Z => out == F
                    case S(t2) => t2 match {
                                    case Z => out == T
                                    case S(t3) => true
                                    }
                    }
     }

} }

}