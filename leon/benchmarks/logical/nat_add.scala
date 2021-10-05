import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
def nat_add(in1: Nat, in2: Nat): Nat = { choose { (out:Nat) => 

   def nat_to_int(x: Nat): Int =
  x match {
    case Z => 0
    case S(m) => nat_to_int(m) + 1
  }

    (nat_to_int(out) >= nat_to_int(in1)) && (nat_to_int(out) >= nat_to_int(in2)) &&
    ((in1 == S(S(Z)) && in2 == S(S(Z))) ==> (out == S(S(S(S(Z))))))

} }

}