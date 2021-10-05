import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class Cmp
case object LT extends Cmp
case object EQ extends Cmp
case object GT extends Cmp
  
def nat_compare(n1: Nat, n2: Nat): Cmp =
  n1 match {
    case Z =>
      n2 match {
        case Z    => EQ
        case S(_) => LT
      }
    case S(m1) =>
      n2 match {
        case Z     => GT
        case S(m2) => nat_compare(m1, m2)
      }
  }
  
def nat_max(xs: Nat,ys: Nat): Nat = { choose { (out:Nat) => 

    def nat_to_int(x: Nat): Int =
      x match {
        case Z => 0
        case S(m) => nat_to_int(m) + 1
      }

    (nat_to_int(out) >= nat_to_int(xs)) && (nat_to_int(out) >= nat_to_int(ys))

} }

}