import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList

def len(xs: NatList): Int =
  xs match {
    case Nil => 0
    case Cons(h,t) => len(t) + 1
  }

def nat_to_int(x: Nat): Int =
  x match {
    case Z => 0
    case S(m) => nat_to_int(m) + 1
  }
  
def list_drop(xs: NatList, n: Nat): NatList = { choose { (out:NatList) => 

    def size = if (len(xs) < nat_to_int(n)) { 0 } else { len(xs) - nat_to_int(n) }

   (len(out) == size)

} }

}