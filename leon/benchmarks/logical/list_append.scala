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
  
def list_append(xs: NatList, ys: NatList): NatList = { choose { (out:NatList) => 
  
def len(l1: NatList): Int =
  l1 match {
    case Nil              => 0
    case Cons(head, tail) => 1+len(tail)
  }

  len(xs)+len(ys)==len(out)

} }

}