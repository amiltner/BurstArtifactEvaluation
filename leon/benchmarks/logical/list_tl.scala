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
  
def list_tl(xs: NatList): NatList = { choose { (out:NatList) => 

   xs match {
    case Nil => out == Nil
    case Cons(h1,t1) => out == t1
    }

} }

}