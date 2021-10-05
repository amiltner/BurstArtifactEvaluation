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
  
def list_hd(xs: NatList): Nat = { choose { (out:Nat) => 
    xs match {
        case Nil => out == Z
        case Cons(h,t) => out == h
    }

} }

}