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

sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def list_stutter(l: NatList): NatList = { choose { (out:NatList) => 

   def len(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

   def double(x:Nat):Nat =
     x match {
       case Z => Z
       case S(n) => S(S(double(n)))
     }

   double(len(l))==len(out)

} }

}