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
  
def list_length(xs: NatList): Nat = { choose { (out:Nat) => 

   xs match {
    case Nil => out == Z
    case Cons(h1,t1) => t1 match {
                    case Nil => out == S(Z)
                    case Cons(h2,t2) => t2 match {
                                    case Nil => out == S(S(Z))
                                    case Cons(h3,t3) => true
                                    }
                    }
     }

} }

}