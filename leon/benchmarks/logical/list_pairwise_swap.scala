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
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
def list_pairwise_swap(xs: NatList): NatList = { choose { (out:NatList) => 

  xs match {
    case Nil => out == Nil
    case Cons(h1,t1) =>
      t1 match {
        case Nil => out == Nil
        case Cons(h2,t2) =>
          t2 match {
            case Nil => out == Cons(h2,Cons(h1,Nil))
            case Cons(h3,t3) =>
              t3 match {
                case Nil => out == Nil
                case Cons(h4,t4) =>
                  t4 match {
                    case Nil => out == Cons(h2,Cons(h1,Cons(h4,Cons(h3,Nil))))
                    case Cons(h5,t5) => true
                  }
              }
          }
      }
  }

} }

}