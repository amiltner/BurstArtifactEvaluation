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

def is_even(n:Nat) : Boolean =
  n match {
    case Z => T
    case S(Z) => F
    case S(S(np)) => is_even(np)
  }

def is_nonzero(n:Nat) : Boolean =
  n match {
    case Z => F
    case S(_) => T
  }

def list_filter(f:Nat=>Boolean,xs: NatList): NatList = { choose { (out:NatList) => 

  def for_all(f:Nat=>Boolean,n2:NatList):Boolean =
    n2 match {
      case Nil => T
      case Cons(h,t) =>
        f(h) match {
          case T => for_all(f,n2)
          case F => F
        }
    }

    (for_all(f,out) == T) && ((for_all(f,xs) == T) ==> (xs == out))

} }

}