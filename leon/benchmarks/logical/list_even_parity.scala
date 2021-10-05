import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class BoolList
case class Cons(head: Boolean, tail: BoolList) extends BoolList
case object Nil extends BoolList

sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
def list_even_parity(xs: BoolList): Boolean = { choose { (out:Boolean) => 
    def len(xs: BoolList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

    def iseven(x: Nat): Boolean =
      x match {
        case Z => T
        case S(n) => n match {
                        case Z => F
                        case S(m) => iseven(m)
                    }
      }

    def only_trues(xs: BoolList) : BoolList =
      xs match {
        case Nil => Nil
        case Cons(h,t) =>
          h match {
            case F => only_trues(t)
            case T => Cons(h,only_trues(t))
          }
      }

    iseven(len(only_trues(xs))) match {
      case F => out == F
      case T => out == T
    }

} }

}