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
  
def list_compress(xs: NatList): NatList = { choose { (out:NatList) =>

  def no_dupes(xs: NatList) : Boolean =
    xs match {
      case Nil =>
        true
      case Cons(h1,t) =>
        t match {
          case Nil => true
          case Cons(h2,t2) =>
            (h1 != h2) && no_dupes(t)
        }
    }

  def content(l: NatList): Set[Nat] = l match {
    case Nil => Set.empty[Nat]
    case Cons(i, t) => Set(i) ++ content(t)
  }

    no_dupes(out) && (content(xs) subsetOf content(out))
} }

}