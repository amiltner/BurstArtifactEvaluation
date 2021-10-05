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

def zero(n:Nat) : Nat = Z

def inc(n:Nat) : Nat = S(n)

def list_map(f:Nat=>Nat,xs: NatList): NatList = { choose { (out:NatList) => 

  def plus(n1:Nat,n2:Nat):Nat =
    n1 match {
      case Z => n2
      case S(n1p) => S(plus(n1p,n2))
    }

  def sum(nl:NatList):Nat =
    nl match {
      case Nil => Z
      case Cons(h,t) => plus(h,(sum(t)))
    }

  def size(l:NatList):Nat =
    l match {
      case Nil => Z
      case Cons(_,t) => S(size(t))
    }

  def is_zero(l:NatList) : Boolean =
    l match {
      case Nil => true
      case Cons(h,t) => (h==Z) && (is_zero(t))
    }

    ((size(out)) == (size(xs))) &&
    (if (f == ((x:Nat) => zero(x))) { is_zero(out) } else { if (f == ((x:Nat) => inc(x))) { sum(out)==plus(sum(xs),size(xs)) } else {true} })

} }

}