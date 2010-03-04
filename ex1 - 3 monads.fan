/*The basic requirement
is that programs should form a category, and
the obvious choice for it is the Kleisli category for a
monad. [Moggi {Computational Lambda Calculus and Monads}]
*/
mixin Monad {
  abstract Func unit(Obj? a)
  abstract Func bind(Func m, |Obj?->Func| f)

  static Void main() {
    echo("\n Identity monad:")
    Expr.make.test
    echo("\n Exception monad:")
    ExceptionMonad.make.test
    echo("\n State monad:")
    StateMonad.make.test
    echo("\n Output monad:")
    OutputMonad.make.test
  }
}
mixin IdentityMonad : Monad {
  override Func unit(Obj? a) { |->Obj?| {a} }
  override Func bind(Func m, |Obj?->Func| f) { |->Obj?| { f(m()).call } }
}

class Expr : IdentityMonad
{
  Func Con(Int v) { unit(v) }
  Func Div(Func t, Func u) {
    bind(t, |Int a -> Func| {
    bind(u, |Int b -> Func| {
      unit(a/b)
    })})
  }
  Void test() {
    echo( Div(Div(Con(1972),Con(2)), Con(23)) .call)
  }
}

  class ExceptionMonad : IdentityMonad
  {
    Func raise(Err e) { |->Obj?| {e} }

    override Func bind(Func m, |Obj?->Func| f) {
      |->Obj?| { v := m(); if (v is Err) return v; return f(v).call }
    }

    Func Con(Int v) { unit(v) }
    Func Div(Func t, Func u) {
      bind(t, |Int a -> Func| {
      bind(u, |Int b -> Func| {
        if (b == 0) return raise(Err("divide by zero")); return unit(a/b)
      })})
    }
    Void test() {
      echo( Div(Div(Con(1972),Con(2)), Con(23)) .call)
      echo( Div(Con(1), Con(0)) .call)
    }
  }

** StateMonad is computations that take a State as input,
** and return the computation's result, paired with a new State
const class State {
  const Int count;
  private new make(Int c) { count=c }//Func? f:=null) { if (f!=null)f(this) }
  new def() : this.make(0) {}
  State inc() { make(count+1) }//{it.count=this.count+1} }
  override Str toStr() { "#$count" }
}
  class StateMonad : Monad
  {
    Func tick() { |State s->Obj?| {[null, s.inc]} }

    override Func unit(Obj? a) { |State s->Obj?| {[a,s]} } // return a and unchanged state

    //|State->Obj?| bind(|State->Obj?| m, |Obj? -> |State->Obj?| | f) {
    override Func bind(Func m, |Obj? -> Func| f) {
      |State x->Obj?| {
        mx := m(x) as Obj?[]
        a := mx[0]; y := mx[1]
        m2 := f(a)(y) as Obj?[]
        b := m2[0]; z := m2[1]
        return [b,z]
      }
    }
    Func Con(Int v) {
      bind(tick, | Int? -> |State->Obj?| | {
        unit(v)
      })
    }
    Func Div(Func t, Func u) {
      bind(   t, |Int a -> |State->Obj?| | { // val from computation t is bound to a
      bind(   u, |Int b -> |State->Obj?| | { // " " u " b
      bind(tick, |    _ -> |State->Obj?| | { // tick modifies state, doesn't produce a val
        unit(a/b)
      })})})
    }
    Void test() {
      init := State.def //{count=0}

      echo( Div(Div(Con(1972),Con(2)), Con(23)) .call(init))
    }
  }

  class OutputMonad : Monad
  {
    Func out(Str x) { |->Obj?| {[x, -1]} }

    Str line(Str t, Int n) { "eval($t) ==> $n\n" }

    override Func unit(Obj? a) { |->Obj?| {["", a]} }

    //|->Obj?| bind(|->Obj?| m, |Obj?-> |->Obj?| | f) {
    override Func bind(Func m, |Obj? -> Func| f) {
      |->Obj?| {
        mx := m() as Obj?[]
        y := mx[0] as Str; a := mx[1] as Int
        m2 := f(a)() as Obj?[]
        z := m2[0] as Str; b := m2[1] as Int
        return ["$y$z",b]
      }
    }

    Func Con(Int v) {
      bind(out(line("Con $v", v)), |Int -> |->Obj?| | {
        unit(v)
      })
    }
    Func Div(Func t, Func u) {
      bind( t, |Int a -> |->Obj?| | {
      bind( u, |Int b -> |->Obj?| | {
      bind(out(line("Div $a $b", a/b)),
               |Int   -> |->Obj?| | {
        unit(a/b)
      })})})
    }
    Void test() {
      echo( Div(Div(Con(1972),Con(2)), Con(23)) .call)
    }
  }
