  const class State {
    const Int pos
    const Str remaining

    Bool empty() { remaining.isEmpty }

    new make(Str src, Int pos := 0) { this.pos = pos; remaining = src }
    This advance(Int n) { make((n<remaining.size)? remaining.slice(n..-1): "", pos+n) }
    override Str toStr() { "@$pos:'$remaining'" }
  }

  **
  ** Result is the result of a parse, combining a parsed value and
  ** the remaining state
  **
  abstract const class Result
  {
    Obj?    val() { (this as Ok)?.v }
    State? rest() { (this as Ok)?.s }

    Bool okay()     { this is Ok }
    Bool error()    { this is Error }

    **
    ** construct an 'Ok' result: a result value, and a snapshot of state
    **
    static Result Ok(Obj? a, State? s) { Ok(a,s) }

    **
    ** construct an 'Error' result with current state.
    **
    static Result Error(State at) { Error(at) }
  }
  **
  ** an Ok result holds a parse result value, and the new state
  **
  const class Ok : Result {
    const Obj? v;
    const State? s;
    new make(Obj? v, State s) {this.v=v; this.s=s}
    override Str toStr() { "Ok [$v, $s]" }
  }
  **
  ** an Error result holds the state at the point of the error.
  **
  const class Error : Result {
    const State at
    new make(State at) {this.at=at}
    override Str toStr() { "Error at $at" }
  }

** Parser a = Parser (State -> [a, State])
const mixin ParserMonad {

  **
  ** monadic unit: convert a basic value into a parser-monadic-function
  ** by wrapping it into a Result along with the then-current state.
  **
  |State->Result| unit(Obj? v) { |State? st->Result|{ Result.Ok(v, st)} }

  **
  ** monadic bind: bind a parser monad to a combining-function.
  ** return a bound computation which will run the monad in a
  ** current state; if the parser ('p') fails, immediately return
  ** the error result; otherwise, pass the resulting value to the
  ** combining-function to get a new monadic function, then call
  ** that second function with the new state.
  **
  |State->Result| bind(|State->Result| p, |Obj?-> |State->Result| | f)
  {
    return |State inp->Result|
    {
      r1  := p.call(inp)        // do computation m, get a result
      if (r1.error) return r1
      p2 := f.call(r1.val)      // feed the computed val to f,
                                // and get another parser, p2.
      return p2.call(r1.rest)   // do the new parse in the new state,
                                // and return its result
    }
  }

  **
  ** parser-deconstructor function: apply parser 'p' to state 'st',
  ** and return the result.
  **
  Result parse(|State->Result| p, State st) { (p)(st) }

  **
  ** return the parser monad's "zero" function: a parser that
  ** always immediately fails, capturing the state at the fail point.
  **
  |State->Result| zero() { |State inp->Result| {Result.Error(inp)} }

  **
  ** "plus" combinator that tries all parsers and returns all successes.
  ** 'plus' fails if no member succeeds.
  ** NOTE: this parser doesn't fit with the rest of these examples,
  ** which all deal with a single-success-or-fail model.
  **
  |State->Result| plus(|State->Result| p, |State->Result| q)
  {
    |State inp->Result| {
      rtn := [,]
      r1 := p(inp); if (r1.okay) rtn.add(r1)
      r2 := q(inp); if (r2.okay) rtn.add(r2)
      if (rtn.isEmpty)
        return Result.Error(inp)
      return Result.Ok(rtn, r1.okay? r1.rest: r2.rest)
    }
  }

  **
  ** "biased choice" combinator that tries each parser in turn,
  ** returning the first successful parse
  **
  |State->Result| or(|State->Result| p, |State->Result| q)
  {
    |State inp->Result| {
      r1 := p(inp); if (r1.okay) return r1
      r2 := q(inp); if (r2.okay) return r2
      return Result.Error(inp)
    }
  }

  **
  ** "biased choice" combinator that tries each parser in turn,
  ** returning the first successful parse
  **
  |State->Result| choice(|State->Result|[] ps)
  {
    |State inp->Result| {
      rslt := ps.eachWhile | |State->Result| p ->Obj?| {
        r := p(inp);
        if (r.okay) return r; return null
      }
      return rslt ?: Result.Error(inp)
    }
  }


  **
  ** return a parser that executes 'p', followed by 'q', and
  ** returns their results in a list.  Parse succeeds only if
  ** both 'p' and 'q' succeed.
  **
  |State->Result| seq(|State->Result| p, |State->Result| q) {
    bind(p, |Obj? x-> |State->Result| | {
    bind(q, |Obj? y-> |State->Result| | {
    unit([x,y])
    })})
  }

  **
  ** return a parser that executes 'p' as long as it succeeds,
  ** concatenating the results.
  **
  |State->Result| many(|State->Result| p) { or(many1(p), unit(null)) }

  **
  ** execute 'p' one or more times, concatenating the results,
  ** or fail if there is not at least one success.
  **
  |State->Result| many1(|State->Result| p) {
    bind(      p , |Obj? x-> |State->Result| | {
    bind( many(p), |Obj? y-> |State->Result| | {
      unit([x,y])
    })})
  }

  //|State->Result| chainl(|State->Result| p, |State->Result| op, Obj? a) {
  //  or(chainl1(p, op), unit(a))
  //}
  //|State->Result| chainr(|State->Result| p, |State->Result| op, Obj? a) {
  //  or(chainr1(p, op), unit(a))
  //}

  **
  ** expect 'op' to be a parser-monad with an action-func attached.
  ** Parse a "chain" of items matching 'p', leftmost first, separated
  ** by items that match 'op'.  The 'op' parser is assumed to return
  ** a Func (|Int,Int->Int|) as its result; this func is applied
  ** to combine the items in the chain.
  **
  |State->Result| chainl1(|State->Result| p, |State->Result| op) {
    |Obj? -> |State->Result| |? rest
    rest = |Obj? x -> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind( p, |Obj? y-> |State->Result| | {
            func := f as |Int,Int->Int|     // typecheck
            return rest(func.call(x,y))     // apply the action to the surrounding vals
          })}),
          unit(x) )
    }
    return bind(p, |Obj? x-> |State->Result| | {
      rest(x)
    })
  }

  **
  ** Like 'chainl1' but rightmost-first.
  **
  |State->Result| chainr1(|State->Result| p, |State->Result| op) {
    bind(p, |Obj? x-> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind(chainr1(p, op), |Obj? y-> |State->Result| | {
            func := f as |Int,Int->Int|     // typecheck
            return unit(func.call(x,y))     // apply the action to the surrounding vals
          })}),
        unit(x) )
    })
  }


  **
  ** parse a sequence of items that match 'p', separated by
  ** items that match 'sep' which are discarded.  Return empty
  ** list if there are no items.
  **
  |State->Result| sepby(|State->Result| p, |State->Result| sep) {
    or(sepby1(p, sep), unit([,]))
  }

  **
  ** parse a sequence of one or more items that match 'p',
  ** separated by items that match 'sep' which are discarded.
  **
  |State->Result| sepby1(|State->Result| p, |State->Result| sep) {
    bind(    p , |Obj? x-> |State->Result| | {
    bind( many(
                bind(sep, |Obj? _-> |State->Result| | {
                bind(  p, |Obj? b-> |State->Result| | {
                  unit(b)
                })})
              ), |Obj? y-> |State->Result| | {
      unit([x,y])
    })})
  }

  **
  ** parse a bracketed expression, returning the parse
  ** inside the parsed brackets.
  **
  |State->Result| bracket(|State->Result| open,
                          |State->Result| p,
                          |State->Result| close)
  {
    bind( open, |Obj? a -> |State->Result| | {
    bind(    p, |Obj? x -> |State->Result| | {
    bind(close, |Obj? b -> |State->Result| | {
      unit(x)
    })})})
  }


  **
  ** 'item' parses a single item from the input stream: this could be
  ** a token-grabber, if we want to use a lexical stage; but for many
  ** purposes we can build parsers all the way down to the individual
  ** character.
  **
  |State->Result| item() {
    |State in->Result| {
      if (in.empty) return Result.Error(in)
      char := in.remaining[0] // grab any char
      state := in.advance(1)  // move state past it
      return Result.Ok(char.toChar, state) // return char (as Str) and state
    }
  }

  **
  ** parse any single character that satisfies the test predicate
  **
  |State->Result| satisfy(|Int->Bool| test) {
    bind(item, |Str x-> |State->Result| | {
      (test(x[0])) ? unit(x) : zero
    })
  }

  /////////////////////////////////////////////////////////////////////
  // character parsers: match a single char
  |State->Result|   char(Int ch) { satisfy(|Int c->Bool|{ch == c}) }
  |State->Result|  oneOf(Str cs) { satisfy(|Int c->Bool|{ cs.any|Int ch->Bool|{c==ch}}) }
  |State->Result| noneOf(Str cs) { satisfy(|Int c->Bool|{!cs.any|Int ch->Bool|{c==ch}}) }
  |State->Result|  digit()       { satisfy(|Int c->Bool|{('0'..'9').contains(c)}) }
  |State->Result|  lower()       { satisfy(|Int c->Bool|{('a'..'z').contains(c)}) }
  |State->Result|  upper()       { satisfy(|Int c->Bool|{('A'..'Z').contains(c)}) }
  |State->Result| letter()       { or(lower,upper) }


  |State->Result|   word()       { many(letter) }
}

const class BitopsParser : ParserMonad
{

  const |State->Result| whitespace := oneOf(" \t\f\n\r")
  const |State->Result| hexdigit   := oneOf("0123456789abcdefABCDEF")
  const |State->Result| ident      := seq(letter, many(or(letter,digit)));

  |State->Result| paren(|State->Result| p) { bracket(char('('), p, char(')')) }

  |State->Result| string(Str s) {
    (s.isEmpty)
      ? unit("")
      : seq(char(s[0]), string(s.slice(1..-1)))
  }

  // to ignore white, wrap "atomic" parsers in these
  |State->Result| spaceOpt() { transformV(many(whitespace), |->Obj?|{null}) }

  |State->Result| token(|State->Result| p) {
    bind(       p, |Obj? x-> |State->Result| | {
    bind(many(whitespace), |Obj? _-> |State->Result| | {
      unit(x) // keep p's result, discard space's
    })})
  }
  |State->Result| symbol(Str s) { token(string(s)) }

  **
  ** apply a parser 'p' to a state, ignoring any leading
  ** whitespace.
  **
  Result apply(|State->Result| p, State st) {
    pp :=
    bind(spaceOpt, |Obj? _-> |State->Result| | {
    bind(       p, |Obj? x-> |State->Result| | {
      unit(x) // keep p's result, discard space's
    })})
    return parse(pp, st)
  }

  **
  ** parse and compute a natural number (sequence of decimal digits)
  **
  |State->Result| nat() {
    // working from the left...
    bind(chainl1( // first, make a transforming-parser from a digit parser and
                  // a function that converts a 1-char string to its int value...
                  transformV(digit, |Str o->Int| { ((Str)o)[0] - '0' }),
                  // then, bind with decimal-converter-fn to shift-and-add in the new value
                  decimalConv
                ), |Obj? x -> |State->Result| | {
    bind(spaceOpt, |Obj? sp-> |State->Result| | {
    unit(x)
    })})
  }
  //const |State->Result| nat2 :=
  //  bind(many1(digit), |Str ns -> |State->Result| | {
  //    unit(Int.fromStr(ns))
  //  });

  **
  ** value-combinator wrapped in monad for composition
  **
  const |State->Result| decimalConv := unit(|Int a,Int b->Int|{a*10+b});

  const |State->Result| expr := |State inp->Result| { or_Exp.call(inp) }
  |State->Result|    or_Exp() { chainl1(  and_Exp,    orOp) }
  |State->Result|   and_Exp() { chainl1(shift_Exp,   andOp) }
  |State->Result| shift_Exp() { chainl1(  add_Exp, shiftOp) }
  |State->Result|   add_Exp() { chainl1(  mul_Exp,   addOp) }
  |State->Result|   mul_Exp() { chainl1( atom_Exp,   mulOp) }
  |State->Result|  atom_Exp() { choice([nat, unary_Exp, paren(expr)]) }

  |State->Result| unary_Exp() {
    bind(unaryOp, |Obj? f -> |State->Result| | {
    bind(atom_Exp, |Obj? a -> |State->Result| | {
      func := f as |Int->Int|
      aint := a as Int
      return unit(func.call(aint))
    })})
  }

  |State->Result| orOp() {
    or(semantics(symbol("|"), |Int a,Int b->Int|{a. or(b)}),
       semantics(symbol("^"), |Int a,Int b->Int|{a.xor(b)}))
  }
  |State->Result| andOp() {
    semantics(symbol("&"), |Int a,Int b->Int|{a.and(b)})
  }
  |State->Result| shiftOp() {
    or(semantics(symbol("<<"), |Int a,Int b->Int|{a.shiftl(b)}),
       semantics(symbol(">>"), |Int a,Int b->Int|{a.shiftr(b)}))
  }
  |State->Result| addOp() {
    or(semantics(symbol("+"), |Int a,Int b->Int|{a.plus(b)}),
       semantics(symbol("-"), |Int a,Int b->Int|{a.minus(b)}))
  }
  |State->Result| mulOp() {
    or(semantics(symbol("*"), |Int a,Int b->Int|{a.mult(b)}),
       semantics(symbol("/"), |Int a,Int b->Int|{a.div(b)}))
  }
  |State->Result| unaryOp() {
    or(semantics(symbol("-"), |Int a->Int|{a.negate}),
       semantics(symbol("~"), |Int a->Int|{a.not}))
  }

  **
  ** transformV wraps a parser 'p' and a value-transformer func,
  ** returning a new parser that transforms the value when p succeeds.
  **
  |State->Result| transformV(|State->Result| p, |Obj?->Obj?| transform) {
    bind(p, |Obj? v-> |State->Result| | { unit(transform(v)) })
  }
  **
  ** 'semantics' binds a semantic action of some sort to a parser func,
  ** creating a new parser that, when it succeeds, yields the action
  ** as its value. Applying the action to the proper values
  ** is handled for example by the chainX1 parsers, which apply
  ** the action to the values parsed around it; or for ex., by
  ** unary_Exp, which applies the function associated with a unaryOp
  ** to the expression that follows it.
  **
  |State->Result| semantics(|State->Result| p, Func act) {
    bind(p, |Obj? -> |State->Result| | { unit(act) })
  }

  Void main() {
    echo(apply(expr, State("2+3*4+5")))           // 19
    echo(apply(expr, State("2 + 3 * - 4 + 5")))   // -5
    echo(apply(expr, State(" 2 + (1 ^ 15) ")))    // 16
  }
}
