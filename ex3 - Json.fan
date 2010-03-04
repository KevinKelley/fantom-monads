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
  |State->Result| unit(Obj? v) {/*echo("->$v"); return*/ |State? st->Result|{ Result.Ok(v, st)} }

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
    //echo(p)
    return |State inp->Result|
    {
      //echo(inp)
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
  ** "plus" combinator that tries each parser in turn,
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
  ** "plus" combinator that tries each parser in turn,
  ** returning the first successful parse
  **
  |State->Result| choice(|State->Result|[] ps)
  {
    |State inp->Result| {
      rslt := ps.eachWhile | |State->Result| p ->Obj?| {
        //echo(inp);
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
    return bind(p, |Obj? x-> |State->Result| | { //echo("x: $x");
    return bind(q, |Obj? y-> |State->Result| | { //echo("y: $y");
    return unit([x,y])
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

  **
  **
  **
  |State->Result| sepby(|State->Result| p, |State->Result| sep) {
    or(sepby1(p, sep), unit([,]))
  }

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

  |State->Result| chainl(|State->Result| p, |State->Result| op, Obj? a) {
    or(chainl1(p, op), unit(a))
  }
  |State->Result| chainr(|State->Result| p, |State->Result| op, Obj? a) {
    or(chainr1(p, op), unit(a))
  }

  |State->Result| chainl1(|State->Result| p, |State->Result| op) {
    |Obj? -> |State->Result| |? rest
    rest = |Obj? x -> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind( p, |Obj? y-> |State->Result| | {
            rest("($f $x,$y)")
          })}),
          unit(x) )
    }
    return bind(p, |Obj? x-> |State->Result| | {
      rest(x)
    })
  }
  |State->Result| chainleft(|State->Result| p, |State->Result| op) {
    |Obj? -> |State->Result| |? rest  // forward decl, so we can recurse
    rest = |Obj? x -> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind( p, |Obj? y-> |State->Result| | {
            func := f as |Int,Int->Int|     // typecheck
            return rest(func.call(x,y))
          })}),
          unit(x) )
    }
    return bind(p, |Obj? x-> |State->Result| | {
      rest(x)
    })
  }


  |State->Result| chainr1(|State->Result| p, |State->Result| op) {
    bind(p, |Obj? x-> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind(chainr1(p, op), |Obj? y-> |State->Result| | {
            unit("($f $x,$y)")
          })}),
          unit(x) )
    })
  }
  |State->Result| chainright(|State->Result| p, |State->Result| op) {
    bind(p, |Obj? x-> |State->Result| | {
      or( bind(op, |Obj? f-> |State->Result| | {
          bind(chainright(p, op), |Obj? y-> |State->Result| | {
            func := f as |Int,Int->Int|     // typecheck
            return unit(func.call(x,y))
          })}),
          unit(x) )
    })
  }


  **
  ** parse a bracketed expression, returning the parse
  ** being bracketed.
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
}

  **
  ** Parser monad that recognizes Json (json.org) grammar (assuming no extraneous whitespace)
  **
  const class JsonParser : ParserMonad
  {
    // parser-func generator methods for Json grammar
    |State->Result| object  () { bracket(char('{'), members, char('}')) }
    |State->Result| members () { sepby(pair, char(',')) }
    |State->Result| pair    () { seq(str, seq(char(':'), value)) }
    |State->Result| array   () { bracket(char('['), elements, char(']')) }
    |State->Result| elements() { sepby(value, char(',')) }
    |State->Result| str     () { bracket(char('"'), many(strchar), char('"')) }
    |State->Result| strchar () { or(nonCtrl, escaped) }
    |State->Result| nonCtrl () { satisfy(|Int c->Bool|{!(c=='"' || c=='\\' || c<' ')}) }
    |State->Result| escaped () { seq(char('\\'), escChar) }
    |State->Result| escChar () { or(oneOf("\"\\/bfnrt"), seq(char('u'), hex4)) }
    |State->Result| number  () { seq(int, seq(fracOpt, expOpt)) }
    |State->Result| int     () { seq( signOpt, or(char('0'), seq(nonzero,digits)) ) }
    |State->Result| fracOpt () { or(seq(char('.'), digits), nothing) }
    |State->Result| expOpt  () { or(seq(e, digits) ,nothing) }
    |State->Result| digits  () { many(digit) }
    |State->Result| hex4    () { seq(seq(seq(hexdigit,hexdigit),hexdigit),hexdigit) }
    |State->Result| hexdigit() { oneOf("0123456789abcdefABCDEF") }
    |State->Result| digit   () { satisfy(|Int c->Bool|{('0'..'9').contains(c)}) }
    |State->Result| nonzero () { satisfy(|Int c->Bool|{('1'..'9').contains(c)}) }
    |State->Result| signOpt () { or(char('-'), nothing) }
    |State->Result| nothing () { unit("") }
    ** eN, e+N, e-N, EN, E+N, E-N all good; this parses the "e" and optional sign
    |State->Result| e() { seq(oneOf("eE"), or(oneOf("+-"), nothing)) }

    // generator-methods syntax (above) is convenient, but you have to break the
    // mutual recursion somewhere.  So 'value' will, instead of immediately creating
    // a parser, will instead create a closure that when evaluated during
    // parsing, will create a parser and then call it.
    //
    // Mutual recursion is fine, during a parse, because we're pretty sure that
    // the input will terminate eventually, no matter how deep the nested objects
    // go.  The problem is just in trying to pre-declare the parser structure:
    // without this change, it's trying to build an infinite-capacity parser
    // before even looking at the input.
    /*const |State->Result| value := |State inp->Result| {
      or(str,
      or(number,
      or(object,
      or(array,
      or(keyword("true"),
      or(keyword("false"),
         keyword("null")
      ))))))
      .call(inp)
    }*/
    const |State->Result| value := |State inp->Result| {
      choice([
        str,
        number,
        object,
        array,
        keyword("true"),
        keyword("false"),
        keyword("null")
      ]).call(inp)
    }

    |State->Result| item() {
      |State in->Result| {
        if (in.empty) return Result.Error(in)
        char := in.remaining[0] // grab any char
        state := in.advance(1)  // move state past it
        return Result.Ok(char.toChar, state) // return char and state
      }
    }

    ** parse any single character that satisfies the test predicate
    |State->Result| satisfy(|Int->Bool| test) {
      bind(item, |Str x-> |State->Result| | {
        (test(x[0])) ? unit(x) : zero
      })
    }
    |State->Result|  oneOf(Str cs) { satisfy(|Int c->Bool|{ cs.any|Int ch->Bool|{c==ch}}) }
    |State->Result| noneOf(Str cs) { satisfy(|Int c->Bool|{!cs.any|Int ch->Bool|{c==ch}}) }
    |State->Result|   char(Int ch) { satisfy(|Int c->Bool|{ch == c}) }

    |State->Result| keyword(Str s) {
      (s.isEmpty)
        ? unit("")
        : seq(char(s[0]), keyword(s.slice(1..-1)))
    }


    Void main() {
      echo(str.call(State("\"a\"")))
      echo(number.call(State("123")))
      echo(escaped.call(State("\\uabcd123"))) // parse the unicode, ignore the 123
      echo(pair.call(State("\"a\":123")))
      echo(sepby(number, char(',')).call(State("1,2,3")))
      echo(many(bracket(char('['), sepby(number, char(',')), char(']'))).call(State("[1,2,3]")))
      echo(array.call(State("[1,2,3]")))
      echo(object.call(State("""{"a":[1,2,3]}""")))
      echo(object.call(State("""{"id":12.3,"ints":[1,2,3],"value":456e8}""")))
      echo(object.call(State("""{"ident":123,"value":-456e8}""")))
    }
  }