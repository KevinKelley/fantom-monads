
  mixin Monad {
    abstract Func unit(Obj? a)
    abstract Func bind(Func m, |Obj?->Func| f)

    virtual Func zero() { |->Obj?| {null} }
    virtual Func plus(Func p, Func q) {|->Obj?|{null}}

    // map :: (a -> b) -> (M a -> M b)
    // map f m = m * \a: unit (f a)
    virtual Func map(|Obj? -> Obj?| f, Func m) {
      bind(m, |Obj? a -> Func| {
        unit(f(a))
      })
    }

    // join :: M (M a) -> M a
    // join z = z * \m:m
    Func join(Func z) {
      bind(z, |Func m -> Func| { m })
    }

    // liftM2 :: Monad m => (a -> b -> c) -> m a -> m b -> m c
    Func lift(Func op, Func mx, Func my) {
      bind( mx, |x -> Func| {
      bind( my, |y -> Func| {
        unit( op(x,y) )
      })})
    }

    // id is the identity function: |Obj? x->Obj?| { x }
    // . is function composition: f . g :: f(g(x))
    // map id = id
    // map (f . g) = map f . map g
    // map f . unit = unit . f
    // map f . join = join . map (map f )
    // join . unit = id
    // join . map unit = id
    // join . map join = join . join
    // m * k = join (map k m)

    static Void main() {
      echo("\n ComputedList monad:")
      ComputedListMonad().test
      echo("\n PlainList monad:")
      PlainListMonad().test
    }
  }
  mixin IdentityMonad : Monad {
    override Func unit(Obj? a) { |->Obj?| {a} }
    override Func bind(Func m, |Obj?->Func| f) { |->Obj?| { f(m()).call } }
  }

  ** the monad here is "computations returning Obj?[]"
  class ComputedListMonad : IdentityMonad
  {
    List fmap(Func f, List m) { m.map|Obj v->List|{((Func)f(v))()} }

    List concat(List lists) {
      lists.reduce([,]) |List l, List? ea->List| {
        if (ea!=null) l.addAll(ea.exclude |Obj? v->Bool| {v==null})
        return l
      }
    }

    List concatMap(Func f, |->List| m) { concat(fmap(f, m())) }

    override Func unit(Obj? a) { |->Obj?[]| {[a]} }

    // (*) :: [a] -> (a -> [b]) -> [b]
    // [] * k = []
    // (a:x) * k = k a ++ (x * k)
    //override |->Obj?[]| bind(Func m, |Obj? -> |->Obj?[]| | f) {
    override Func bind(Func m, |Obj?->Func| f) {
      |->Obj?[]| {
        alist := m() as List
        return alist.reduce([,]) |List r, Obj a->Obj| { r.addAll(f(a)() as List) }
      }
    }

    Func bind2(Func m, Func f) { |->List| { concatMap(f, m) } }

    Func letters := |->List| { ('a'..'d').toList.map|Int c->Str|{ c.toChar } }
    Func digits  := |->List| { ('7'..'9').toList.map|Int c->Str|{ c.toChar } }

    Func odds  := |->List| { (0..2).toList.map|Int x->Int|{ x*2+1 } }
    Func evens := |->List| { (0..2).toList.map|Int x->Int|{ x*2   } }

    Func cross(Func f, Func g) {
      bind2(f, |Obj a-> |->Obj?[]| | {
      bind2(g, |Obj b-> |->Obj?[]| | {
        unit([a, b])
      })})
    }
    Func add(Func f, Func g) {
      bind2(f, |Obj a-> |->Obj?[]| | {
      bind2(g, |Obj b-> |->Obj?[]| | {
        unit((sum)(a,b))
      })})
    }
    Func sum := |Int a, Int b -> Int| { a + b }
    Func msum := |Func m1, Func m2 -> Func| { lift(sum, m1, m2) }

    // pyth = [(x,y,z) | x <- [1..20], y <- [x..20], z <- [y..20], x^2 + y^2 == z^2]
    ** find pythagorean triples (x^2 + y^2 = z^2)
    ** for x in f, y in g, z in h.
    Func pyth(Func f, Func g, Func h) {
      bind2(f, |Int x-> |->Obj?[]| | {
      bind2(g, |Int y-> |->Obj?[]| | {
      bind2(h, |Int z-> |->Obj?[]| | {
        (x*x + y*y == z*z) ? unit([x,y,z]) : zero
      })})})
    }

    Void test() {
      ex := letters
      echo(cross(letters, digits).call)
      echo(add(odds, evens).call)

      ints := |->Int[]| { (1..100).toList }

      echo(((msum)(odds, evens) as Func)())

      echo(pyth(ints,ints,ints).call)

      //echo(map(double, ex).call)
      //z := |->Func| { map(double, ex) }
      //echo(join(z) .call)
    }
  }

  ** monad is "Obj[]"
  class PlainListMonad
  {
    List fmap(Func f, List m) { m.map|Obj v->List|{f(v)} }

    List concat(List lists) { lists.reduce([,]) |List l, List ea->List| { l.addAll(ea) } }

    List unit(Obj v) { [v] }
    List bind2(List seq, |Obj->Obj[]| f) {
      cat:=[,];
      seq.each|v|{ os:=f(v); os.each|i|{cat.add(i)} };
      return cat
    }
    List bind(List m, Func f) { concat(fmap(f, m)) }

    List innerProduct(List list) {
      bind(           list,  |Int a ->List| {
      bind( (0..<a).toList,  |Int b ->List| {
      unit( a * b )
      })})
    }
    List crossProduct(List l1, List l2) {
      bind( l1,  |Obj a->List| {
      bind( l2,  |Obj b->List| {
      unit( [a,b] )
      })})
    }
    Void test() {
      echo(innerProduct((0..4).toList))
      echo(crossProduct((1..3).toList, "a b c".split))
    }
  }

