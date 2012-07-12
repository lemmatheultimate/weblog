# Finite Isomorphic Types

## WORK IN PROGRESS

My interest in isomorphic types all started after reading a somewhat unrelated but enlightening little [Reddit comment](http://www.reddit.com/r/types/comments/qeox7/decidable_equality_in_agda/c3xbj6b) by [Conor McBride](https://personal.cis.strath.ac.uk/conor.mcbride/).  He describes how to create a small universe capable of representing the standard non-dependent algebraic types we all know and love. A nice benefit is that you can write functions that pattern match on the codes of the universe that work for any representable type (i.e. perform generic programming). What this allows you to do is come up with your own incantations of things that `deriving` would give you in Haskell. For example, Conor gives a generic equality, but you are free to define whatever comes to mind like Enum, Ord, etc. The real excitement comes from imagining a language that is bootstrapped on such a universe (ala [The Gentle Art of Levitation](https://personal.cis.strath.ac.uk/pierreevariste.dagand/papers/levitation.pdf)). Here you would no longer be forced into the [di]satisfaction provided by `deriving` mechanisms that come with a given compiler. Instead, you could write your own generic programs in libraries over the "builtin" universe of codes and live happily ever after.

This led me to think about making one such generic function be a transformation from one isomorphic type to another. You've likely heard of algebraic data types in functional programming. The "algebraic" part is inspired by the properties that arise when considering the types `⊤` (unit), `⊥` (bottom), `⊎` (disjoint union), and `×` (cartesian product) as their familiar numeric brethren `1` (one), `0` (zero), `+` (addition), and `*` (multiplication). If you haven't seen this before, this [Lab49 post](http://blog.lab49.com/archives/3011) explains it well to a non-expert audience.

The interesting bit is that at least in this finite universe (no type recursion / `μ`), two given types are isomorphic if and only if the evaluation/simplification of their numeric counterpart reduce to equal numbers. The affect that this has is that pairs of types such as `(⊤ ⊎ ⊤) ⊎ ⊤` & `⊤ ⊎ (⊤ ⊎ ⊤)`, or `⊥ × ⊤` & `⊥` are isomorphic (i.e. we can define mutually inverse functions that convert a value of one type to a value of the other type). In general this happens because both universes described are commutative semigroups; so you get isomorphisms that correspond with familiar properties like the associativity of addition, one with addition acting as an identity, zero with multiplication acting as an annihilator, etc. These kinds of isomorphisms are well known and [Robert Di Cosmo](http://www.dicosmo.org/) has even written a book called [Isomorphisms of Types](http://books.google.com/books/about/Isomorphisms_of_Types.html?id=cdJZRjIxavwC) about them. For more information, you can also read about [Tarski's high school algebra problem](http://en.wikipedia.org/wiki/Tarski's_high_school_algebra_problem). Yet another (albeit this time model theoretic) way to think about it is that two types are isomorphic if and only if their two numerical versions are isomorphic as objects in the category of finite sets (this and the relation to Tarski's problem is covered at the beginning of Di Cosmo's book).

### The Meat

Now that we know that the isomorphisms described exist, we would like to have a constructive method for converting between values of isomorphic types. Let us start by recapping the finite universe of types that we are working with. The convention that we will be using for type codes is prefixing them with a backtick, for example the code for unit is ``⊤` while its interpretation is `⊤` (no backtick present).

```haskell
data Type : Set where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El : Type → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
```

Note that we have also added a `→` (function type), which corresponds with `^` (exponentiation). Using this, another example of an isomorphism is `Three × Three` & `Two → Three` (where constants like `Two` are just shorthand for `⊤ ⊎ ⊤`, etc.) This is because `Three × Three` evaluates as `3 * 3` and `Two → Three` as `3^2`, which both normalize to `9`.

Not surprisingly, we can define a function to `count` the number of inhabitants of a type.

```haskell
count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S
```

What we are really after is a static method for knowing when two given types are isomorphic, so we can write a total function that converts values between the types. The static "equality" will then act as a parameter to our coercion function whose "proof" we can use to restrict our definition to only the necessary isomorphic type cases.

A first attempt to define such a function might be as follows:

```haskell
coerce : {S T : Type} → El S → count S ≡ count T → El T
```

Or similarly using a more structurally defined equivalence relation:

```haskell
coerce : {S T : Type} → El S → S ≈ T → El T
```

While either of these examples would work, requiring an extra explicit proof parameter feels like a burden and not in the spirit of correct-by-construction programming. When writing proofs / total functions in a language like Agda, you tend to get simpler definitions when implicitly enforcing equality constraints by reusing type dependent variables in a type signature. Plus, we started out with such a beautiful denotational semantics, why ruin it with post-hoc reasoning? What we really want is a type signature like this:

```haskell
coerce : {n : ℕ} {S T : Type n} → El S → El T
```

Here a single natural number `n : ℕ` is implicitly shared between two codes of a family of types indexed by the natural numbers. As a result a separate explicit proof need not be supplied. How do we write such a type? We merely encode our `count` function into our previous denotational semantics.

```haskell
data Type : ℕ → Set where
  `⊥ : Type 0
  `⊤ : Type 1
  _`⊎_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m + n)
  _`×_ : ∀ {m n} (S : Type m) (T : Type n) → Type (m * n)
  _`→_ : ∀ {m n} (S : Type m) (T : Type n) → Type (n ^ m)

El : ∀ {n} → Type n → Set
El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T
```

### TODOS
* expand to dependencies
* link to copumpinks stackoverflow answer
* isomorphic types + curry howard = proofs 
* gist of abstract theory code + implicit/intentional type system
* compare implicit approach to semiring solver + reflection
