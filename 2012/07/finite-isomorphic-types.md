# WORK IN PROGRESS (please do not link to this)

# Finite Isomorphic Types

## Background

My interest in isomorphic types all started after reading a somewhat unrelated but enlightening little [Reddit comment](http://www.reddit.com/r/types/comments/qeox7/decidable_equality_in_agda/c3xbj6b) by [Conor McBride](https://personal.cis.strath.ac.uk/conor.mcbride/).  He describes how to create a small universe capable of representing the standard non-dependent algebraic types we all know and love. A nice benefit is that you can write functions that pattern match on the codes of the universe that work for any representable type (i.e. perform generic programming). What this allows you to do is come up with your own incantations of things that `deriving` would give you in Haskell. For example, Conor gives a generic equality (`Eq`), but you are free to define whatever comes to mind like `Enum`, `Ord`, etc. The real excitement comes from imagining a language whose own type system is bootstrapped on such a universe (ala [The Gentle Art of Levitation](https://personal.cis.strath.ac.uk/pierreevariste.dagand/papers/levitation.pdf)). Here you would no longer be forced into the [di]satisfaction provided by `deriving` mechanisms that come with a given compiler. Instead, you could write your own generic programs in libraries over the "builtin" universe of codes and live happily ever after.

This led me to think about making one such generic function be a transformation from one isomorphic type to another. You've likely heard of algebraic data types in functional programming. The "algebraic" part is inspired by the properties that arise when considering the types `⊤` (unit), `⊥` (bottom), `⊎` (disjoint union), and `×` (cartesian product) as their familiar numeric brethren `1` (one), `0` (zero), `+` (addition), and `*` (multiplication). If you haven't seen this before, this [Lab49 post](http://blog.lab49.com/archives/3011) explains it well to a non-expert audience.

The interesting bit is that at least in this finite universe (no type recursion / `μ`), two given types are isomorphic if and only if the evaluation/simplification of their numeric counterpart reduce to equal numbers. The affect that this has is that pairs of types such as `(⊤ ⊎ ⊤) ⊎ ⊤` & `⊤ ⊎ (⊤ ⊎ ⊤)`, or `⊥ × ⊤` & `⊥` are isomorphic (i.e. we can define mutually inverse functions that convert a value of one type to a value of the other type). In general this happens because both universes described are commutative semigroups; so you get isomorphisms that correspond with familiar numeric properties like the associativity of addition, one with addition acting as an identity, zero with multiplication acting as an annihilator, etc. These kinds of isomorphisms are well known and [Robert Di Cosmo](http://www.dicosmo.org/) has even written a book called [Isomorphisms of Types](http://books.google.com/books/about/Isomorphisms_of_Types.html?id=cdJZRjIxavwC) about them. For more information, you can also read about [Tarski's high school algebra problem](http://en.wikipedia.org/wiki/Tarski's_high_school_algebra_problem). Yet another (albeit this time model theoretic) way to think about it is that two types are isomorphic if and only if their two numerical versions are isomorphic as objects in the category of finite sets (this and the relation to Tarski's problem is covered at the beginning of Di Cosmo's book).

## Denotational Semantics

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

Note that we have also added a `→` (function type), which corresponds to `^` (exponentiation). Using this, another example of an isomorphism is `Three × Three` & `Two → Three` (where constants like `Two` are just shorthand for `⊤ ⊎ ⊤`, etc.) This is because `Three × Three` evaluates as `3 * 3` and `Two → Three` as `3^2`, which both normalize to `9`.

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

While either of these examples would work, requiring an extra explicit proof parameter feels like a burden and is not in the spirit of correct-by-construction programming. When writing proofs / total functions in a language like Agda, you tend to get simpler definitions when implicitly enforcing equality constraints by reusing variables in a dependent type signature. Plus, we started out with such a beautiful denotational semantics, why ruin it with post-hoc reasoning? What we really want is a type signature like this:

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

## Type Coercion

Now that we have a good looking type, we should begin thinking about how we will provably cross the chasm between two isomorphic types. As mentioned earlier, isomorphism occurs when it exists between objects in the category of sets. We can use this as inspiration for our plan to convert values. Namely, we will have one function that injects values of `Type n` into their corresponding `Fin n` (the type of finite sets), and another function which brings a `Fin n` back to the world of `Type n`'s. It's worth noting that when writing these functions we get to reuse the technique of sharing our implicit `n` in the type signature without any other explicit proof that a `Type` and `Fin` are somehow related.

Another [un]intended side effect is that once such a bijection between types and finite sets has been established, we can reuse any (and there are many) functions previously defined for `Fin`! For example, equality of finite sets, enumeration of all possible values in a finite set, orderings between finite sets... essentially our familiar `Eq`, `Enum`, and `Ord`deriving mechanisms from Haskell but defined in user land and accompanied by proofs. This means by the end of our journey we will have for `Type` the deriving functions `Iso`, `Eq`, `Enum`, `Ord` and more (where more is whatever you are capable of defining)!

### Technical Digression

As a minor technical detail, we will change notation from `El` (element of the universe) as our interpretation function to the more familiar semantics brackets `⟦_⟧`. The real motivation behind this is to prevent the functional definition of `El` from expanding (in places we don't want it to, like when appealing to an inductive hypothesis via recursion) as we pattern match on its domain. This is accomplished by hiding our functional definition inside of a concrete data type with a single constructor. Also of note is mutually defining this new type, so that `El` may recurse with it (yet another method to make inductive steps of proofs go through more elegantly). Also please excuse my omission of `→`, everything still works when it is included but I don't have the proof cases for it that appear later in the post.

```haskell
El : ∀ {n} → Type n → Set
data ⟦_⟧ {n} (F : Type n) : Set

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = ⟦ S ⟧ ⊎ ⟦ T ⟧
El (S `× T) = ⟦ S ⟧ × ⟦ T ⟧

data ⟦_⟧ {n} F where
  [_] : El F → ⟦ F ⟧
```

### Back To Regularly Scheduled Programming

```haskell
postulate
  inject+ : ∀ {m} n → Fin m → Fin (m + n)
  raise : ∀ {m} n → Fin m → Fin (n + m)
  concat : ∀ {m n} → Fin m → Fin n → Fin (m * n)

toFin : ∀ {n} {F : Type n} → ⟦ F ⟧ → Fin n
toFin {F = `⊥} [ () ]
toFin {F = `⊤} [ tt ] = zero
toFin {F = S `⊎ T} [ inj₁ a ] = inject+ _ (toFin a)
toFin {F = _`⊎_ {m = m} S T} [ inj₂ b ] = raise m (toFin b)
toFin {F = S `× T} [ a , b ] = concat (toFin a) (toFin b)
```

The `toFin` function allows us to transform a value of a type into into an element of a finite set of the same cardinality. Explaining it and subsequent functions in detail is beyond the scope of this post, but you can get a feel for how it operates (and/or look here for [the completed source](http://todo.com)). The disjoint union case translates a value to the world of finite sets where we raise a particularly positioned finite set element to a bigger finite set but still in the same position. In the finite set world, the cartesian product case combines two finite sets positions into a single one corresponding to their position in the multiplication of both set cardinalities.

```haskell
postulate
  case : ∀ {m} {n} → Fin (m + n) → Fin m ⊎ Fin n
  split : ∀ {m} {n} → Fin (m * n) → Fin m × Fin n

inject : ∀ {n} (F : Type n) → Fin n → ⟦ F ⟧
inject `⊥ ()
inject `⊤ i = [ tt ]
inject (S `⊎ T) i with case i
... | inj₁ j = [ inj₁ (inject S j) ]
... | inj₂ k = [ inj₂ (inject T k) ]
inject (S `× T) i with split i
... | j , k = [ (inject S j , inject T k) ]
```

Now going in the other direction, if we have a finite set element and a code for the type/shape we would like it to become, we can inject the element into the expected value. At this point I should mention that the traversal order of our tree-structured types that the isomorphic `toFin` and `inject` follow is arbitrary, and there are in fact several other isomorphisms we could choose to go through. The special thing about this isomorphism, is that it corresponds nicely with the pattern matching structure of other definitions (e.g. `+`, `*`, etc), so we get prettier proofs. The `case` and `split` functions are analogous to the previously seen `inject+`/`raise` and `concat`, merely in the other direction.

```haskell
lift : ∀ {m n} {S T : Type m} {U V : Type n} →
  (⟦ S ⟧ → ⟦ U ⟧) → ⟦ T ⟧ → ⟦ V ⟧
lift {m} {n} {S} {T} {U} {V} f t =
  inject V (toFin (f (inject S (toFin t))))

coerce : ∀ {n} {S T : Type n} → ⟦ S ⟧ → ⟦ T ⟧
coerce {S = S} s = lift (id {A = ⟦ S ⟧}) s
```

The magnificent moment has arrived, our desired `coerce` function! Coercion is in fact a special case of a more general definition that `lift`s functions with a different domain and codomain to functions defined on different types but whose cardinalities respectively match the original function. In particular, the special case is the lifting of the identity function `id`. `lift` uses our previously defined functions to `toFin` out of old types and `inject` into the desired new types.

## Proof

Now that we have a coercion function, it remains to be shown that its components `toFin` and `inject` are in fact mutually inverse. Below we will give the proof of one direction of the bijection law we wish to see hold.

```haskell
postulate
  case-raise : ∀ {n} m → (i : Fin n) → case {m = m} (raise m i) ≡ inj₂ i
  case-inject : ∀ {m} n → (i : Fin m) → case (inject+ n i) ≡ inj₁ i
  split-concat : ∀ {m} {n} → (i : Fin m) (j : Fin n) → split (concat i j) ≡ (i , j)

bijection₁ : ∀ {n} {S : Type n} (s : ⟦ S ⟧) → inject S (toFin s) ≡ s
bijection₁ {S = `⊥} [ () ]
bijection₁ {S = `⊤} [ tt ] = refl
bijection₁ {S = _`⊎_ {n = n} S T} [ inj₁ a ]
  with case-inject n (toFin a) | bijection₁ a
... | p | ih rewrite p | ih = refl
bijection₁ {S = _`⊎_ {m = m} S T} [ inj₂ b ]
  with case-raise m (toFin b) | bijection₁ b
... | p | ih rewrite p | ih = refl
bijection₁ {S = S `× T} [ (a , b) ]
  with split-concat (toFin a) (toFin b) | bijection₁ a | bijection₁ b
... | p | ih₁ | ih₂ rewrite p | ih₁ | ih₂ = refl
```
Thanks to our lemmas and careful attention to which definitions we pattern match on across several definitions, the `bijection₁` proof is reasonably tame. The proofs of the lemmas are also inductive and quite tidy.

## Deriving

We started this post with the connection to `deriving` generic functions as in Haskell, and now we are here at last. The `coerce` function that we already have corresponds to what you might call something like deriving `Iso` in a language limited to finte types.

```haskell
_≟_ : ∀ {n} {F : Type n} → Decidable {A = ⟦ F ⟧} _≡_
_≟_ {F = F} x y  with toFin x ≟f toFin y
... | no p = no (p ∘ cong toFin)
... | yes p with bijection₁ x | bijection₁ y | cong (inject F) p
... | a | b | c rewrite a | b = yes c

enum : ∀ {n} (F : Type n) → Vec ⟦ F ⟧ n
enum = tabulate ∘ inject
```

`≟` and `enum` correspond to deriving `Eq` and `Enum`. An equivalent for deriving `Ord` via making use of the function `compare` would be a bit more involved because it return an `Ordering` type defined on `Fin`'s, and I haven't gotten around to attempting it yet. However, do notice that our `≟` gives us a proof of equality (rather than a boolean predicate), `enum` is assured to give us a vector of values whose length match the number of inhabitants, and `Ord` would give us back a proof of why something is `less`, `equal`, or `greater` (just like the already defined `Fin` version in the Agda standard library).

### TODOS
* expand to dependent types
* link to copumpinks stackoverflow answer
* isomorphic types + curry howard = proofs 
* link to type-isomorphisms repo
* compare implicit approach to semiring solver + reflection
