# Finite Isomorphic Types

## WORK IN PROGRESS

My interest in isomorphic types all started after reading a somewhat unrelated but enlightening little [Reddit comment](http://www.reddit.com/r/types/comments/qeox7/decidable_equality_in_agda/c3xbj6b) by [Conor McBride](https://twitter.com/pigworker/).  He describes how to create a small universe capable of representing the standard non-dependent algebraic types we all know and love. A nice benefit is that you can write functions that pattern match on the codes of the universe that work for any representable type (i.e. perform generic programming). What this allows you to do is come up with your own incantations of things that `deriving` would give you in Haskell. For example, Conor gives a generic equality, but you are free to define whatever comes to mind like Enum, Ord, etc. The real excitement comes from imagining a language that is bootstrapped on such a universe (ala [The Gentle Art of Levitation](https://personal.cis.strath.ac.uk/pierreevariste.dagand/papers/levitation.pdf)). Here you would no longer be forced into the [di]satisfaction provided by `deriving` mechanisms that come with a given compiler. Instead, you could write your own generic programs in libraries over the "builtin" universe of codes and live happily ever after.

This led me to think about making one such generic function be a transformation from one isomorphic type to another. You've likely heard of algebraic data types in functional programming. The "algebraic" part is inspired by the properties that arise when considering the types `⊤` (unit), `⊥` (bottom), `⊎` (disjoint union), and `×` (cartesian product) as their familiar numeric brethren `1` (one), `0` (zero), `+` (addition), and `*` (multiplication). If you haven't seen this before, this [Lab49 post](http://blog.lab49.com/archives/3011) explains it well to a non-expert audience.

The interesting bit is that at least in this finite universe (no type recursion / `μ`), two given types are isomorphic if and only if the evaluation/simplification of their numeric counterpart reduce to equal numbers. The affect that this has is that pairs of types such as `(⊤ ⊎ ⊤) ⊎ ⊤` & `⊤ ⊎ (⊤ ⊎ ⊤)`, or `⊥ × ⊤` & `⊥` are isomorphic (i.e. we can define mutually inverse functions that convert a value of one type to a value of the other type). In general this happens because both universes described are commutative semigroups; so you get isomorphisms that correspond with familiar properties like the associativity of addition, one with addition acting as an identity, zero with multiplication acting as an annihilator, etc. These kinds of isomorphisms are well known and Robert Di Cosmo has even written a book called [Isomorphisms of Types](http://books.google.com/books/about/Isomorphisms_of_Types.html?id=cdJZRjIxavwC) about them. For more information, you can also read about [Tarski's high school algebra problem](http://en.wikipedia.org/wiki/Tarski's_high_school_algebra_problem). Yet another way to think about it is that two types are isomorphic if and only if their two numerical versions are isomorphic as objects in the category of finite sets (both this and the relation to Tarski's problem is covered at the beginning of Di Cosmo's book).


### TODOS
* expand to functions/exponentials
* expand to dependencies
* mention category
* link to copumpinks stackoverflow answer
* isomorphic types + curry howard = proofs 
* gist of abstract theory code + implicit/intentional type system
