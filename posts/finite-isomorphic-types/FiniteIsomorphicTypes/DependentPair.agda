open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module FiniteIsomorphicTypes.DependentPair where

∣Σ∣ : ∀ {n} {A : Set} → Vec A n → (A → ℕ) → ℕ
∣Σ∣ [] f = zero
∣Σ∣ (x ∷ xs) f = f x + ∣Σ∣ xs f

Σconcat : ∀ {n} {A : Set} {B : A → Set} →
  (f : A → ℕ) (xs : Vec A n) (g : (a : A) →
  Vec (B a) (f a)) →
  Vec (Σ A B) (∣Σ∣ xs f)
Σconcat f [] g = []
Σconcat f (x ∷ xs) g = map (_,_ x) (g x) ++ Σconcat f xs g

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ : (S T : Type) → Type
  `Σ : (S : Type)(T : El S → Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (`Σ S T) = Σ (El S) λ s → El (T s)

count : Type → ℕ
enum : (R : Type) → Vec (El R) (count R)

count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (`Σ S T) = ∣Σ∣ (enum S) (λ s → count (T s))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (`Σ S T) = Σconcat (λ s → count (T s)) (enum S) (λ s → enum (T s))

--------------------------------------------------------------------------------

`two : Type
`two = `⊤ `⊎ `⊤

`three : Type
`three = `⊤ `⊎ `two

`four : Type
`four = `⊤ `⊎ `three

`square : El `four → Type
`square (inj₁ tt) = `⊥ `× `⊥
`square (inj₂ (inj₁ tt)) = `⊤ `× `⊤
`square (inj₂ (inj₂ (inj₁ tt))) = `two `× `two
`square (inj₂ (inj₂ (inj₂ tt))) = `three `× `three

`sum-of-squares : Type
`sum-of-squares = `Σ `four `square

`even : El `four → Type
`even (inj₁ tt) = `⊤
`even (inj₂ (inj₁ tt)) = `⊥
`even (inj₂ (inj₂ (inj₁ tt))) = `⊤
`even (inj₂ (inj₂ (inj₂ tt))) = `⊥

`∃even : Type
`∃even = `Σ `four `even
