open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum hiding ( map )
open import Data.Product hiding ( map )
open import Data.Fin hiding ( _+_ )
open import Data.Vec
open import Relation.Binary.PropositionalEquality

module FiniteIsomorphicTypes.Function where

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

image : ∀ {n} {A : Set}
  (m : ℕ) → (Vec A n) →
  Vec (Vec A m) (n ^ m)
image zero xs = [] ∷ []
image (suc m) xs = concat (map (λ x → map (_∷_ x) (image m xs)) xs)

fconcat : ∀ {m n} → Fin m → Fin n → Fin (m * n)
fconcat {zero} {n} () j
fconcat {suc m} {zero} zero ()
fconcat {suc m} {suc n} zero j = inject+ _ j
fconcat {suc m} {n} (suc i) j = raise n (fconcat i j)

fimage : ∀ {m n} → Vec (Fin n) m → Fin (n ^ m)
fimage [] = zero
fimage (x ∷ xs) = fconcat x (fimage xs)

--------------------------------------------------------------------------------

data Type : Set
El : Type → Set

data Type where
  `⊥ `⊤ : Type
  _`⊎_ _`×_ _`→_ : (S T : Type) → Type

El `⊥ = ⊥
El `⊤ = ⊤
El (S `⊎ T) = El S ⊎ El T
El (S `× T) = El S × El T
El (S `→ T) = El S → El T

count : Type → ℕ
count `⊥ = 0
count `⊤ = 1
count (S `⊎ T) = count S + count T
count (S `× T) = count S * count T
count (S `→ T) = count T ^ count S

toFin : {R : Type} → El R → Fin (count R)
enum : (R : Type) → Vec (El R) (count R)

toFin {`⊥} ()
toFin {`⊤} tt = zero
toFin {S `⊎ T} (inj₁ x) = inject+ (count T) (toFin {S} x)
toFin {S `⊎ T} (inj₂ y) = raise (count S) (toFin {T} y)
toFin {S `× T} (x , y) = fconcat (toFin {S} x) (toFin {T} y)
toFin {S `→ T} f = fimage (map (toFin {T}) (map f (enum S)))

enum `⊥ = []
enum `⊤ = tt ∷ []
enum (S `⊎ T) = map inj₁ (enum S) ++ map inj₂ (enum T)
enum (S `× T) = concat (map (λ s → map (_,_ s) (enum T)) (enum S))
enum (S `→ T) = map (λ ts s → lookup (toFin {S} s) ts ) (image (count S) (enum T))


