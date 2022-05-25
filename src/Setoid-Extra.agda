------------------------------------------------------------
-- Nominal Sets
--
--
-- Extensional equality. Predicates on Setoids. Indexed Setoids.
--
-- Taken from the Universal Algebra Library:
--   https://github.com/miguelpagano/universal-algebra
------------------------------------------------------------
module Setoid-Extra where

open import Level renaming (suc to lsuc ; zero to lzero)

open import Data.Empty
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum hiding (map)
open import Data.Unit
open import Function as F hiding (_⟶_;_↔_)
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as EqR
import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary


module Inequality {ℓ₁ ℓ₂} (A : Setoid ℓ₁ ℓ₂) where
  open Setoid A
  ≉-sym : ∀ {a b} → a ≉ b → b ≉ a
  ≉-sym a≠b b=a = contradiction (sym b=a) a≠b

  ≉-resp-≈₁ : ∀ {a b c} → a ≈ b → b ≉ c → a ≉ c
  ≉-resp-≈₁ a=b b≠c a=c = contradiction (trans (sym a=b) a=c) b≠c

  ≉-resp-≈₂ : ∀ {a b c} → b ≈ c → a ≉ b → a ≉ c
  ≉-resp-≈₂ b=c a≠b a=c = contradiction (trans a=c (sym b=c)) a≠b

{- Carrier -}
∥_∥ : ∀ {ℓ₁ ℓ₂} → (Setoid ℓ₁ ℓ₂) → Set ℓ₁
∥ S ∥ =  Carrier
  where open Setoid S

open Setoid
-- Extensional Equality
module ExtEq {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄) where
  private
    _≈B_ : _
    _≈B_ = Setoid._≈_ B

    _≈A_ : _
    _≈A_ = Setoid._≈_ A

  open Func
  _≈→_ : Rel (Func A B) _
  F ≈→ G  = (a : ∥ A ∥) → (f F a) ≈B (f G a)

  ext-preserves-≈ : ∀ {a a' F G} → F ≈→ G → a ≈A a' → (f F a) ≈B (f G a')
  ext-preserves-≈ {a' = a'} {F} f≈g a≈a' = trans B (cong F a≈a') (f≈g a')

  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = record
    { refl = λ {F} a → refl B {f F a}
    ; sym = λ p → sym B ∘ p
    ; trans = λ p q a → trans B (p a) (q a)
    }

  _⇒ₛ_ : Setoid (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₄)
  Carrier (_⇒ₛ_) = Func A B
  _≈_ (_⇒ₛ_) = _≈→_
  isEquivalence (_⇒ₛ_) = Equiv≈→


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (S : Setoid ℓ₁ ℓ₂)
          {P : Pred ∥ S ∥ ℓ₃} {Q : Pred ∥ S ∥ ℓ₄} where
  open Setoid S renaming (_≈_ to _≈S_)

  ∪-resp-≈ : P Respects _≈S_ → Q Respects _≈S_ → (P ∪ Q) Respects _≈S_
  ∪-resp-≈ P-wd Q-wd a≈b (inj₁ p-a) = inj₁ (P-wd a≈b p-a)
  ∪-resp-≈ P-wd Q-wd a≈b (inj₂ q-a) = inj₂ (Q-wd a≈b q-a)


  ∩-resp-≈ :  P Respects _≈S_ → Q Respects _≈S_ → (P ∩ Q) Respects _≈S_
  ∩-resp-≈ P-wd Q-wd a≈b (pa , qa) = P-wd a≈b pa , Q-wd a≈b qa


{- A setoid predicate is a well-defined predicate over a setoid -}
record SetoidPredicate {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) :
                           Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))  where
  open Setoid S renaming (_≈_ to _≈S_)
  field
    predicate : Pred ∥ S ∥ ℓ₃
    resp-≈ : predicate Respects _≈S_

  syntax predicate P a = a ∈ₛ P
  no-sats : Pred ∥ S ∥ ℓ₃
  no-sats a = ¬ predicate a
  syntax no-sats P a = a ∉ₛ P

open SetoidPredicate

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {S : Setoid ℓ₁ ℓ₂} (P : SetoidPredicate {ℓ₃ = ℓ₃} S) (Q : SetoidPredicate {ℓ₃ = ℓ₄} S)
  where

  _∪ₛ_ : SetoidPredicate {ℓ₃ = ℓ₃ ⊔ ℓ₄} S
  _∪ₛ_  = record {
           predicate = predicate P ∪ predicate Q
         ; resp-≈ = ∪-resp-≈ S (resp-≈ P) (resp-≈ Q)
         }

  _∩ₛ_ : SetoidPredicate {ℓ₃ = ℓ₃ ⊔ ℓ₄} S
  _∩ₛ_  = record {
            predicate = predicate P ∩ predicate Q
          ; resp-≈ = ∩-resp-≈ S (resp-≈ P)  (resp-≈ Q)
          }

  ∉-∪ₛ⁻ˡ : ∀ {a} → a ∉ₛ _∪ₛ_ → a ∉ₛ P
  ∉-∪ₛ⁻ˡ a∉∪ a∈P = a∉∪ (inj₁ a∈P)

  ∉-∪ₛ⁻ʳ : ∀ {a} → a ∉ₛ _∪ₛ_ → a ∉ₛ Q
  ∉-∪ₛ⁻ʳ a∉∪ a∈Q = a∉∪ (inj₂ a∈Q)

⊥ₛ : ∀ {ℓ₁ ℓ₂} {S : Setoid ℓ₁ ℓ₂} → SetoidPredicate S
predicate ⊥ₛ = ∅
resp-≈ ⊥ₛ = F.const F.id

⊤ₛ : ∀ {ℓ₁ ℓ₂} {S : Setoid ℓ₁ ℓ₂} → SetoidPredicate S
predicate ⊤ₛ = F.const ⊤
resp-≈ ⊤ₛ = F.const F.id

[_]ₛ : ∀ {ℓ₁ ℓ₂} {S : Setoid ℓ₁ ℓ₂} → (a : Carrier S) → SetoidPredicate {ℓ₃ = ℓ₂} S
[_]ₛ {S = S} a = record { predicate = λ x → x ≈S a
                        ; resp-≈ = λ x=y x=a → trans S (sym S x=y) x=a
                        }
     where open Setoid S renaming (_≈_ to _≈S_) using ()

Subset : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) → (Pred A ℓ₂) → Set _
Subset A P = Σ[ a ∈ A ] (P a)

{- A setoid predicate defines a setoid -}
SubSetoid : ∀ {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) → (P : Pred ∥ S ∥ ℓ₃) →
                         Setoid _ _
SubSetoid S P = record
  { Carrier = Subset ∥ S ∥ P
  ; _≈_ = λ { (e₁ , _) (e₂ , _) → (_≈_ S) e₁ e₂ }
  ; isEquivalence = record
    { refl = refl S
    ; sym = sym S
    ; trans = trans S
    }
  }

_↔_ : ∀ {ℓP ℓa} {A : Set ℓa} → (P Q : Pred A ℓP) → Set (ℓP ⊔ ℓa)
P ↔ Q = P ⊆ Q × Q ⊆ P

module _ {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) where

  _↔ₛ_ : (P Q : SetoidPredicate {ℓ₃ = ℓ₃} S) → Set (ℓ₁ ⊔ ℓ₃)
  P ↔ₛ Q = predicate P ↔ predicate Q

  open IsEquivalence
  PredSetoid : Setoid (lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃) (ℓ₁ ⊔ ℓ₃)
  Carrier PredSetoid = SetoidPredicate {ℓ₃ = ℓ₃} S
  _≈_ PredSetoid = _↔ₛ_
  refl (isEquivalence PredSetoid) = F.id , F.id
  sym (isEquivalence PredSetoid) (p ,  q) = q , p
  trans (isEquivalence PredSetoid) (p , q) (r , s)= (r ∘ p) , q ∘ s

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {S : Setoid ℓ₁ ℓ₂} {S' : Setoid ℓ₃ ℓ₄}
  (P : SetoidPredicate {ℓ₃ = ℓ₅} S) (Q : SetoidPredicate {ℓ₃ = ℓ₆} S')
  where

  _×ₚₛ_ : SetoidPredicate {ℓ₃ = ℓ₅ ⊔ ℓ₆} (S ×ₛ S')
  predicate _×ₚₛ_ (a , b) = a ∈ₛ P × b ∈ₛ Q
  resp-≈ _×ₚₛ_ eq (pa , qb) = resp-≈ P (proj₁ eq) pa , resp-≈ Q (proj₂ eq) qb


module Orthogonality where
  private
    variable
      ℓA ℓEqA ℓB ℓEqB ℓRel : Level
      A : Setoid ℓA ℓEqA
      B : Setoid ℓB ℓEqB
      R : REL ∥ A ∥  ∥ B ∥ ℓRel

  {- A binary relation over a setoid should be even with respect to the equality -}
  WellDefREL : REL ∥ A ∥ ∥ B ∥ ℓRel → Set _
  WellDefREL {A = A} {B = B} R₁ = ∀ {x y w z} → x ≈A y → w ≈B z → R₁ x w → R₁ y z
    where
    _≈A_ = _≈_ A
    _≈B_ = _≈_ B

  _ᵗ_ : ∀ {ℓ₃} (A₁ : SetoidPredicate {ℓ₃ = ℓ₃} A) → WellDefREL {A = A} {B = B} R → SetoidPredicate B
  _ᵗ_ {A = A} {B = B} {R = R} A₁ Rr = record
    { predicate = λ b → ∀ {a : ∥ A ∥} → a ∈ₛ A₁ → R a b
    ; resp-≈ = λ {x} {y} x=y A⇒R {a} a∈A₁ → Rr (reflA {x = a}) x=y (A⇒R a∈A₁)
    }
    where reflA = refl A

