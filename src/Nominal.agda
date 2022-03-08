------------------------------------------------------------
-- Nominal Sets
--
-- Nominal Sets
------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
module Nominal where
open import Level
open import Data.Product hiding (map)
open import Data.List
open import Algebra hiding (Inverse)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;≢-sym)
open import Relation.Nullary
open import Relation.Unary hiding (_∉_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)

variable
  ℓ ℓ' ℓx ℓx' ℓP : Level

module Nominal (A-setoid : DecSetoid ℓ ℓ') where
  open DecSetoid
  import Permutation
  open module A-Perm = Permutation.Perm A-setoid
  𝔸 : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  𝔸 = Perm-A

  open import Data.List.Membership.DecSetoid A-setoid

  import GroupAction
  open import Setoid-Extra
  module Support {ℓx ℓx' : Level}
    (X-set : GroupAction.G-Set {cℓ = (ℓ ⊔ ℓ') } {ℓ = ℓ ⊔ ℓ'} {ℓ₁ = ℓx} {ℓ₂ = ℓx'} 𝔸)
    (P : SetoidPredicate {ℓ₃ = ℓP} (setoid A-setoid))
    where
    open GroupAction.G-Set
    open GroupAction.G-Action.Action
    open Setoid hiding (_≉_)
    open Inverse
    open SetoidPredicate
    open Func

    _≈X_ = _≈_ (set X-set)
    _∘ₓ_ : PERM → Carrier (set X-set) → Carrier (set X-set)
    p ∘ₓ a = (f ∘ ⊙ₐ) (act X-set) (p , a)

    is-supp_ : (x : Carrier (set X-set)) → Set (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
    is-supp x = ∀ (π : PERM) → (∀ a → predicate P a → a ∉-dom (proj₁ π)) → (π ∘ₓ x) ≈X x

    private
      is-supp'_ : (x : Carrier (set X-set)) → Set (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
      is-supp' x = ∀ (π : PERM) → (∀ a → predicate P a → a ∉ atoms' (proj₁ (proj₂ π))) →
        (π ∘ₓ x) ≈X x

      imp : ∀ x → is-supp x → is-supp' x
      imp x pred π inv = pred π (λ a Pa → proj₂ (∉-PERM π a)
         (∉-atoms'-∉ (proj₁ (proj₂ π)) (inv a Pa)))

      imp' : ∀ x → is-supp' x → is-supp x
      imp' x pred Π@(π , p , _) inv = pred Π (λ a Pa → ∉-∉-atoms p (proj₁ (∉-PERM Π a) ((inv a Pa))))
