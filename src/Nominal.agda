------------------------------------------------------------
-- Nominal Sets
--
-- Nominal Sets
------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
module Nominal where
open import Level
open import Data.Product hiding (map)
open import Algebra hiding (Inverse)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;≢-sym)
open import Relation.Nullary
open import Relation.Unary
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

    _≈A_ = _≈_ A-setoid
    _≉A_ = _≉_ A-setoid
    _≈X_ = _≈_ (set X-set)
    _∘ₓ_ : PERM → Carrier (set X-set) → Carrier (set X-set)
    p ∘ₓ a = (f ∘ ⊙ₐ) (act X-set) (p , a)
    supp_ : (x : Carrier (set X-set)) → Set (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
    supp x = ∀ (π : PERM) → (∀ a → predicate P a → a ∉ₐ (proj₁ π)) → (π ∘ₓ x) ≈X x
