------------------------------------------------------------
-- Nominal Sets
--
-- Action of a Group in a Set.
------------------------------------------------------------
open import Level
open import Algebra hiding (Inverse)
open import Relation.Binary

module GroupAction where

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Permutation
open Setoid
open Group

module G-Action {ℓ ℓ' cℓ ℓ''} (A : Setoid ℓ ℓ') (G : Group cℓ ℓ'') where

  record IsAction
    (⊙ₐ : Func (setoid G ×ₛ A) A) : Set (ℓ ⊔ ℓ' ⊔ cℓ ⊔ ℓ'') where

    _≈A_ = _≈_ A
    _∙ₐ_ : Carrier G → Carrier A → Carrier A
    g ∙ₐ x = Func.f ⊙ₐ (g , x)

    field
      idₐ : ∀ x → (ε G ∙ₐ x) ≈A x
      ∘ₐ : ∀ g g' x → (g' ∙ₐ (g ∙ₐ x)) ≈A ((_∙_ G g g') ∙ₐ x)

  record Action : Set (ℓ ⊔ ℓ' ⊔ cℓ ⊔ ℓ'') where
    open module G = Group G
    field
      ⊙ₐ : Func (G.setoid ×ₛ A) A
      isAction : IsAction ⊙ₐ

    open IsAction isAction public

open G-Action

record G-Set {ℓ ℓ'} {cℓ ℓ''} (G : Group cℓ ℓ'') : Set (suc (ℓ ⊔ ℓ' ⊔ cℓ ⊔ ℓ'')) where
  field
    set : Setoid ℓ ℓ'
    act : Action set G


IsEquivariant : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {cℓ ℓ}
  {G : Group cℓ ℓ} →
  {A : Setoid ℓ₁ ℓ₂} →
  {B : Setoid ℓ₃ ℓ₄} →
  (⊙-A : Action A G) →
  (⊙-B : Action B G) →
  (F : Func A B) → Set (ℓ₁ ⊔ ℓ₄ ⊔ cℓ)
IsEquivariant {B = B} ⊙-A ⊙-B F = ∀ x g → F.f ( g ⊙-A.∙ₐ x) ≈B (g ⊙-B.∙ₐ (F.f x))
  where open module ⊙-A = Action ⊙-A ; open module ⊙-B = Action ⊙-B
        open module F = Func F
        _≈B_ = _≈_ B
