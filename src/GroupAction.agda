------------------------------------------------------------
-- Nominal Sets
--
-- Action of a Group in a Set. G-Sets and Equivariant
-- functions.
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

    infix 8 _∙ₐ_
    _≈A_ = _≈_ A
    _≈G_ = _≈_ G
    _∙ₐ_ : Carrier G → Carrier A → Carrier A
    g ∙ₐ x = Func.f ⊙ₐ (g , x)

    open module G = Group G
    field
      idₐ : ∀ x → (G.ε ∙ₐ x) ≈A x
      ∘ₐ : ∀ g g' x → (g' ∙ₐ (g ∙ₐ x)) ≈A ((g G.∙ g') ∙ₐ x)

    congˡ : ∀ {g} {g'} x → g ≈G g' → (g ∙ₐ x) ≈A (g' ∙ₐ x)
    congˡ x g≈g' = Func.cong ⊙ₐ (g≈g' , refl A)

  record Action : Set (ℓ ⊔ ℓ' ⊔ cℓ ⊔ ℓ'') where
    G-setoid = Group.setoid G
    field
      ⊙ₐ : Func (G-setoid ×ₛ A) A
      isAction : IsAction ⊙ₐ
    open IsAction isAction public

    infix 9 _′
    _′ = G._⁻¹
    open ≈-Reasoning A

    _∘ₐ_-inv-idˡ : ∀ g x → (g ′ ∙ₐ (g ∙ₐ x)) ≈A x
    _∘ₐ_-inv-idˡ g x = begin
      (g ′ ∙ₐ (g ∙ₐ x))
      ≈⟨ ∘ₐ g (g ′) x  ⟩
      ((g G.∙ g ′) ∙ₐ x)
      ≈⟨ congˡ x (G.inverseʳ g) ⟩
      (G.ε ∙ₐ x)
      ≈⟨ idₐ x ⟩
      x ∎

    _∘ₐ_-inv-idʳ : ∀ g x → (g ∙ₐ (g ′ ∙ₐ x)) ≈A x
    _∘ₐ_-inv-idʳ g x = begin
      (g ∙ₐ (g ′ ∙ₐ x))
      ≈⟨ ∘ₐ (g ′) g x  ⟩
      ((g ′ G.∙ g ) ∙ₐ x)
      ≈⟨ congˡ x (G.inverseˡ g) ⟩
      (G.ε ∙ₐ x)
      ≈⟨ idₐ x ⟩
      x ∎

open G-Action

record G-Set {ℓ ℓ'} {cℓ ℓ''} (G : Group cℓ ℓ'') : Set (suc (ℓ ⊔ ℓ' ⊔ cℓ ⊔ ℓ'')) where
  field
    set : Setoid ℓ ℓ'
    act : Action set G


IsEquivariant : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {cℓ ℓ}
  {G : Group cℓ ℓ} →
  {A : Setoid ℓ₁ ℓ₂} →
  {B : Setoid ℓ₃ ℓ₄} →
  (∙A : Action A G) →
  (∙B : Action B G) →
  (F : Func A B) → Set (ℓ₁ ⊔ ℓ₄ ⊔ cℓ)
IsEquivariant {B = B} ∙A ∙B F = ∀ x g → F.f ( g ∙A.∙ₐ x) ≈B (g ∙B.∙ₐ (F.f x))
  where open module ∙A = Action ∙A
        open module ∙B = Action ∙B
        open module F = Func F
        _≈B_ = _≈_ B

record Equivariant {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {cℓ ℓ}
  {G : Group cℓ ℓ}
  {A : G-Set {ℓ₁} {ℓ₂} G}
  {B : G-Set {ℓ₃} {ℓ₄} G} : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ cℓ)) where

  open G-Set
  field
    F : Func (set A) (set B)
    isEquiv : IsEquivariant (act A) (act B) F
