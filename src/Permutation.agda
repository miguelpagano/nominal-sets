------------------------------------------------------------
-- Nominal Sets
--
-- Permutations on a setoid form the Symmetry Group.
------------------------------------------------------------
module Permutation where

open import Level
open import Data.Product
open import Algebra hiding (Inverse)
open import Function
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)

variable
  ℓ ℓ' : Level

module Symmetry-Group (A-setoid : Setoid ℓ ℓ') where
  open IsEquivalence
  open Inverse
  open Setoid hiding (_≈_)
  open ≈-Reasoning A-setoid

  _≈_ = Setoid._≈_ A-setoid
  isEq = isEquivalence A-setoid

  Perm : Set _
  Perm = Inverse A-setoid A-setoid

  _≈ₚ_ : Rel Perm _
  F ≈ₚ G = (x : Carrier A-setoid) → f F x ≈ f G x

  cong-⁻¹ : Congruent₁ _≈ₚ_ _⁻¹
  cong-⁻¹ {F} {G} F≈G x = begin
            f⁻¹ F x
              ≈⟨ cong₂ F (sym isEq (proj₁ (inverse G) x)) ⟩
            (f⁻¹ F ∘ (f G ∘ f⁻¹ G)) x
              ≈⟨ cong₂ F (sym isEq (F≈G (f⁻¹ G x))) ⟩
            (f⁻¹ F ∘ (f F ∘ f⁻¹ G)) x
              ≈⟨ proj₂ (inverse F) (f⁻¹ G x) ⟩
            f⁻¹ G x
              ∎

  cong₂-≈-∘ : Congruent₂ _≈ₚ_ _∘ₚ_
  cong₂-≈-∘ {F} {G} {H} {K} F≈G  H≈K x = begin
    f H (f F x)  ≈⟨ cong₁ H (F≈G x) ⟩
    f H (f G x)  ≈⟨ H≈K (f G x) ⟩
    f K (f G x) ∎

  Sym-A : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  Sym-A = record
            { Carrier = Perm
            ; _≈_ = _≈ₚ_
            ; _∙_ = _∘ₚ_
            ; ε = idₚ A-setoid
            ; _⁻¹ = _⁻¹
            ; isGroup = record {
                isMonoid = record {
                  isSemigroup = record {
                  isMagma = record {
                    isEquivalence = record {
                        refl = λ {F} x → cong₁ F (refl isEq)
                      ; sym = λ F≈G → sym isEq ∘ F≈G
                      ; trans = λ F≈G G≈H x → trans isEq (F≈G x) (G≈H x)
                    } ;
                    ∙-cong = λ {F} {G} {H} {K} → cong₂-≈-∘ {F} {G} {H} {K}
                  }
                  ; assoc = λ _ _ _ _ → refl isEq
                  }
                ; identity = (λ _ _ → refl isEq) , (λ _ _ → refl isEq)
                }
              ; inverse = proj₁ ∘ inverse , proj₂ ∘ inverse
              ; ⁻¹-cong = λ {F} {G} → cong-⁻¹ {F} {G}
              }
            }
