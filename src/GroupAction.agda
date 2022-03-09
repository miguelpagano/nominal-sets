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
open import Function.Construct.Composition renaming (inverse to _∘ₚ_;function to _∘ₛ_)
open import Function.Construct.Identity renaming (inverse to idₚ;function to idₛ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open Setoid
open Group

private
 variable
  cℓ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

module G-Action (A : Setoid ℓ₁ ℓ₂) (G : Group cℓ ℓ) where

  record IsAction
    (⊙ₐ : Func (setoid G ×ₛ A) A) : Set (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ) where

    infix 8 _∙ₐ_
    private
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

    congʳ : ∀ g {x} {x'} → x ≈A x' → (g ∙ₐ x) ≈A (g ∙ₐ x')
    congʳ g x≈x' = Func.cong ⊙ₐ (refl G , x≈x')

  record Action : Set (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ) where
    G-setoid = Group.setoid G
    field
      ⊙ₐ : Func (G-setoid ×ₛ A) A
      isAction : IsAction ⊙ₐ
    open IsAction isAction public
    private
      _≈A_ = _≈_ A
      _≈G_ = _≈_ G

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
private
 variable
  G : Group cℓ ℓ

record G-Set {cℓ ℓ ℓ₁ ℓ₂ : Level} (G : Group cℓ ℓ) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ)) where
  field
    set : Setoid ℓ₁ ℓ₂
    act : Action {cℓ = cℓ} {ℓ} set G

IsEquivariant :
  {A : Setoid ℓ₁ ℓ₂} →
  {B : Setoid ℓ₃ ℓ₄} →
  (∙A : Action {cℓ = cℓ} {ℓ} A G) →
  (∙B : Action B G) →
  (F : Func A B) → Set (ℓ₁ ⊔ ℓ₄ ⊔ cℓ)
IsEquivariant {B = B} ∙A ∙B F = ∀ x g → F.f ( g ∙A.∙ₐ x) ≈B (g ∙B.∙ₐ (F.f x))
  where open module ∙A = Action ∙A
        open module ∙B = Action ∙B
        open module F = Func F
        _≈B_ = _≈_ B

record Equivariant
  {G : Group cℓ ℓ}
  (A : G-Set {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} G)
  (B : G-Set {ℓ₁ = ℓ₃} {ℓ₂ = ℓ₄} G) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ cℓ)) where

  open G-Set
  field
    F : Func (set A) (set B)
    isEquivariant : IsEquivariant (act A) (act B) F

open G-Set
open Action

-- Identity
private
 variable
  A : G-Set {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} G
  B : G-Set {ℓ₁ = ℓ₃} {ℓ₂ = ℓ₄} G
  C : G-Set {ℓ₁ = ℓ₅} {ℓ₂ = ℓ₆} G

Id : Equivariant A A
Id {A = A} =  record
  { F = idₛ A-setoid
  ; isEquivariant = λ x g → refl A-setoid
  }
  where A-setoid = set A

_∘G_ : Equivariant A B → Equivariant B C → Equivariant A C
_∘G_ {A = A} {B = B} {C = C} H K = record {
    F = F H ∘ₛ F K
  ; isEquivariant = λ x g →
    begin
      f (F H ∘ₛ F K) (g ∙A x)
      ≈⟨ cong (F K) (isEquivariant H x g ) ⟩
      f (F K) (g ∙B (f (F H) x))
      ≈⟨ isEquivariant K (f (F H) x) g ⟩
      g ∙C f (F H ∘ₛ F K) x ∎
  }
  where open Equivariant
        open ≈-Reasoning (set C)
        open Func
        open Action (act A) renaming (_∙ₐ_ to _∙A_)
        open Action (act B) renaming (_∙ₐ_ to _∙B_)
        open Action (act C) renaming (_∙ₐ_ to _∙C_)

-- Binary Product (do we need/want more?)
GSet-× : G-Set {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} G → G-Set {ℓ₁ = ℓ₃} {ℓ₄} G → G-Set {ℓ₁ = ℓ₁ ⊔ ℓ₃} {ℓ₂ = ℓ₂ ⊔ ℓ₄} G
GSet-× A B = record
  { set = set A ×ₛ set B
  ; act = record
    { ⊙ₐ = record
      { f =  λ (g , (a , b)) → (g ∙A.∙ₐ a , (g ∙B.∙ₐ b))
      ; cong = λ (g≈g' , a≈a' , b≈b') → Func.cong ∙A.⊙ₐ (g≈g' , a≈a') ,  Func.cong ∙B.⊙ₐ (g≈g' , b≈b')
      }
    ; isAction = record
      { idₐ = λ x → ∙A.idₐ (proj₁ x) , ∙B.idₐ (proj₂ x)
      ; ∘ₐ = λ g g' x → (∙A.∘ₐ g g' (proj₁ x)) , ∙B.∘ₐ g g' (proj₂ x)
      }
    }
  }
  where open module ∙A = Action (act A)
        open module ∙B = Action (act B)

-- Projections
π₁ : Equivariant (GSet-× A B) A
π₁ {A = A} {B = B} = record
  {  F =  record
       {  f = proj₁
        ;  cong = proj₁
       }
   ;  isEquivariant = λ x g → refl A-setoid
  }
  where open Equivariant
        open Func
        open Setoid (set A) renaming (Carrier to A'; _≈_ to  _≈A_)
        open Setoid (set B) renaming (Carrier to B'; _≈_ to  _≈B_)
        A-setoid = set A

π₂ : Equivariant (GSet-× A B) B
π₂ {A = A} {B = B} = record
  {  F =  record
       {  f = proj₂
        ;  cong = proj₂
       }
   ;  isEquivariant = λ x g → refl B-setoid
  }
  where open Equivariant
        open Func
        open Setoid (set A) renaming (Carrier to A'; _≈_ to  _≈A_)
        open Setoid (set B) renaming (Carrier to B'; _≈_ to  _≈B_)
        B-setoid = set B

-- Product morphism
⟨_,_⟩ : Equivariant C A → Equivariant C B → Equivariant C (GSet-× A B)
⟨_,_⟩  {C = C} {A = A} {B = B} H K = record
  {  F =  record
       {  f =  λ c →  (f (F H)) c ,  (f (F K)) c
        ;  cong = λ c≈c' → Func.cong  (F H) c≈c' , Func.cong (F K)  c≈c'
       }
   ;  isEquivariant = λ x g →
        ( A=.begin
        f (F H) (g ∙C x)
        A=.≈⟨ isEquivariant H x g ⟩
        g ∙A f (F H) x
        A=.∎ ) ,
      (B=.begin
         f (F K) (g ∙C x)
         B=.≈⟨ isEquivariant K x g ⟩
         g ∙B f (F K) x
         B=.∎ )
  }
  where open Equivariant
        module A= = ≈-Reasoning (set A)
        module B= = ≈-Reasoning (set B)
        open Func
        open Setoid (set A) renaming (Carrier to A'; _≈_ to  _≈A_)
        open Setoid (set B) renaming (Carrier to B'; _≈_ to  _≈B_)
        open Action (act A) renaming (_∙ₐ_ to _∙A_)
        open Action (act B) renaming (_∙ₐ_ to _∙B_)
        open Action (act C) renaming (_∙ₐ_ to _∙C_)

open Equivariant

-- Equalities
-- eq₁ : (H : Equivariant C A) → (K : Equivariant C B) → ⟨ H , K ⟩ ∘G π₁ = H

-- Discrete G-Set
Δ : (A : Setoid ℓ₁ ℓ₂) → G-Set G
Δ A = record
  { set = A
  ; act = record
     { ⊙ₐ = record
       { f = proj₂
       ; cong = proj₂
       }
       ; isAction = record
         { idₐ = λ _ → refl A
         ; ∘ₐ = λ _ _ _ → refl A
         }
     }
  }
