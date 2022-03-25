-- Nominal Sets
-- ============
--
-- Action of a Group in a Set. G-Sets and Equivariant
-- functions.

open import Level
module GroupAction where

open import Algebra hiding (Inverse)
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function
open import Function.Construct.Composition renaming (inverse to _∘ₚ_;function to _∘ₛ_)
open import Function.Construct.Identity renaming (inverse to idₚ;function to idₛ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
 variable
  cℓ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

open Setoid

module G-Action (A : Setoid ℓ₁ ℓ₂) (G : Group cℓ ℓ) where

-- A function $\mathit{F} \colon G \times A\to A$ is an
-- \emph{action} if
-- * $F(\epsilon,\_) = \mathit{id}$ and
-- * $F(g,F(h,x)) = F(g\cdot h,x)$.
--
-- We assume that $F$ preserves the equality of the setoids
-- (of the group) and of the set on which it acts; in agda
-- this is given by Func.
  open Group
  open import Algebra.Properties.Group G

  record IsAction (F : Func (setoid G ×ₛ A) A) : Set (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ) where

    infix 8 _∙ₐ_
    open module G = Group G
    private
       _≈A_ = _≈_ A
       _≈G_ = _≈_ G
       ε′ = G.ε G.⁻¹

-- We introduce a more conventional syntax for the action as
-- an infix operator.

    _∙ₐ_ : Carrier G → Carrier A → Carrier A
    g ∙ₐ x = Func.f F (g , x)

    field
      idₐ : ∀ x → (G.ε ∙ₐ x) ≈A x
      ∘ₐ : ∀ g g' x → (g' ∙ₐ (g ∙ₐ x)) ≈A ((g' G.∙ g) ∙ₐ x)

    congˡ : ∀ {g} {g'} x → g ≈G g' → (g ∙ₐ x) ≈A (g' ∙ₐ x)
    congˡ x g≈g' = Func.cong F (g≈g' , refl A)

    congʳ : ∀ g {x} {x'} → x ≈A x' → (g ∙ₐ x) ≈A (g ∙ₐ x')
    congʳ g x≈x' = Func.cong F (refl G , x≈x')

    id⁻¹ : ∀ x → ((G.ε G.⁻¹) ∙ₐ x) ≈A x
    id⁻¹ x = trans A (congˡ x ε⁻¹≈ε) (idₐ x)


-- An Action is given by the function (preserving equalities) and
-- the proof that it satisfies the aforementioned laws.

  record Action : Set (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ) where

    private
      G-setoid = Group.setoid G
      _≈A_ = _≈_ A
      _≈G_ = _≈_ G

    field
      action : Func (G-setoid ×ₛ A) A
      isAction : IsAction action

    open IsAction isAction public
    private
      infix 9 _′
      _′ = G._⁻¹

    open ≈-Reasoning A

-- It is straightforward to verify $g^{ -1} \cdot (g \cdot x) = x$,
-- and the analogous one.
    _∘ₐ_-inv-idˡ : ∀ g x → (g ′ ∙ₐ (g ∙ₐ x)) ≈A x
    _∘ₐ_-inv-idˡ g x = begin
      (g ′ ∙ₐ (g ∙ₐ x))
      ≈⟨ ∘ₐ g (g ′) x  ⟩
      ((g ′) G.∙ g) ∙ₐ x
      ≈⟨ congˡ x (G.inverseˡ g) ⟩
      (G.ε ∙ₐ x)
      ≈⟨ idₐ x ⟩
      x ∎

    _∘ₐ_-inv-idʳ : ∀ g x → (g ∙ₐ (g ′ ∙ₐ x)) ≈A x
    _∘ₐ_-inv-idʳ g x = begin
      (g ∙ₐ (g ′ ∙ₐ x))
      ≈⟨ ∘ₐ (g ′) g x ⟩
      ((g  G.∙ g ′ ) ∙ₐ x)
      ≈⟨ congˡ x (G.inverseʳ g) ⟩
      (G.ε ∙ₐ x)
      ≈⟨ idₐ x ⟩
      x ∎

open G-Action
private
 variable
  G : Group cℓ ℓ

-- A G-Set is a set(oid) together with an action.
record G-Set {cℓ ℓ ℓ₁ ℓ₂ : Level} (G : Group cℓ ℓ) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ)) where
  field
    set : Setoid ℓ₁ ℓ₂
    act : Action {cℓ = cℓ} {ℓ} set G

-- A (equality preserving) function between two G-sets is \emph{equivariant}
-- if it commutes with the action.
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

-- The identity is an equivariant function.
Id : Equivariant A A
Id {A = A} =  record
  { F = idₛ A-setoid
  ; isEquivariant = λ x g → refl A-setoid
  }
  where A-setoid = set A

-- The composition of equivariants functions is also equivariant.
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

-- Binary Product (do we need/want more?) of G-Sets.
GSet-× : G-Set {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} G → G-Set {ℓ₁ = ℓ₃} {ℓ₄} G → G-Set {ℓ₁ = ℓ₁ ⊔ ℓ₃} {ℓ₂ = ℓ₂ ⊔ ℓ₄} G
GSet-× A B = record
  { set = set A ×ₛ set B
  ; act = record
    { action = record
      { f =  λ (g , (a , b)) → (g ∙A.∙ₐ a , (g ∙B.∙ₐ b))
      ; cong = λ (g≈g' , a≈a' , b≈b') → Func.cong ∙A.action (g≈g' , a≈a') ,  Func.cong ∙B.action (g≈g' , b≈b')
      }
    ; isAction = record
      { idₐ = λ x → ∙A.idₐ (proj₁ x) , ∙B.idₐ (proj₂ x)
      ; ∘ₐ = λ g g' x → (∙A.∘ₐ g g' (proj₁ x)) , ∙B.∘ₐ g g' (proj₂ x)
      }
    }
  }
  where open module ∙A = Action (act A)
        open module ∙B = Action (act B)

-- Projections are equivariants
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

-- Product morphism is equivariant.
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

-- Any setoid can be turned in a G-Set by letting $F(g,x) = x$.
-- This G-Set is called the discrete G-Set.
Δ : (A : Setoid ℓ₁ ℓ₂) → G-Set G
Δ A = record
  { set = A
  ; act = record
     { action = record
       { f = proj₂
       ; cong = proj₂
       }
       ; isAction = record
         { idₐ = λ _ → refl A
         ; ∘ₐ = λ _ _ _ → refl A
         }
     }
  }

module _ (AG : G-Set {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} G) (BG : G-Set {ℓ₁ = ℓ₃} {ℓ₄} G) where

  open import Setoid-Extra
  open Func
  open IsAction
  open module ∙A = Action (act AG)
  open module ∙B = Action (act BG)
  open ≈-Reasoning (set BG)

  module Grp = Group G
  private
    _′ = Grp._⁻¹
    ε = Grp.ε
    _∙_ = Grp._∙_
  open import Algebra.Properties.Group G

  GSet-⇒ : G-Set {ℓ₁ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} {ℓ₂ = ℓ₁ ⊔ ℓ₄} G
  set GSet-⇒ = set AG ⇒ₛ set BG
  f (f (action (act GSet-⇒)) (g , F)) a = g ∙B.∙ₐ f F (g ′ ∙A.∙ₐ a)
  cong (f (action (act GSet-⇒)) (g , F)) a≈a' = ∙B.congʳ g (cong F (∙A.congʳ (g ′) a≈a'))
  cong (action (act GSet-⇒)) {x = g , F} {g' , G} (g≈g' , F=G) a = begin
    g ∙B.∙ₐ f F (g ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ g (F=G ((g ′ ∙A.∙ₐ a))) ⟩
    g ∙B.∙ₐ f G (g ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ g (cong G (∙A.congˡ a (Grp.⁻¹-cong g≈g'))) ⟩
    g ∙B.∙ₐ f G (g' ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congˡ (f G (g' ′ ∙A.∙ₐ a)) g≈g' ⟩
    g' ∙B.∙ₐ f G (g' ′ ∙A.∙ₐ a) ∎
  idₐ (isAction (act GSet-⇒)) H a = begin
    ε ∙B.∙ₐ f H (ε ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ ε (cong H (∙A.id⁻¹ a)) ⟩
    ε ∙B.∙ₐ f H a
    ≈⟨ ∙B.idₐ (f H a) ⟩
    (f H a) ∎
  ∘ₐ (isAction (act GSet-⇒)) g g' H a = begin
    (g' ∙B.∙ₐ (g ∙B.∙ₐ f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a))))
    ≈⟨ ∙B.∘ₐ g g' (f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a))) ⟩
    (g' ∙ g) ∙B.∙ₐ (f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a)))
    ≈⟨ ∙B.congʳ (g' ∙ g) (cong H (∙A.∘ₐ (g' ′) (g ′) a)) ⟩
    (g' ∙ g) ∙B.∙ₐ f H (((g ′) ∙ (g' ′)) ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ (g' ∙ g) (cong H (∙A.congˡ a (Grp.sym (⁻¹-anti-homo-∙ g' g)))) ⟩
    (g' ∙ g) ∙B.∙ₐ f H ((g' ∙ g) ′ ∙A.∙ₐ a) ∎
