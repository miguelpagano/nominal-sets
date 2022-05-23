-- Nominal Sets
-- ============
--
-- Action of a Group in a Set. G-Sets and Equivariant
-- functions.

open import Level
module GroupAction where

open import Algebra hiding (Inverse)
open import Data.Container using (Container)
  renaming (setoid to C-setoid;map to C-map)
open import Data.Product hiding (map)
import Data.Product.Relation.Binary.Pointwise.Dependent as DepProd
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum renaming (map to ⊎-map)
open import Data.Sum.Relation.Binary.Pointwise
open import Function
open import Function.Construct.Composition renaming (inverse to _∘ₚ_;function to _∘ₛ_)
open import Function.Construct.Identity renaming (inverse to idₚ;function to idₛ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Indexed.Heterogeneous as H
import Relation.Binary.Indexed.Heterogeneous.Construct.At as At
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
 variable
  cℓ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

open Setoid

module G-Action (G : Group cℓ ℓ) where

-- A function $\mathit{F} \colon G \times A\to A$ is an
-- \emph{action} if
-- * $F(\epsilon,\_) = \mathit{id}$ and
-- * $F(g,F(h,x)) = F(g\cdot h,x)$.
--
-- We assume that $F$ preserves the equality of the setoids
-- (of the group) and of the set on which it acts; in agda
-- this is given by Func.

  open module G = Group G hiding (_∙_;ε)
  open import Algebra.Properties.Group G public
  private
    _≈G_ = _≈_ G
  ε = G.ε
  ε′ = G.ε G.⁻¹
  infix 9 _′
  _′ = G._⁻¹
  _∙_ = G._∙_

  module _ {A : Setoid ℓ₁ ℓ₂} where

    GFunc : Set (cℓ ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    GFunc = Func (G.setoid ×ₛ A) A
    infixr 8 _●_

    _●_ : {F : GFunc} → Carrier G → Carrier A → Carrier A
    _●_ {F} g x = Func.f F (g , x)

    record IsAction (F : GFunc) : Set (ℓ₁ ⊔ ℓ₂ ⊔ cℓ ⊔ ℓ) where
      infix 4 _≈A_
      infixr 8 _∙ₐ_

      private
         _≈A_ = _≈_ A
      _∙ₐ_ = _●_ {F = F}
--   We introduce a more conventional syntax for the action as
--   an infix operator.

      field
        idₐ : ∀ x → G.ε ∙ₐ x ≈A x
        compₐ : ∀ g' g x → g' ∙ₐ g ∙ₐ x ≈A (g' ∙ g) ∙ₐ x

      congˡ : ∀ {g} {g'} x → g ≈G g' → g ∙ₐ x ≈A g' ∙ₐ x
      congˡ x g≈g' = Func.cong F (g≈g' , refl A)

      congʳ : ∀ g {x} {x'} → x ≈A x' → g ∙ₐ x ≈A g ∙ₐ x'
      congʳ g x≈x' = Func.cong F (refl G , x≈x')

      id⁻¹ : ∀ x → ε′ ∙ₐ x ≈A x
      id⁻¹ x = trans A (congˡ x ε⁻¹≈ε) (idₐ x)

      open ≈-Reasoning A

      act-inv-idˡ : ∀ g x → (g ′ ∙ₐ (g ∙ₐ x)) ≈A x
      act-inv-idˡ g x = begin
        g ′ ∙ₐ (g ∙ₐ x)
        ≈⟨ compₐ (g ′) g x  ⟩
        ((g ′) G.∙ g) ∙ₐ x
        ≈⟨ congˡ x (G.inverseˡ g) ⟩
        G.ε ∙ₐ x
        ≈⟨ idₐ x ⟩
        x ∎

      act-inv-idʳ : ∀ g x → (g ∙ₐ (g ′ ∙ₐ x)) ≈A x
      act-inv-idʳ g x = begin
        g ∙ₐ (g ′ ∙ₐ x)
        ≈⟨ compₐ g (g ′) x ⟩
        (g  G.∙ g ′ ) ∙ₐ x
        ≈⟨ congˡ x (G.inverseʳ g) ⟩
        G.ε ∙ₐ x
        ≈⟨ idₐ x ⟩
        x ∎


-- An Action is given by the function (preserving equalities) and
-- the proof that it satisfies the aforementioned laws.
  record GSet : Set (suc (cℓ ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
     field
       set : Setoid ℓ₁ ℓ₂
       action : Func (G.setoid ×ₛ set) set
       isAction : IsAction action

     open IsAction isAction public

  open GSet
  open Func

  G-GSet : GSet
  set (G-GSet) = Group.setoid G
  f (action (G-GSet)) (g , g') = g ∙ g'
  cong (action (G-GSet )) (x=x' , y=y') = ∙-cong x=x' y=y'
  isAction (G-GSet) = record
    { idₐ = λ x → identityˡ x
    ; compₐ = λ g g' x → sym G (assoc g g' x)
    }

-- A (equality preserving) function between two G-sets is \emph{equivariant}
-- if it commutes with the action.

  IsEquivariant :
    {A : Setoid ℓ₁ ℓ₂} →
    {B : Setoid ℓ₃ ℓ₄} →
    (∙A : GFunc {A = A}) →
    (∙B : GFunc {A = B}) →
    (F : Func A B) → Set (ℓ₁ ⊔ ℓ₄ ⊔ cℓ)
  IsEquivariant {A = A} {B = B} ∙A ∙B F = ∀ x g → F.f (g ●A x) ≈B (g ●B F.f x)
    where
    _●A_ = _●_ {F = ∙A} ; _●B_ = _●_ {F = ∙B} ; _≈B_ = _≈_ B
    open module F = Func F

  record Equivariant
    (A : GSet {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂})
    (B : GSet {ℓ₁ = ℓ₃} {ℓ₂ = ℓ₄}) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ cℓ)) where

    infixl 8 _●A_ _●B_
    open GSet
    _●A_ = _●_ {F = GSet.action A}
    _●B_ = _●_ {F = GSet.action B}

    src = set A
    tgt = set B

    open GSet
    field
      F : Func (set A) (set B)
      isEquivariant : IsEquivariant (action A) (action B) F


variable
  G : Group cℓ ℓ
open G-Action using (GSet; IsAction; Equivariant)
open GSet
open IsAction
open Equivariant

-- Identity
private
 variable
  A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}
  B : GSet G {ℓ₁ = ℓ₃} {ℓ₂ = ℓ₄}
  C : GSet G {ℓ₁ = ℓ₅} {ℓ₂ = ℓ₆}

-- The identity is an equivariant function.
Id : Equivariant G A A
Id {A = A} =  record
  { F = idₛ A-setoid
  ; isEquivariant = λ _ _ → refl A-setoid
  }
  where A-setoid = set A

-- The composition of equivariants functions is also equivariant.
_∘G_ : Equivariant G A B → Equivariant G B C → Equivariant G A C
_∘G_ H K = record {
    F = F H ∘ₛ F K
  ; isEquivariant = λ x g →
    begin
      f (F H ∘ₛ F K) (g ∙A x)
      ≈⟨ cong (F K) (isEquivariant H x g ) ⟩
      f (F K) (g ∙B (f (F H) x))
      ≈⟨ isEquivariant K (f (F H) x) g ⟩
      g ∙C f (F H ∘ₛ F K) x ∎
  }
  where
  open Equivariant H renaming (_●A_ to _∙A_;_●B_ to _∙B_) using ()
  open Equivariant K renaming (_●B_ to _∙C_) using ()
  open ≈-Reasoning (tgt K)
  open Func

open Func

-- Binary Product (do we need/want more?) of G-Sets.
module _ (A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) (B : GSet G {ℓ₁ = ℓ₃} {ℓ₄}) where
  private
    open module ∙A = GSet A
    open module ∙B = GSet B

  GSet-× : GSet G {ℓ₁ = ℓ₁ ⊔ ℓ₃} {ℓ₂ = ℓ₂ ⊔ ℓ₄}
  set GSet-×  = set A ×ₛ set B
  f (action GSet-×) (g , (a , b)) = g ∙A.∙ₐ a  , g ∙B.∙ₐ b
  cong (action GSet-×) (g=g' , (a=a' , b=b')) = Func.cong ∙A.action (g=g' , a=a') ,  Func.cong ∙B.action (g=g' , b=b')
  idₐ (isAction (GSet-×)) (a , b) = ∙A.idₐ a , ∙B.idₐ b
  compₐ (isAction (GSet-×)) g g' (a , b) = ∙A.compₐ g g' a , ∙B.compₐ g g' b

-- Projections are equivariant
  π₁ : Equivariant G GSet-× A
  π₁ = record
    { F = record
          { f = proj₁
          ; cong = proj₁
          }
    ; isEquivariant = λ x g → refl A-setoid
    }
    where A-setoid = set A


  π₂ : Equivariant G GSet-× B
  π₂ = record
    { F = record
          { f = proj₂
          ; cong = proj₂
          }
    ; isEquivariant = λ x g → refl B-setoid
    }
    where B-setoid = set B


-- Product morphism is equivariant.
⟨_,_⟩ : Equivariant G C A → Equivariant G C B → Equivariant G C (GSet-× A B)
⟨ H , K ⟩ = record
  { F = record
        { f =  < f (F H) , f (F K) >
        ; cong = < Func.cong (F H) , Func.cong (F K) >
        }
  ; isEquivariant = λ x → < isEquivariant H x ,
                            isEquivariant K x >
  }

module _ (A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) (B : GSet G {ℓ₁ = ℓ₃} {ℓ₄}) where
  private
    open module ∙A = GSet A
    open module ∙B = GSet B
  GSet-⊎ : GSet G {ℓ₁ = ℓ₁ ⊔ ℓ₃} {ℓ₂ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄}
  set GSet-⊎ = set A ⊎ₛ set B
  f (action GSet-⊎) (g , inj₁ a) = inj₁ (g ∙A.∙ₐ a)
  f (action GSet-⊎) (g , inj₂ b) = inj₂ (g ∙B.∙ₐ b)
  cong (action GSet-⊎) (g=g' , inj₁ a=a') = inj₁ (Func.cong ∙A.action (g=g' , a=a'))
  cong (action GSet-⊎) (g=g' , inj₂ b=b') = inj₂ (Func.cong ∙B.action (g=g' , b=b'))
  idₐ (isAction GSet-⊎) (inj₁ a) = inj₁ (∙A.idₐ a)
  idₐ (isAction GSet-⊎) (inj₂ b) = inj₂ (∙B.idₐ b)
  compₐ (isAction GSet-⊎) g g' (inj₁ a) = inj₁ (∙A.compₐ g g' a)
  compₐ (isAction GSet-⊎) g g' (inj₂ b) = inj₂ (∙B.compₐ g g' b)


  -- Injections are equivariants
  inject₁ : Equivariant G A GSet-⊎
  inject₁ = record
    { F = record
          { f = inj₁
          ; cong = inj₁
          }
    ; isEquivariant = λ x g → inj₁ (refl A-setoid)
    }
    where A-setoid = set A

  inject₂ : Equivariant G B GSet-⊎
  inject₂ = record
    { F = record
          { f = inj₂
          ; cong = inj₂
          }
    ; isEquivariant = λ x g → inj₂ (refl B-setoid)
    }
    where B-setoid = set B

-- CoProduct morphism is equivariant.
[_,_]G : Equivariant G A C → Equivariant G B C → Equivariant G (GSet-⊎ A B) C
[_,_]G {A = A} {C = C} {B = B} H K = record
  { F = record
        { f = [ f (F H) , f (F K) ]′
        ; cong = λ { (inj₁ c≈c') → Func.cong (F H) c≈c'
                   ; (inj₂ c≈c') → Func.cong (F K) c≈c' }
        }
  ; isEquivariant = λ { (inj₁ x) g → isEquivariant H x g
                      ; (inj₂ x) g → isEquivariant K x g }
  }

-- Equalities
-- eq₁ : (H : Equivariant C A) → (K : Equivariant C B) → ⟨ H , K ⟩ ∘G π₁ = H

open Equivariant
open IsAction
-- Any setoid can be turned in a GSet by letting $F(g,x) = x$.
-- This GSet is called the discrete GSet.
Δ : (A : Setoid ℓ₁ ℓ₂) → GSet G
set (Δ A) = A
f (action (Δ A)) = proj₂
cong (action (Δ A)) = proj₂
idₐ (isAction (Δ A)) _ = refl A
compₐ (isAction (Δ A)) _ _ _ = refl A

-- Lists.
module _ (A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) where
  private
    open module ∙A = GSet A
    open G-Action G hiding (IsAction;GSet;Equivariant)

  open import Setoid-Extra
  open Func
  open IsAction
  open import Data.List.Relation.Binary.Equality.Setoid (set A)
  open import Data.List.Relation.Binary.Pointwise as PW' hiding (Pointwise;_∷_;[])
  open import Data.List renaming (map to map[])

  open ≈-Reasoning ≋-setoid
  open module PW = Setoid ≋-setoid
  GSet-[] : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₁ ⊔ ℓ₂}
  set GSet-[] = ≋-setoid
  f (action GSet-[]) (g , as) = map[] (g ∙A.∙ₐ_) as
  cong (action GSet-[]) {g , as} {g' , bs} (g=g' , as=bs) = cong' as=bs
    where
    cong' : ∀ {as} {bs} → as ≋ bs → map[] ((g ∙A.∙ₐ_)) as ≋ map[] ((g' ∙A.∙ₐ_)) bs
    cong' PW'.[] = PW'.[]
    cong' (x=y PW'.∷ as=bs) = cong ∙A.action (g=g' , x=y) PW'.∷ (cong' as=bs)
  idₐ (isAction GSet-[]) xs = id-action xs
    where
    id-action : ∀ xs → map[] ((ε ∙A.∙ₐ_)) xs PW.≈ xs
    id-action [] = PW.refl
    id-action (x ∷ xs) =  ∙A.idₐ x ∷ id-action xs
  compₐ (isAction GSet-[]) g' g = sym ≋-setoid ∘ comp-action
    where
    comp-action : ∀ xs → map[] ((g' ∙ g) ∙A.∙ₐ_) xs PW.≈ map[] (g' ∙A.∙ₐ_) (map[] ((g ∙A.∙ₐ_)) xs)
    comp-action [] = PW.refl
    comp-action (x ∷ xs) = (sym (set A) (∙A.compₐ g' g x)) PW'.∷ (comp-action xs)

module _ (A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) (B : GSet G {ℓ₁ = ℓ₃} {ℓ₄}) where
  private
    open module ∙A = GSet A
    open module ∙B = GSet B
    open G-Action G hiding (IsAction;GSet;Equivariant)
    open ≈-Reasoning (set B)

    ′-cong = Group.⁻¹-cong G

  open import Setoid-Extra
  GSet-⇒ : GSet G {ℓ₁ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} {ℓ₂ = ℓ₁ ⊔ ℓ₄}
  set GSet-⇒ = set A ⇒ₛ set B
  f (f (action GSet-⇒) (g , F)) a = g ∙B.∙ₐ f F (g ′ ∙A.∙ₐ a)
  cong (f (action GSet-⇒) (g , F)) a≈a' = ∙B.congʳ g (cong F (∙A.congʳ (g ′) a≈a'))
  cong (action GSet-⇒) {x = g , F} {g' , H} (g≈g' , F=H) a = begin
    g ∙B.∙ₐ f F (g ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ g (F=H (g ′ ∙A.∙ₐ a)) ⟩
    g ∙B.∙ₐ f H (g ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ g (cong H (∙A.congˡ a (′-cong g≈g'))) ⟩
    g ∙B.∙ₐ f H (g' ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congˡ (f H (g' ′ ∙A.∙ₐ a)) g≈g' ⟩
    g' ∙B.∙ₐ f H (g' ′ ∙A.∙ₐ a) ∎
  idₐ (isAction GSet-⇒) H a = begin
    ε ∙B.∙ₐ f H (ε ′ ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ ε (cong H (∙A.id⁻¹ a)) ⟩
    ε ∙B.∙ₐ f H a
    ≈⟨ ∙B.idₐ (f H a) ⟩
    (f H a) ∎
  compₐ (isAction GSet-⇒) g' g H a = begin
    (g' ∙B.∙ₐ (g ∙B.∙ₐ f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a))))
    ≈⟨ ∙B.compₐ g' g (f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a))) ⟩
    (g' ∙ g) ∙B.∙ₐ (f H (g ′ ∙A.∙ₐ (g' ′ ∙A.∙ₐ a)))
    ≈⟨ ∙B.congʳ (g' ∙ g) (cong H (∙A.compₐ (g ′) (g' ′) a)) ⟩
    (g' ∙ g) ∙B.∙ₐ f H (((g ′) ∙ (g' ′)) ∙A.∙ₐ a)
    ≈⟨ ∙B.congʳ (g' ∙ g) (cong H (∙A.congˡ a (sym (Group.setoid G) (⁻¹-anti-homo-∙ g' g)))) ⟩
    (g' ∙ g) ∙B.∙ₐ f H ((g' ∙ g) ′ ∙A.∙ₐ a) ∎


module _ (A : GSet G {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) {ℓs ℓp} (C : Container ℓs ℓp) where
  private
    open import Setoid-Extra
    open module ∙A = GSet A hiding (set)
    open G-Action G hiding (IsAction;GSet;Equivariant)
    open import Data.Container.Relation.Binary.Pointwise hiding (map)
    open import Relation.Binary.PropositionalEquality using (_≡_)

  GSet-C : GSet G {ℓ₁ = ℓs ⊔ ℓp ⊔ ℓ₁} {ℓ₂ = ℓs ⊔ ℓp ⊔ ℓ₂}
  set GSet-C = C-setoid (set A) C
  f (action GSet-C) (g , as) = C-map (g ∙A.∙ₐ_) as
  cong (action GSet-C) (g=g' , (s=s' , f=f')) = s=s' , (λ p → cong ∙A.action (g=g' , (f=f' p)))
  idₐ (isAction GSet-C) (s , f) = _≡_.refl , ∙A.idₐ ∘ f
  compₐ (isAction GSet-C) g g' (s , f) = _≡_.refl , ∙A.compₐ g g' ∘ f

module Sigma {ℓ3 ℓ4} (A : Set ℓ₁)
             {B : H.IndexedSetoid A ℓ3 ℓ4 }
             (actFam : ∀ a → Func (Group.setoid G ×ₛ (At.setoid B a)) (At.setoid B a))
             (isActFam : ∀ a → IsAction G (actFam a))
             where

  open Func
  open H.IndexedSetoid renaming (Carrier to ICarrier)
  open DepProd

  GSet-Σ  : GSet G {ℓ₁ = ℓ₁ ⊔ ℓ3} {ℓ₂ = ℓ₁ ⊔ ℓ3 ⊔ ℓ4}
  set GSet-Σ = DepProd.setoid (PE.setoid A) B
  f (action GSet-Σ) (g , a , b) = a , f (actFam a) (g , b)
  cong (action GSet-Σ) {g , (a , b)} (g=g' , PE._≡_.refl , b=b') =
    PE._≡_.refl , cong (actFam a) (g=g' , b=b')
  idₐ (isAction GSet-Σ) (a , b) = PE._≡_.refl , idₐ (isActFam a) b
  compₐ (isAction GSet-Σ) g g' (a , b) = PE._≡_.refl , compₐ (isActFam a) g g' b

