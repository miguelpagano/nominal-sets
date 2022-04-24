-- Nominal Sets
-- ============

-- Permutations on a setoid form the Symmetry Group.
{-# OPTIONS --allow-unsolved-metas #-}
module Permutation where

open import Level renaming (suc to lsuc)

open import Algebra hiding (Inverse)
open import Data.List
open import Data.List.Properties

open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  renaming (head to head')
import Data.List.Membership.DecSetoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any hiding (tail)
open import Data.Product hiding (map)
open import Function hiding (_↔_)
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_;≢-sym;Reveal_·_is_;[_];inspect)
  renaming(sym to ≡-sym;subst to ≡-subst;cong to ≡-cong)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary hiding (_∈_;_∉_)

open import Setoid-Extra
import List-Extra

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

-- Two permutations are equal if they coincide in every atom.
  _≈ₚ_ : Rel Perm _
  F ≈ₚ G = (x : Carrier A-setoid) → f F x ≈ f G x

-- The inverse of equal permutations are equal
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
-- and the composition of permutation maps equal permutations to
-- equal permutations.
  cong₂-≈-∘ : Congruent₂ _≈ₚ_ _∘ₚ_
  cong₂-≈-∘ {F} {G} {H} {K} F≈G  H≈K x = begin
    f H (f F x)  ≈⟨ cong₁ H (F≈G x) ⟩
    f H (f G x)  ≈⟨ H≈K (f G x) ⟩
    f K (f G x) ∎

-- Group of symmetries
-- -------------------

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

-- In this module we first define the transposition of atoms,
-- prove that it is an Permutation (a bijection) on the
-- set of atoms and prove several properties about them.
-- Then we define the group of Finite Permutations.

-- TODO:
-- * prove that Perm is a sub-group of Sym.

module Perm (A-setoid : DecSetoid ℓ ℓ') where
  open DecSetoid A-setoid
  open module A-Sym = Symmetry-Group setoid hiding (_≈_) public
  open import Data.Bool hiding (_≟_)
  open import Data.Empty

  open Inequality setoid

  open Inverse

  perm-injective : (π : Perm) → Injective _≈_ _≈_ (f π)
  perm-injective π {c} {d} eq = begin
    c
    ≈⟨ sym (Inverse.inverseʳ π c) ⟩
    f⁻¹ π (f π c)
    ≈⟨ cong₂ π eq ⟩
    f⁻¹ π (f π d)
    ≈⟨ Inverse.inverseʳ π d ⟩
    d ∎
    where open ≈-Reasoning setoid

  perm-injective' : (π : Perm) → Injective _≉_ _≉_ (f π)
  perm-injective' π {c} {d} neq c=d = contradiction (cong₁ π c=d) neq

-- Transposition (or swapping) of atoms
-- ------------------------------------

-- Usually, $\mathit{transp}\, a\,b$ is written $(a\ b)$.
  transp : (a b c : Carrier) → Carrier
  transp a b c with does (c ≟ a)
  ... | true = b
  ... | false with does (c ≟ b)
  ... | true = a
  ... | false = c

  transp-eq₁ : ∀ {a} b {c} → c ≈ a → transp a b c ≡ b
  transp-eq₁ {a} b {c} c=a with c ≟ a
  ... | yes p = _≡_.refl
  ... | no c≠a = contradiction c=a c≠a

  transp-eq₂ : ∀ {a b c} → c ≉ a → c ≈ b → transp a b c ≡ a
  transp-eq₂ {a} {b} {c} c≠a c=b with c ≟ a
  ... | yes c=a = contradiction c=a c≠a
  ... | no c≠a with c ≟ b
  ... | yes c=b = _≡_.refl
  ... | no c≠b = contradiction c=b c≠b

  transp-eq₃ : ∀ {a b c} → c ≉ a → c ≉ b → transp a b c ≡ c
  transp-eq₃ {a} {b} {c} c≠a c≠b with c ≟ a
  ... | yes c=a = contradiction c=a c≠a
  ... | no c≠a with c ≟ b
  ... | no _ = _≡_.refl
  ... | yes c=b = contradiction c=b c≠b

-- This simple-minded induction principle allows for short proofs of
-- several properties about transp.
  transp-induction : ∀ {ℓP} (P : Carrier → Set ℓP) →
                     ∀ a b c →
                     (c ≈ a → P b) →
                     (c ≉ a → c ≈ b → P a) →
                     (c ≉ a → c ≉ b → P c) →
                     P ((transp a b) c)
  transp-induction P a b c P-eq1 P-eq2 P-eq3 with a ≟ c
  ... | yes a=c rewrite transp-eq₁ b (sym a=c) = P-eq1 (sym a=c)
  ... | no a≠c with b ≟ c
  ... | yes b=c rewrite transp-eq₂ (≉-sym a≠c) (sym b=c) = P-eq2 (≉-sym a≠c) (sym b=c)
  ... | no b≠c rewrite transp-eq₃ (≉-sym a≠c) (≉-sym b≠c) = P-eq3 (≉-sym a≠c) (≉-sym b≠c)

  transp-id : ∀ a b c → a ≈ b → (transp a b) c ≈ c
  transp-id a b c a=b = transp-induction (_≈ c) a b c
    (λ c=a → trans (sym a=b) (sym c=a))
    (λ _ c=b → trans a=b (sym c=b))
    (λ _ _ → refl)


-- These four lemmas are inversions because we deduce some information
-- about the atoms involved from information about the swapping.
  transp-inv₁ : ∀ a b c → transp a b c ≈ a → b ≈ c
  transp-inv₁ a b c = transp-induction (λ x → x ≈ a → b ≈ c) a b c
     (λ c=a b=a → trans b=a (sym c=a))
     (λ _ b=c _ → sym b=c)
     (λ c≠a _ c=a → ⊥-elim (c≠a c=a))

  transp-inv₂ : ∀ a b c → transp a b c ≉ a → transp a b c ≈ b → a ≈ c
  transp-inv₂ a b c = transp-induction (λ x → x ≉ a → x ≈ b → a ≈ c) a b c
    (λ c=a _ _ → sym c=a)
    (λ _ _ a≠a _ → contradiction refl a≠a)
    (λ _ c≠b _ c=b → contradiction c=b c≠b)

  transp-inv₂' : ∀ a b c → transp a b c ≈ b → a ≈ c
  transp-inv₂' a b c = transp-induction (λ x → x ≈ b → a ≈ c) a b c
    (λ a=c _ → sym a=c)
    (λ c≠a c=b a=b → trans a=b (sym c=b))
    (λ c≠a c≠b c=b → ⊥-elim (c≠b c=b))

  transp-inv₃ : ∀ a b c → transp a b c ≉ a → transp a b c ≉ b → transp a b c ≈ c
  transp-inv₃ a b c = transp-induction (λ x → x ≉ a → x ≉ b → x ≈ c) a b c
    (λ _ _ b≠b → ⊥-elim (b≠b refl))
    (λ _ _ a≠a → ⊥-elim (a≠a refl))
    (λ _ _ _ _ → refl)

-- Swapping is commutative.
  transp-comm : ∀ a b c → (transp a b) c ≈ (transp b a) c
  transp-comm a b c with a ≟ b
  ... | yes a=b = trans (transp-id a b c a=b) (sym (transp-id b a c (sym a=b)))
  ... | no a≠b = transp-induction (transp a b c ≈_) b a c
      (λ c=b → reflexive (transp-eq₂ (≉-sym (≉-resp-≈₂ (sym c=b) a≠b)) c=b))
      (λ c≠b c=a → reflexive (transp-eq₁ b c=a))
      (λ c≠b c≠a → reflexive (transp-eq₃ c≠a c≠b))

  transp-eq₁' : ∀ a {b} {c} → c ≈ b → transp a b c ≈ a
  transp-eq₁' a {b} {c} c=b = trans (transp-comm a b c)
                                    (reflexive (transp-eq₁ a c=b))

-- it is involutive.
  transp-involutive : ∀ a b → Involutive _≈_ (transp a b)
  transp-involutive a b c = transp-induction (_≈ c) a b (transp a b c)
    (transp-inv₁ a b c)
    (transp-inv₂ a b c)
    (transp-inv₃ a b c)

-- and preserves the equality.
  transp-respects-≈ : ∀ a b → (transp a b) Preserves _≈_ ⟶ _≈_
  transp-respects-≈ a b {c} {d} c≈d = transp-induction (transp a b c ≈_) a b d
    (λ d=a → reflexive (transp-eq₁ b (trans c≈d d=a)))
    (λ d≠a d=b → reflexive (transp-eq₂ (≉-resp-≈₁ c≈d d≠a) (trans c≈d d=b)))
    (λ d≠a d≠b → trans (reflexive (transp-eq₃ ((≉-resp-≈₁ c≈d d≠a)) ((≉-resp-≈₁ c≈d d≠b)))) c≈d)


  transp-cancel' : ∀ a b c d → d ≉ b → d ≉ c → transp c b (transp a c d) ≈ transp a b d
  transp-cancel' a b c d d≠b d≠c = transp-induction (λ x → transp c b (transp a c d) ≈ x) a b d
    (λ d=a → trans (transp-respects-≈ c b (reflexive (transp-eq₁ c d=a))) (reflexive (transp-eq₁ b refl)))
    (λ d≠a d=b → ⊥-elim (d≠b d=b))
    (λ d≠a d≠b → trans (transp-respects-≈ c b (reflexive (transp-eq₃ d≠a d≠c)))
                       (reflexive (transp-eq₃ d≠c d≠b)))

  transp-cancel : ∀ a b c e → a ≉ b → a ≉ c → b ≉ c →
    transp a b e ≈ ((transp a c) ∘ (transp b c) ∘ (transp a c)) e
  transp-cancel a b c e a≠b a≠c b≠c = transp-induction
        (λ x → x ≈ ((transp a c) ∘ (transp b c) ∘ (transp a c)) e) a b e
        (sym ∘ eq₁)
        (λ e≠a → sym ∘ (eq₂ e≠a))
        (λ e≠a → sym ∘ (eq₃ e≠a))
        where
        open ≈-Reasoning setoid
        eq-ctx : ∀ {x y} → x ≈ y → transp a c (transp b c x) ≈ transp a c (transp b c y)
        eq-ctx x=y = transp-respects-≈ a c (transp-respects-≈ b c x=y)
        eq₁ : e ≈ a → transp a c (transp b c (transp a c e)) ≈ b
        eq₁ e=a = begin
          transp a c (transp b c (transp a c e))
          ≈⟨ eq-ctx (reflexive (transp-eq₁ c e=a)) ⟩
          transp a c (transp b c c)
          ≈⟨ transp-respects-≈ a c (transp-eq₁' b refl) ⟩
          transp a c b
          ≈⟨ reflexive (transp-eq₃ (≉-sym a≠b) b≠c) ⟩
          b ∎
        eq₂ : e ≉ a → e ≈ b → transp a c (transp b c (transp a c e)) ≈ a
        eq₂ e≠a e=b = begin
          transp a c (transp b c (transp a c e))
          ≈⟨ eq-ctx (reflexive (transp-eq₃ e≠a (≉-resp-≈₁ e=b b≠c))) ⟩
          transp a c (transp b c e)
          ≈⟨ transp-respects-≈ a c (reflexive (transp-eq₁ c e=b)) ⟩
          transp a c c
          ≈⟨ transp-eq₁' a refl ⟩
          a ∎
        eq₃ : e ≉ a → e ≉ b → transp a c (transp b c (transp a c e)) ≈ e
        eq₃ e≠a e≠b with e ≟ c
        ... | yes e=c = begin
          transp a c (transp b c (transp a c e))
          ≈⟨ eq-ctx (transp-eq₁' a e=c) ⟩
          transp a c (transp b c a)
          ≈⟨ transp-respects-≈ a c (reflexive (transp-eq₃ a≠b a≠c)) ⟩
          transp a c a
          ≈⟨ reflexive (transp-eq₁ c refl) ⟩
          c
          ≈⟨ sym e=c ⟩
          e ∎

        ... | no e≠c = begin
          transp a c (transp b c (transp a c e))
          ≈⟨ eq-ctx (reflexive (transp-eq₃ e≠a e≠c)) ⟩
          transp a c (transp b c e)
          ≈⟨ transp-respects-≈ a c (reflexive (transp-eq₃ e≠b e≠c)) ⟩
          transp a c e
          ≈⟨ reflexive (transp-eq₃ e≠a e≠c) ⟩
          e ∎

-- Finite Permutations
-- -------------------
--
-- A finite permutation can be given by a composition of
-- transpositions (alternatively we can think of a finite permutation
-- given by a composition of disjoint cycles).

-- We introduce a representation of composition of swappings; this is
-- different from other presentations because we don't fix how they
-- associate.

  data FinPerm : Set ℓ where
    Id : FinPerm
    Comp : (fp fq : FinPerm) → FinPerm
    Swap : (a b : Carrier) → FinPerm

  -- Given a representation of a finite permutation, we can produce
  -- a permutation; although we don't prove it should be obvious that
  -- the domain of ⟦ p ⟧ is finite.
  ⟦_⟧ : FinPerm → Perm
  ⟦ Id ⟧ = idₚ setoid
  ⟦ Comp p q ⟧ =  ⟦ q ⟧ ∘ₚ ⟦ p ⟧
  ⟦ Swap a b ⟧ = record
    { f = transp a b
    ; f⁻¹ = transp a b
    ; cong₁ = transp-respects-≈ a b
    ; cong₂ = transp-respects-≈ a b
    ; inverse = transp-involutive a b , transp-involutive a b
    }


  -- We obtain some properties of transp for free, because it is
  -- a permutation.
  transp-injective : ∀ a b → Injective _≈_ _≈_  (transp a b)
  transp-injective a b = perm-injective ⟦ Swap a b ⟧

  transp-distributive-perm : ∀ (π : Perm) a b c →
    transp (f π a) (f π b) (f π c) ≈ f π ((transp a b) c)
  transp-distributive-perm π a b c = transp-induction (λ x → x ≈ (f π ∘ transp a b) c) (f π a) (f π b) (f π c)
    (λ πc=πa → cong₁ π (sym (reflexive (transp-eq₁ b (perm-injective π πc=πa)))))
    (λ πc≠πa πc=πb → cong₁ π (sym (reflexive (transp-eq₂ (perm-injective' π πc≠πa) (perm-injective π πc=πb)))))
    (λ πc≠πa πc≠πb → cong₁ π (sym (reflexive (transp-eq₃ (perm-injective' π πc≠πa) (perm-injective' π πc≠πb)))))

  transp-distributive : ∀ a b c d e →
    transp a b (transp c d e) ≈ transp (transp a b c) (transp a b d) (transp a b e)
  transp-distributive a b c d e = sym (transp-distributive-perm ⟦ Swap a b ⟧ c d e)


  -- We can think of FinPerm as codes for finite permutations.  In
  -- order to define the group of finite permutation we can take, at
  -- least, two approaches: let the carrier be FinPerm and then the
  -- equality would be the equality of the associated permutations or,
  -- and this is what we prefer, take the carrier as the image of ⟦_⟧.
  -- Yet another conception would be using finite maps where we have
  -- {a ↦ b , b ↦ a} for (transp a b).

  -- The inverse of a FinPerm swaps the swaps and also
  -- swaps the inverses in the compositions.
  _⁻¹ᵖ : (p : FinPerm) → ∃ (λ q → (⟦ p ⟧ ⁻¹) ≈ₚ ⟦ q ⟧)
  Id ⁻¹ᵖ = Id , λ _ → refl
  Swap a b ⁻¹ᵖ = Swap a b , (λ _ → refl)
  Comp p q ⁻¹ᵖ with  p ⁻¹ᵖ | q ⁻¹ᵖ
  ... | p' , eqp | q' , eqq = Comp q' p' , λ x →
      begin
      f⁻¹ ⟦ q ⟧ (f⁻¹ ⟦ p ⟧ x)
      ≈⟨ cong₂ ⟦ q ⟧ (eqp x) ⟩
      f⁻¹ ⟦ q ⟧ (f ⟦ p' ⟧ x)
      ≈⟨ eqq (f ⟦ p' ⟧ x) ⟩
      (f ⟦ q' ⟧ (f ⟦ p' ⟧ x)) ∎
    where open ≈-Reasoning setoid

  -- This is our carrier, we use capital letters to refer to the
  -- image of ⟦_⟧ on the whole FinPerm. Notice that we could have
  -- used the _∋-Image_ type.

  PERM : Set (ℓ ⊔ ℓ')
  PERM = Σ[ p ∈ Perm ] (Σ[ q ∈ FinPerm ] ( p ≈ₚ ⟦ q ⟧))

  ID : PERM
  ID = idₚ setoid , Id , λ _ → refl

  _⁻¹P : Op₁ PERM
  (p , code , eq) ⁻¹P = p ⁻¹
                    , proj₁ (code ⁻¹ᵖ)
                    , λ x → begin
      f⁻¹ p x
    ≈⟨ cong-⁻¹ {p} {⟦ code ⟧} eq x ⟩
      f⁻¹ ⟦ code ⟧ x
    ≈⟨ proj₂ (code ⁻¹ᵖ) x ⟩
      f ⟦ proj₁ (code ⁻¹ᵖ) ⟧ x ∎
    where open ≈-Reasoning setoid

  _∘P_ : Op₂ PERM
  (p , code , eq) ∘P (q , code' , eq') =
      q ∘ₚ p
    , Comp code code'
    , λ x → trans (cong₁ p (eq' x)) (eq (f ⟦ code' ⟧ x))

  SWAP : Carrier → Carrier → PERM
  SWAP a b = ⟦ Swap a b ⟧ , Swap a b , λ x → refl

  toPERM : (p : FinPerm) → PERM
  toPERM Id = ID
  toPERM (Comp p q) = toPERM p ∘P toPERM q
  toPERM (Swap a b) = SWAP a b

  toPERM-corr : ∀ p → proj₁ (proj₂ (toPERM p)) ≡ p
  toPERM-corr Id = _≡_.refl
  toPERM-corr (Comp p q) rewrite toPERM-corr p | toPERM-corr q = _≡_.refl
  toPERM-corr (Swap a b) = _≡_.refl

  toPERM-eq : ∀ p → proj₁ (toPERM p) ≡ ⟦ p ⟧
  toPERM-eq Id = _≡_.refl
  toPERM-eq (Comp p q) rewrite toPERM-eq p | toPERM-eq q = _≡_.refl
  toPERM-eq (Swap a b) = _≡_.refl

  toPERM-eq' : ∀ p → proj₁ (toPERM p) ≈ₚ ⟦ p ⟧
  toPERM-eq' p x rewrite toPERM-eq p = refl

  toPERM-eq'' : ∀ (π : PERM) → proj₁ π ≈ₚ proj₁ (toPERM (proj₁ (proj₂ π)))
  toPERM-eq'' π x rewrite toPERM-eq (proj₁ (proj₂ π)) = proj₂ (proj₂ π) x

  Perm-A : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  Perm-A = record
            { Carrier = PERM
            ; _≈_ = _≈ₚ_ on proj₁
            ; _∙_ = _∘P_
            ; ε = ID
            ; _⁻¹ = _⁻¹P
            ; isGroup = record {
                isMonoid = record {
                  isSemigroup = record {
                  isMagma = record {
                    isEquivalence = record {
                        refl = λ _ → refl
                      ; sym = λ x → sym ∘ x
                      ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂)
                    } ;
                    ∙-cong = λ {f} {g} {h} {k} f=g h=k →
                      Group.∙-cong Sym-A {proj₁ h} {proj₁ k} {proj₁ f} {proj₁ g} h=k f=g
                  }
                  ; assoc = λ _ _ _ _ → refl
                  }
                ; identity = (λ _ _ → refl) , λ _ _ → refl
                }
              ; inverse = Inverse.inverseʳ ∘ proj₁ , Inverse.inverseˡ ∘ proj₁
              ; ⁻¹-cong = λ {f} {g} → Group.⁻¹-cong Sym-A {proj₁ f} {proj₁ g}
              }
            }

  ⁻¹ₚ-eq : ∀ (p q : FinPerm) →  (⟦ Comp p q ⟧ ⁻¹) ≈ₚ ((⟦ p ⟧ ⁻¹) ∘ₚ (⟦ q ⟧  ⁻¹))
  ⁻¹ₚ-eq p q x = refl

  inv-eq : ∀ p x → f⁻¹ ⟦ p ⟧ x ≈ f (⟦ p ⟧ ⁻¹) x
  inv-eq p x = refl

  open Membership A-setoid
  open List-Extra.Extra setoid

  -- Ideally we would like to have a function that removes redundant
  -- information from FinPerms. Since the set of atoms appearing in
  -- FinPerm is computable and we can test if each of them is in the
  -- domain of the permutation, we can keep only those. Then we compute
  -- the composition of permutations.

  -- TODO: define a function norm : FinPerm → FinPerm that removes
  -- redundant information and prove it correct.

  _≡A_ = _≡_ {A = Carrier}

  _∈-dom_ : Carrier → Perm → Set ℓ'
  a ∈-dom π = f π a ≉ a

  ∈-dom? : (p : Perm) → (x : Carrier) → Dec (x ∈-dom p)
  ∈-dom? p x = ¬? (f p x ≟ x)

  -- Strict equality
  _∉-dom!_ : Carrier → Perm → Set ℓ
  a ∉-dom! π = f π a ≡A a

  _∉-dom_ : Carrier → Perm → Set ℓ'
  a ∉-dom π = f π a ≈ a

  atoms : FinPerm → List Carrier
  atoms Id = []
  atoms (Comp p q) = atoms p ++ atoms q
  atoms (Swap a b) = a ∷ b ∷ []

  at-swap : ∀ a b → a ∈ atoms (Swap a b) × b ∈ atoms (Swap a b)
  at-swap a b = here refl , there (here refl)

  ∈-atoms? : (p : FinPerm) → (x : Carrier) → Dec (x ∈ atoms p)
  ∈-atoms? p x = x ∈? (atoms p)

  atoms' : FinPerm → List Carrier
  atoms' p = filter (∈-dom? ⟦ p ⟧) (atoms p)

  atomsₚ : PERM → List Carrier
  atomsₚ = atoms' ∘ proj₁ ∘ proj₂

  ∈-dom-resp-≈ : (π : Perm) → (_∈-dom π) Respects _≈_
  ∈-dom-resp-≈ π {x} {y} x≈y x∈domp y∉domp = x∈domp x∉domp
    where x∉domp : f π x ≈ x
          x∉domp = trans (cong₁ π x≈y) (trans y∉domp (sym x≈y))

  ∉-dom-resp-≈ : (π : Perm) → (_∉-dom π) Respects _≈_
  ∉-dom-resp-≈ π {x} {y} x≈y x∈domp  = trans (cong₁ π (sym x≈y)) (trans x∈domp x≈y)

  ∈-dom⇒∈-dom-f : (π : Perm) → {a : Carrier} → (a ∈-dom π) → f π a ∈-dom π
  ∈-dom⇒∈-dom-f π {a} a∈domp fa∉domp = a∈domp (perm-injective π fa∉domp)

  ∉-∉⁻¹ : ∀ {q a} → a ∉-dom ⟦ q ⟧ → f⁻¹ ⟦ q ⟧ a ≈ a
  ∉-∉⁻¹ {q} {a} a∉dom = trans (sym (cong₂ ⟦ q ⟧ a∉dom)) (Inverse.inverseʳ ⟦ q ⟧ a)

  ∉-atoms-∉! : ∀ {q a} → a ∉ atoms q → a ∉-dom! ⟦ q ⟧
  ∉-atoms-∉! {Id} {a} a∉at = _≡_.refl
  ∉-atoms-∉! {Swap b c} {a} a∉at =
    transp-eq₃ (∉-∷⁼ (Any.here refl) a∉at)
               (∉-∷⁼ (Any.there (Any.here refl)) a∉at)
  ∉-atoms-∉! {Comp p q} {a} a∉at = goal -- goal
    where
    a∉q = ∉-atoms-∉! {q} {a} (∉-++⁻ʳ (atoms p) a∉at)
    goal : a ∉-dom! (⟦ q ⟧ ∘ₚ ⟦ p ⟧)
    goal rewrite a∉q = ∉-atoms-∉! {p} (∉-++⁻ˡ (atoms p) a∉at)

  ∉-atoms-∉ : ∀ {q a} → a ∉ atoms q → a ∉-dom ⟦ q ⟧
  ∉-atoms-∉ {q} {a} a∉at = reflexive (∉-atoms-∉! {q} a∉at)

  ∉-atoms'-∉ : ∀ q {a} → a ∉ atoms' q → a ∉-dom ⟦ q ⟧
  ∉-atoms'-∉ q {a} a∉atq with ∈-atoms? q a
  ... | yes a∈atq = decidable-stable (f ⟦ q ⟧ a ≟ a) (p a∉atq)
    where
    open List-Extra
    p = ∉-filter⁻ setoid (∈-dom? ⟦ q ⟧) (∈-dom-resp-≈ ⟦ q ⟧) {xs = atoms q} a∈atq
  ... | no a∉atq = ∉-atoms-∉ {q} a∉atq

  ∉-∉-atoms : ∀ q {a} → a ∉-dom ⟦ q ⟧ → a ∉ atoms' q
  ∉-∉-atoms p a∉dom a∈at = proj₂ q a∉dom
    where q = ∈-filter⁻ setoid (∈-dom? ⟦ p ⟧) (∈-dom-resp-≈ ⟦ p ⟧) {xs = atoms p} a∈at

  comp-id : ∀ a p q → a ∉-dom ⟦ q ⟧ → f ⟦ Comp p q ⟧ a ≈ f ⟦ p ⟧ a
  comp-id a p q ∉dom = cong₁ ⟦ p ⟧ ∉dom

  comp-id₂ : ∀ a p q → f ⟦ q ⟧ a ∉-dom ⟦ p ⟧ → f ⟦ Comp p q ⟧ a ≈ f ⟦ q ⟧ a
  comp-id₂ a p q ∉dom = ∉dom

-- TODO: move this to Setoid-Extra

  ∈-PERM : (P : PERM) → (_∈-dom (proj₁ P)) ↔ (_∈-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∈-PERM (π , p , eq) = (λ {a} a∈domπ a∉domp → a∈domπ (trans (eq a) a∉domp)) ,
                          λ {a} a∈domp a∉domπ → a∈domp (trans (sym (eq a)) a∉domπ)

  ∉-PERM : (P : PERM) → (_∉-dom (proj₁ P)) ↔ (_∉-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∉-PERM (π , p , eq) = (λ {a} → trans (sym (eq a))) , λ {a} → trans (eq a)

  -- Cycle representation
  -----------------------
  module _ where
    open import Data.Nat hiding (_⊔_;_≟_;_^_)
    open import Data.Unit.Polymorphic renaming (⊤ to ⊤ₚ;tt to ttₚ) hiding (_≟_)

    -- TODO: use a better representation; I tried to use Fresh lists
    -- but some proofs where difficult (or impossible).
    Cycle : Set ℓ
    Cycle = List Carrier

  -- TODO: this can be used to ensure that cycles are disjoint.
    -- Alternatively, one can use Disjoint from the stdlib composed
    -- with toList :: Cycle → List Carrier.
    Disj : Rel Cycle (ℓ ⊔ ℓ')
    Disj [] ρ' = ⊤ₚ
    Disj (a ∷ ρ) [] = ⊤ₚ
    Disj (a ∷ ρ) (b ∷ ρ') = a ≉ b × a ∉ ρ' × b ∉ ρ × Disj ρ ρ'

    disj-∈ : ∀ ρ ρ' a → a ∈ ρ → Disj ρ ρ' → a ∉ ρ'
    disj-∈ (x ∷ ρ) [] a a∈ρ rel = λ ()
    disj-∈ (x ∷ ρ) (x₁ ∷ ρ') a (here px) (u , a≉b , a∉ρ' , disj) =
      ∉-∷⁺ (≉-resp-≈₁ px u) (∉-resp-≈ setoid (sym px) a≉b)
    disj-∈ (x ∷ ρ) (x₁ ∷ ρ') a (there a∈ρ) (_ , a≉b , a∉ρ' , disj) =
      ∉-∷⁺ (≉-sym (∉-∷⁼ a∈ρ a∉ρ')) (disj-∈ ρ ρ' a a∈ρ disj)

    open import Data.Unit.Polymorphic using (tt)

    disj-tl : ∀ ρ ρ' a → Disj (a ∷ ρ) ρ' → Disj ρ ρ'
    disj-tl [] ρ' a disj = tt
    disj-tl (x ∷ ρ) [] a disj = tt
    disj-tl (x ∷ ρ) (x₁ ∷ ρ') a (u , v , w , z ) =
      ≉-sym (∉-∷⁼ (here refl) w) , disj-∈ (x ∷ ρ) ρ' x (here refl) z , ∉-∷⁼ᵗ w , disj-tl ρ ρ' x z

    -- We get rid of identities.
    comp : Op₂ FinPerm
    comp p Id = p
    comp p (Comp q q') = Comp p (Comp q q')
    comp p (Swap a b) = Comp p (Swap a b)

    comp-corr : ∀ p q → ⟦ comp p q ⟧ ≈ₚ ⟦ Comp p q ⟧
    comp-corr p Id =  λ x → refl
    comp-corr p (Comp q q₁) = λ x → refl
    comp-corr p (Swap a b) = λ x → refl

    comp-corr' : ∀ p q a → f⁻¹ ⟦ comp p q ⟧ a ≈ f⁻¹ ⟦ Comp p q ⟧ a
    comp-corr' p Id a = refl
    comp-corr' p (Comp q q₁) a = refl
    comp-corr' p (Swap a₁ b) a = refl

    -- We assume that each cycle doesn't contain repeated elements.
    cycle-to-FP : Cycle → FinPerm
    cycle-to-FP [] = Id
    cycle-to-FP (a ∷ []) = Id
    cycle-to-FP (a ∷ as@(b ∷ _)) = comp (Swap a b) (cycle-to-FP as)

    -- We assume that each cycle doesn't contain repeated elements.
    cycle-to-FP' : Carrier → Cycle → FinPerm
    cycle-to-FP' _ [] = Id
    cycle-to-FP' a (b ∷ as) = comp (Swap a b) (cycle-to-FP' b as)

    cycle-to-FP'' : Cycle → FinPerm
    cycle-to-FP'' [] = Id
    cycle-to-FP'' (x ∷ as) = cycle-to-FP' x as

    eqcy : ∀ x ρ → cycle-to-FP (x ∷ ρ) ≡ cycle-to-FP' x ρ
    eqcy x [] = _≡_.refl
    eqcy x (x₁ ∷ ρ) = ih (eqcy x₁ ρ)
       where
       ih : ∀ {a a'} → a ≡ a' → comp (Swap x x₁) a ≡  comp (Swap x x₁) a'
       ih eq rewrite eq = _≡_.refl

    eq'cy : ∀ ρ → cycle-to-FP ρ ≡ cycle-to-FP'' ρ
    eq'cy [] = _≡_.refl
    eq'cy (x ∷ ρ) = eqcy x ρ

    -- cycle-atoms
    cycle-atoms : ∀ a as → a ∉ as → a ∉-dom ⟦ cycle-to-FP as ⟧
    cycle-atoms a [] a∉as = refl
    cycle-atoms a (x ∷ []) a∉as = refl
    cycle-atoms a (x ∷ x₁ ∷ as) a∉as = trans (comp-corr ((Swap x x₁)) (cycle-to-FP (x₁ ∷ as)) a)
      (trans ((comp-id a (Swap x x₁) (cycle-to-FP (x₁ ∷ as)) (cycle-atoms a (x₁ ∷ as) a∉tl)))
        (reflexive (transp-eq₃ (∉-∷⁼ (here refl) a∉as) (∉-∷⁼ (there (here refl)) a∉as))))
      where a∉tl : a ∉ (x₁ ∷ as)
            a∉tl = ∉-∷⁼ᵗ a∉as

    cycle-atoms' : ∀ a as c → c ≉ a → c ∉ as → c ∉-dom ⟦ cycle-to-FP' a as ⟧
    cycle-atoms' a [] c a≉c c∉xs = refl
    cycle-atoms' b (a ∷ as) c b≉c c∉xs = begin
      f ⟦ comp P Q ⟧ c
      ≈⟨ comp-corr P Q c ⟩
      f ⟦ Comp P Q ⟧ c
      ≈⟨ transp-respects-≈ b a (cycle-atoms' a as c c≉a (∉-∷⁼ᵗ c∉xs)) ⟩
      f ⟦ P ⟧ c
      ≈⟨ reflexive (transp-eq₃ b≉c c≉a) ⟩
      c ∎
      where
      open ≈-Reasoning setoid
      P = Swap b a
      Q = cycle-to-FP' a as
      c≉a : c ≉ a
      c≉a = ∉-∷⁼ (here refl) c∉xs

    -- We assume that cycles are disjoint.
    to-FP : List Cycle → FinPerm
    to-FP [] = Id
    to-FP (ρ ∷ ρs) = comp (cycle-to-FP ρ) (to-FP ρs)

    _^_,_ : Perm → ℕ → Carrier → Carrier
    p ^ ℕ.zero , a = a
    p ^ suc n , a with a ≟ (f p (p ^ n , a))
    ... | yes _ = p ^ n , a
    ... | no _ = f p (p ^ n , a)

    cycle : Perm → ℕ → (a : Carrier) → Cycle × Carrier
    cycle p ℕ.zero a = f p a ∷  [] , f p a
    cycle p (suc n) a with cycle p n a
    ... | ρ , aⁿ with a ≟ f p aⁿ
    ... | yes _ = ρ , aⁿ
    ... | no _ = ρ ∷ʳ f p aⁿ , f p aⁿ

    cycle-for-at : ℕ → (a : Carrier) → (π : Perm) → Cycle
    cycle-for-at zero a π with a ≟ f⁻¹ π a
    ... | yes _ = []
    ... | no _ = a ∷ []
    cycle-for-at (suc n) a π with cycle-for-at n a π
    ... | [] = []
    ... | ρ'@(aⁿ ∷ ρ) with a ≟ aⁿ
    ... | yes _ = ρ'
    ... | no an≠a = (f⁻¹ π aⁿ) ∷ ρ'

    Fresh : Pred (List Carrier) (ℓ ⊔ ℓ')
    Fresh = AllPairs _≉_

    open import Data.List.Relation.Unary.All
    open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
    open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any;¬Any⇒All¬)

    data _,_~_,_ (p : Perm)  : (a b : Carrier) → Cycle → Set (ℓ ⊔ ℓ') where
      sing~ : ∀ a → f p a ≉ a → p , a ~ f p a , (f p a ∷ [])
      ∷~ : ∀ a c ρ → f p a ≉ a → a ∉ ρ →
           p , (f p a) ~ c , ρ →
           p , a ~ c , (f p a ∷ ρ)

    ++-~ : ∀ p ρ ρ' a b c → p , a ~ c , ρ → p , c ~ b , ρ' → a ∉ ρ' → Disj ρ ρ' →
      p , a ~ b , (ρ ++ ρ')
    ++-~ p .(f p a ∷ []) ρ' a b .(f p a) (sing~ .a x) rel' a∉ disj = ∷~ a b ρ' x a∉ rel'
    ++-~ p .(f p a ∷ ρ) ρ' a b c (∷~ .a .c ρ x x₁ rel) rel' a∉ disj =
      ∷~ a b (ρ ++ ρ') x (∉-++⁺ ρ x₁ a∉) ih
      where
      ih : p , f p a ~ b , (ρ ++ ρ')
      ih = ++-~ p ρ ρ' (f p a) b c rel rel' {!!} {!!}

    in~ : ∀ p a n → a ∈-dom p → let (ρ , c) = cycle p n a in  p , a ~ c , ρ
    in~ p a zero a∈dom = sing~ {p = p} a a∈dom
    in~ p a (suc n) a∈dom with cycle p n a | inspect (cycle p n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f p aⁿ
    ... | yes a=an = ih'
      where
      ih' : p , a ~ aⁿ , ρ
      ih' rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq)= in~ p a n a∈dom
    ... | no a≠an = ++-~ p ρ (f p aⁿ ∷ []) a (f p aⁿ) aⁿ ih' ih₂ {!!} {!!}
      where
      ih' : p , a ~ aⁿ , ρ
      ih' rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq)= in~ p a n a∈dom
      ih₂ : p , aⁿ ~ f p aⁿ , (f p aⁿ ∷ [])
      ih₂ = in~ p aⁿ ℕ.zero {!!}

    _,_~ᶜ_,_ : (p : Perm) (a b : Carrier) (ρ : Cycle) → Set (ℓ ⊔ ℓ')
    p , a ~ᶜ b , ρ = p , a ~ b , ρ × f p b ≈ a

    ~⇒# : ∀ p ρ a c → p , a ~ c , ρ → a ∉ ρ
    ~⇒# p .(f p a ∷ []) a .(f p a) (sing~ .a x) = All¬⇒¬Any ((≉-sym x) ∷ [])
    ~⇒# p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) = All¬⇒¬Any ((≉-sym x) ∷ (¬Any⇒All¬ ρ x₁))

    ~⇒fresh : ∀ p ρ a c → p , a ~ c , ρ → Fresh ρ
    ~⇒fresh p .(f p a ∷ []) a .(f p a) (sing~ .a x) = [] ∷ []
    ~⇒fresh p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) =
      ¬Any⇒All¬ ρ (~⇒# p ρ (f p a) c rel) ∷ (~⇒fresh p ρ (f p a) c rel)

    ~⇒last : ∀ p ρ a c → p , a ~ c , ρ → c ∈ ρ
    ~⇒last p .(f p a ∷ []) a .(f p a) (sing~ .a x) = here refl
    ~⇒last p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) = there (~⇒last p ρ (f p a) c rel)

    ~⇒h-closed : ∀ p ρ a c → p , a ~ c , ρ → f p a ∈ ρ
    ~⇒h-closed p .(f p a ∷ []) a .(f p a) (sing~ .a x) = here refl
    ~⇒h-closed p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) = here refl

    ~⇒p-closed : ∀ p ρ a c → p , a ~ c , ρ → ∀ b → b ≉ c → b ∈ ρ → f p b ∈ ρ
    ~⇒p-closed p .(f p a ∷ []) a .(f p a) (sing~ .a x) b b≠c (here px) = contradiction px b≠c
    ~⇒p-closed p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) b b≠c (here px) =
      ∈-resp-≈ setoid (sym (cong₁ p px)) (there (~⇒h-closed p ρ (f p a) c rel))
    ~⇒p-closed p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) b b≠c (there b∈ρ) =
      there (~⇒p-closed p ρ (f p a) c rel b b≠c b∈ρ)

    out' : ∀ p ρ a c → p , a ~ c , ρ → ∀ b → b ≉ c → b ∈ (a ∷ ρ) →
      f p b ≈ f ⟦ cycle-to-FP' a ρ ⟧ b
    out' p .(f p a ∷ []) a .(f p a) (sing~ .a _) b b≠c (here b=a) =
      trans (cong₁ p b=a) (sym (reflexive (transp-eq₁ (f p a) b=a)))
    out' p .(f p a ∷ []) a .(f p a) (sing~ .a _) b b≠c (there (here b=a)) = contradiction b=a b≠c
    out' p .(f p a ∷ ρ) a c (∷~ .a .c ρ a≠pa a∉ρ rel) b b≠c (here b=a) = begin
        f p b
      ≈⟨ cong₁ p b=a ⟩
        f p a
      ≈⟨ sym (reflexive (transp-eq₁ (f p a) b=a)) ⟩
        f ⟦ P ⟧ b
      ≈⟨ sym (comp-id b P Q (cycle-atoms' (f p a) ρ b b≉fpa (∉-resp-≈ setoid (sym b=a) a∉ρ))) ⟩
        f ⟦ Comp P Q ⟧ b
      ≈⟨  sym (comp-corr P Q b) ⟩
        f ⟦ comp P Q ⟧ b  ∎
      where
      open ≈-Reasoning setoid
      b≉fpa : b ≉ f p a
      b≉fpa = ≉-resp-≈₁ b=a (≉-sym a≠pa)
      P = Swap a (f p a)
      Q = cycle-to-FP' (f p a) ρ

    out' p .(f p a ∷ ρ) a c R@(∷~ .a .c ρ a≠pa a∉ρ rel) b b≠c (there b∈ρ') =  begin
      f p b
      ≈⟨ ih ⟩
        f ⟦ Q ⟧ b
      ≈⟨ sym (comp-id₂ b P Q (∉-atoms-∉ {q = P} (All¬⇒¬Any (Qb≠a ∷ (Qb≠pa ∷ []))))) ⟩
        f ⟦ Comp P Q ⟧ b
      ≈⟨  sym (comp-corr P Q b) ⟩
        f ⟦ comp P Q ⟧ b  ∎
      where
      open ≈-Reasoning setoid
      open import Data.Sum
      P = Swap a (f p a)
      Q = cycle-to-FP' (f p a) ρ
      ih = out' p ρ (f p a) c rel b b≠c b∈ρ'
      Qb≠a : f ⟦ Q ⟧ b ≉ a
      Qb≠a Qb=a with ∈-++⁻ setoid (f p a ∷ []) b∈ρ'
      ... | inj₁ (here b=pa) = contradiction (∈-resp-≈ setoid (trans (cong₁ p (sym b=pa)) b≈a) j) a∉ρ
        where
        j : f p (f p a) ∈ ρ
        j = ~⇒h-closed p ρ (f p a) c rel
        b≈a : f p b ≈ a
        b≈a = trans ih Qb=a
      ... | inj₂ b∈ρ = contradiction (∈-resp-≈ setoid b≈a (~⇒p-closed p ρ (f p a) c rel b b≠c b∈ρ)) a∉ρ
        where
        b≈a : f p b ≈ a
        b≈a = trans ih Qb=a
      Qb≠pa : f ⟦ Q ⟧ b ≉ f p a
      Qb≠pa Qb=pa = contradiction (∈-resp-≈ setoid b≈a b∈ρ')
                                  (All¬⇒¬Any ((≉-sym a≠pa) ∷ ¬Any⇒All¬ ρ a∉ρ))
        where
        b≈a : b ≈ a
        b≈a = trans  (sym (Inverse.inverseʳ p b))
              (trans (cong₂ p (trans ih Qb=pa))
                     (Inverse.inverseʳ p a))

    out-closed-last : ∀ p ρ a c → p , a ~ c , ρ →
      a ≈ f ⟦ cycle-to-FP' a ρ ⟧ c
    out-closed-last p .(f p a ∷ []) a .(f p a) (sing~ .a x) =
      sym (transp-eq₁' a refl)
    out-closed-last p .(f p a ∷ ρ) a c (∷~ .a .c ρ x x₁ rel) = begin
        a
      ≈⟨ sym (transp-eq₁' a refl) ⟩
        f ⟦ P ⟧ (f p a)
      ≈⟨ cong₁ ⟦ P ⟧ ih  ⟩
        f ⟦ Comp P Q ⟧ c
      ≈⟨  sym (comp-corr P Q c) ⟩
        f ⟦ comp P Q ⟧ c  ∎
      where
      open ≈-Reasoning setoid
      P = Swap a (f p a)
      Q = cycle-to-FP' (f p a) ρ
      ih : f p a ≈ f ⟦ cycle-to-FP' (f p a) ρ ⟧ c
      ih = out-closed-last p ρ (f p a) c rel

    out-closed : ∀ p ρ a c → p , a ~ᶜ c , ρ → ∀ b → b ∈ (a ∷ ρ) →
      f p b ≈ f ⟦ cycle-to-FP' a ρ ⟧ b
    out-closed p ρ a c (rel , pc=a) b b∈ρ' with b ≟ c
    ... | yes b=c = begin
      f p b
      ≈⟨ cong₁ p b=c ⟩
      f p c
      ≈⟨ pc=a ⟩
      a
      ≈⟨ out-closed-last p ρ a c rel ⟩
      f ⟦ cycle-to-FP' a ρ ⟧ c
      ≈⟨ cong₁ ⟦ cycle-to-FP' a ρ ⟧ (sym b=c) ⟩
      f ⟦ cycle-to-FP' a ρ ⟧ b ∎
      where
      open ≈-Reasoning setoid
    ... | no b≠c = out' p ρ a c rel b b≠c b∈ρ'


    -- Given a permutation and a list of atoms we construct the list
    -- of cycles.
    from-atoms : Perm → ℕ → List Carrier → List Cycle → List Cycle
    from-atoms π _ [] ρs = ρs
    from-atoms π n (x ∷ ls) ρs with any? (x ∈?_) ρs
    ... | yes _ = from-atoms π n ls ρs
    ... | no _ = from-atoms π n ls (reverse (cycle-for-at n x π) ∷ ρs)

    fromFP : FinPerm → List Cycle
    fromFP p = from-atoms ⟦ p ⟧ n sup []
      where sup = reverse (atoms' p)
            n = length sup

    norm : FinPerm → FinPerm
    norm = to-FP ∘ fromFP

    RelCycles : REL FinPerm (List Cycle) (ℓ ⊔ ℓ')
    RelCycles p ρs =  ⟦ p ⟧ ≈ₚ ⟦ to-FP ρs ⟧

    norm-corr : (p : FinPerm) → ⟦ p ⟧ ≈ₚ ⟦ norm p ⟧ × atoms' (norm p) ≡ atoms (norm p)
    norm-corr Id = (λ x → refl) , _≡_.refl
    norm-corr (Comp p p₁) = {!!}
    norm-corr (Swap a b) = {!!}


module Ex where
  open import Data.Nat hiding (_^_)
  open import Data.Nat.Properties
  open Perm ≡-decSetoid
  open import Data.List

  ejemplo : FinPerm
  ejemplo = Comp (Swap 1 2) (Swap 1 2)

  -- norm : FinPerm → FinPerm
  -- norm π = π' -- tal que ∀n∈ℕ. π n = π' n ∧ atomos(π') = sup(π')
  --
  -- Propiedad: Si R(π',ρs) ... entonces Q(to-FP ρs)
  -- Propiedad' : R(π,to-cycle π)

  --
  cycle₀ cycle₁ : Cycle
  cycle₀ = 1 ∷ 3 ∷ 5 ∷ 7 ∷ 9 ∷ []
  cycle₁ = 2 ∷ 4 ∷ 6 ∷ []
  cycles : List Cycle
  cycles = cycle₀ ∷ cycle₁ ∷ []
  h = ( (Comp (Swap 1 3) (Swap 3 5)))
  open Func
  open Inverse
  h' : ℕ
  h' = {!cycle ⟦ cycle-to-FP cycle₀ ⟧ 5 9 !}
{-
  test₁ : norm (Comp (Swap 8 8) (to-FP cycles)) ≡
          norm (Comp (Swap 9 9) (to-FP cycles))
  test₁ = _≡_.refl
  h = (Comp (Swap 7 1) (Comp (Swap 1 3) (Swap 3 5)))
  open Func
  open Inverse
  test₂ : norm (Comp (Swap 8 8) (to-FP cycles)) ≡
          Comp (Comp (Swap 2 4) (Swap 4 6))
          (Comp (Swap 1 3) (Comp (Swap 3 5) (Swap 5 7)))
  test₂ = {!!}

  prueba : (List ℕ) × ℕ
  prueba = {!cycle-for-at 0 7 ⟦ h ⟧ !} -- cycle-for-at 0 1 ⟦ h ⟧
  lista : Cycle
  lista = 1 ∷ 1 ∷ []
-}
