-- Nominal Sets
-- ============

-- Permutations on a setoid form the Symmetry Group.

module Permutation where

open import Level

open import Algebra hiding (Inverse)
open import Data.List
import Data.List.Membership.DecSetoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any
open import Data.Product hiding (map)
open import Function hiding (_↔_)
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality using (_≡_;≢-sym)
  renaming(sym to ≡-sym)
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
                     P (transp a b c)
  transp-induction P a b c P-eq1 P-eq2 P-eq3 with a ≟ c
  ... | yes a=c rewrite transp-eq₁ b (sym a=c) = P-eq1 (sym a=c)
  ... | no a≠c with b ≟ c
  ... | yes b=c rewrite transp-eq₂ (≉-sym a≠c) (sym b=c) = P-eq2 (≉-sym a≠c) (sym b=c)
  ... | no b≠c rewrite transp-eq₃ (≉-sym a≠c) (≉-sym b≠c) = P-eq3 (≉-sym a≠c) (≉-sym b≠c)

  transp-id : ∀ a b c → a ≈ b → transp a b c ≈ c
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
  transp-comm : ∀ a b c → transp a b c ≈ transp b a c
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

  ∈-dom? : (p : FinPerm) → (x : Carrier) → Dec (x ∈-dom ⟦ p ⟧)
  ∈-dom? p x = ¬? (f ⟦ p ⟧ x ≟ x)

  ∈-atoms? : (p : FinPerm) → (x : Carrier) → Dec (x ∈ atoms p)
  ∈-atoms? p x = x ∈? (atoms p)

  atoms' : FinPerm → List Carrier
  atoms' p = filter (∈-dom? p) (atoms p)

  atomsₚ : PERM → List Carrier
  atomsₚ = atoms' ∘ proj₁ ∘ proj₂

  ∈-dom-resp-≈ : (p : FinPerm) → (_∈-dom ⟦ p ⟧) Respects _≈_
  ∈-dom-resp-≈ p {x} {y} x≈y x∈domp y∉domp = x∈domp x∉domp
    where x∉domp : f ⟦ p ⟧ x ≈ x
          x∉domp = trans (cong₁ ⟦ p ⟧ x≈y) (trans y∉domp (sym x≈y))

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
    p = ∉-filter⁻ setoid (∈-dom? q) (∈-dom-resp-≈ q) {xs = atoms q} a∈atq
  ... | no a∉atq = ∉-atoms-∉ {q} a∉atq

  ∉-∉-atoms : ∀ q {a} → a ∉-dom ⟦ q ⟧ → a ∉ atoms' q
  ∉-∉-atoms p a∉dom a∈at = proj₂ q a∉dom
    where q = ∈-filter⁻ setoid (∈-dom? p) (∈-dom-resp-≈ p) {xs = atoms p} a∈at

-- TODO: move this to Setoid-Extra
  _↔_ : ∀ {ℓP ℓQ} → (P : Pred Carrier ℓP) → (Q : Pred Carrier ℓQ) → Set (ℓ ⊔ ℓP ⊔ ℓQ)
  P ↔ Q = ∀ a → (P a → Q a) × (Q a → P a)

  ∈-PERM : (P : PERM) → (_∈-dom (proj₁ P)) ↔ (_∈-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∈-PERM (π , p , eq) a = (λ a∈domπ a∉domp → a∈domπ (trans (eq a) a∉domp)) ,
                           λ a∈domp a∉domπ → a∈domp (trans (sym (eq a)) a∉domπ)

  ∉-PERM : (P : PERM) → (_∉-dom (proj₁ P)) ↔ (_∉-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∉-PERM (π , p , eq) a = trans (sym (eq a)) , trans (eq a)
