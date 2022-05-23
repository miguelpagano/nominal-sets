-- Nominal Sets
-- ============

-- Permutations on a setoid form the Symmetry Group.
module Permutation where

open import Level renaming (suc to lsuc)

open import Algebra hiding (Inverse)
open import Data.Bool hiding (_≟_;_≤_)
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  renaming (head to head')
import Data.List.Membership.DecSetoid as Membership
open import Data.List.Membership.Setoid.Properties
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Data.List.Relation.Unary.All
  renaming (map to mapAll; tail to tailAll; head to headAll)
open import Data.List.Relation.Unary.All.Properties
  using (All¬⇒¬Any;¬Any⇒All¬;Any¬⇒¬All;¬All⇒Any¬)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
  using (¬Any[];lift-resp;any⁻)
open import Data.Nat hiding (_⊔_;_≟_;_^_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ₚ)
  using (tt)
open import Function hiding (_↔_)
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
  hiding (inverseʳ;inverseˡ)
open import Function.Construct.Identity renaming (inverse to idₚ)
  hiding (inverseʳ;inverseˡ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
  hiding (inverseʳ;inverseˡ)
open import Relation.Binary hiding (Sym)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_;≢-sym;Reveal_·_is_;[_];inspect)
  renaming(sym to ≡-sym;subst to ≡-subst;cong to ≡-cong;trans to ≡-trans)
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to map-dec)
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Relation.Unary hiding (_∈_;_∉_)

open import Setoid-Extra
open import Set-Extra
import List-Extra

variable
  ℓ ℓ' : Level

module Symmetry-Group (A-setoid : Setoid ℓ ℓ') where
  open IsEquivalence
  open Inverse
  open Setoid hiding (_≈_)
  open ≈-Reasoning A-setoid

  _≈A_ = Setoid._≈_ A-setoid
  isEq = isEquivalence A-setoid

  Perm : Set _
  Perm = Inverse A-setoid A-setoid

-- Two permutations are equal if they coincide in every atom.
  _≈ₚ_ : Rel Perm _
  F ≈ₚ G = (x : Carrier A-setoid) → f F x ≈A f G x

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
  open Group renaming (_⁻¹ to _′)
  Sym : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  Carrier Sym = Perm
  _≈_ Sym = _≈ₚ_
  _∙_ Sym = _∘ₚ_
  ε Sym = idₚ A-setoid
  _′ Sym = _⁻¹
  isGroup Sym = record {
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

-- In this module we first define the transposition of atoms,
-- prove that it is an Permutation (a bijection) on the
-- set of atoms and prove several properties about them.
-- Then we define the group of Finite Permutations.

-- TODO:
-- * prove that Perm is a sub-group of Sym.

module Perm (A-setoid : DecSetoid ℓ ℓ') where
  open DecSetoid A-setoid renaming (Carrier to A)
  open module A-Sym = Symmetry-Group setoid hiding (_≈A_)
  open Equality setoid using (≋-refl)

  open Inequality setoid

  open Inverse
  open Set A-setoid

  perm-injective : (π : Perm) → Injective _≈_ _≈_ (f π)
  perm-injective π {c} {d} eq = begin
    c
    ≈⟨ sym (inverseʳ π c) ⟩
    f⁻¹ π (f π c)
    ≈⟨ cong₂ π eq ⟩
    f⁻¹ π (f π d)
    ≈⟨ inverseʳ π d ⟩
    d ∎
    where open ≈-Reasoning setoid

  perm-injective' : (π : Perm) → Injective _≉_ _≉_ (f π)
  perm-injective' π {c} {d} neq c=d = contradiction (cong₁ π c=d) neq

-- Transposition (or swapping) of atoms
-- ------------------------------------

-- Usually, $\mathit{transp}\, a\,b$ is written $(a\ b)$.
  transp : (a b c : A) → A
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
  transp-induction : ∀ {ℓP} (P : A → Set ℓP) →
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
    Comp : (p q : FinPerm) → FinPerm
    Swap : (a b : A) → FinPerm

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

  open Membership A-setoid
  open List-Extra.Extra setoid

  -- Ideally we would like to have a function that removes redundant
  -- information from FinPerms. Since the set of atoms appearing in
  -- FinPerm is computable and we can test if each of them is in the
  -- domain of the permutation, we can keep only those. Then we compute
  -- the composition of permutations.

  -- TODO: define a function norm : FinPerm → FinPerm that removes
  -- redundant information and prove it correct.

  _∈-dom_ : A → Perm → Set ℓ'
  a ∈-dom π = f π a ≉ a

  ∈-dom? : (p : Perm) → (x : A) → Dec (x ∈-dom p)
  ∈-dom? p x = ¬? (f p x ≟ x)

  -- Strict equality
  _∉-dom!_ : A → Perm → Set ℓ
  a ∉-dom! π = f π a ≡A a
    where _≡A_ = _≡_ {A = A}

  _∉-dom_ : A → Perm → Set ℓ'
  a ∉-dom π = f π a ≈ a

  ¬∈-dom⇒∉-dom : {π : Perm} → (¬_ ∘ (_∈-dom π)) ⊆ (_∉-dom π)
  ¬∈-dom⇒∉-dom {π} {a} ¬a∈dom = decidable-stable (f π a ≟ a) ¬a∈dom

  atoms : FinPerm → List A
  atoms Id = []
  atoms (Comp p q) = atoms p ++ atoms q
  atoms (Swap a b) with a ≟ b
  ... | yes _ = a ∷ []
  ... | no _ = a ∷ b ∷ []

  at-swap : ∀ a b → a ∈ atoms (Swap a b) × b ∈ atoms (Swap a b)
  at-swap a b  with a ≟ b
  ... | yes a=b = here refl , here (sym a=b)
  ... | no _ = here refl , there (here refl)

  at-swap⁻ : ∀ a b {c} → c ∈ atoms (Swap a b) → c ≈ a ⊎ c ≈ b
  at-swap⁻ a b {c} c∈at with a ≟ b
  at-swap⁻ a b {c} (here c=a) | yes _ = inj₁ c=a
  at-swap⁻ a b {c} (here c=a) | no _ = inj₁ c=a
  at-swap⁻ a b {c} (there (here c=b)) | no _ = inj₂ c=b

  at-swap-∉ : ∀ {a b c} → c ≉ a → c ≉ b → c ∉ atoms (Swap a b)
  at-swap-∉ {a} {b} c≠a c≠b c∈ with at-swap⁻ a b c∈
  ... | inj₁ c=a = contradiction c=a c≠a
  ... | inj₂ c=b = contradiction c=b c≠b

  ∉-at-swap : ∀ {a b c} → c ∉ atoms (Swap a b) → c ≉ a × c ≉ b
  ∉-at-swap {a} {b} {c} c∉ =
      (λ x → c∉ (∈-resp-≈ setoid (sym x) (proj₁ (at-swap a b))))
    , (λ x → c∉ (∈-resp-≈ setoid (sym x) (proj₂ (at-swap a b))))

  ∈-atoms? : (p : FinPerm) → (x : A) → Dec (x ∈ atoms p)
  ∈-atoms? p x = x ∈? (atoms p)

  support : FinPerm → List A
  support p = filter (∈-dom? ⟦ p ⟧) (atoms p)

  ∈-dom-resp-≈ : (π : Perm) → (_∈-dom π) Respects _≈_
  ∈-dom-resp-≈ π {x} {y} x≈y x∈domp y∉domp = x∈domp x∉domp
    where x∉domp : f π x ≈ x
          x∉domp = trans (cong₁ π x≈y) (trans y∉domp (sym x≈y))

  ∉-dom-resp-≈ : (π : Perm) → (_∉-dom π) Respects _≈_
  ∉-dom-resp-≈ π {x} {y} x≈y x∈domp  = trans (cong₁ π (sym x≈y)) (trans x∈domp x≈y)

  ∈-dom⇒∈-dom-f : (π : Perm) → {a : A} → (a ∈-dom π) → f π a ∈-dom π
  ∈-dom⇒∈-dom-f π {a} a∈domp fa∉domp = a∈domp (perm-injective π fa∉domp)

  ∉-∉⁻¹ : ∀ {q a} → a ∉-dom ⟦ q ⟧ → f⁻¹ ⟦ q ⟧ a ≈ a
  ∉-∉⁻¹ {q} {a} a∉dom = trans (sym (cong₂ ⟦ q ⟧ a∉dom)) (inverseʳ ⟦ q ⟧ a)

  ∉-atoms-∉! : ∀ {q a} → a ∉ atoms q → a ∉-dom! ⟦ q ⟧
  ∉-atoms-∉! {Id} {a} a∉at = _≡_.refl
  ∉-atoms-∉! {Swap b c} {a} a∉at = transp-eq₃
    (proj₁ (∉-at-swap a∉at))
    (proj₂ (∉-at-swap a∉at))

  ∉-atoms-∉! {Comp p q} {a} a∉at = goal -- goal
    where
    a∉q = ∉-atoms-∉! {q} {a} (∉-++⁻ʳ (atoms p) a∉at)
    goal : a ∉-dom! (⟦ q ⟧ ∘ₚ ⟦ p ⟧)
    goal rewrite a∉q = ∉-atoms-∉! {p} (∉-++⁻ˡ (atoms p) a∉at)

  ∉-atoms-∉ : ∀ {q a} → a ∉ atoms q → a ∉-dom ⟦ q ⟧
  ∉-atoms-∉ {q} {a} a∉at = reflexive (∉-atoms-∉! {q} a∉at)

  ∉-support-∉ : ∀ q {a} → a ∉ support q → a ∉-dom ⟦ q ⟧
  ∉-support-∉ q {a} a∉atq with ∈-atoms? q a
  ... | yes a∈atq = decidable-stable (f ⟦ q ⟧ a ≟ a) (p a∉atq)
    where
    open List-Extra
    p = ∉-filter⁻ setoid (∈-dom? ⟦ q ⟧) (∈-dom-resp-≈ ⟦ q ⟧) {xs = atoms q} a∈atq
  ... | no a∉atq = ∉-atoms-∉ {q} a∉atq

  ∉-∉-atoms : ∀ q {a} → a ∉-dom ⟦ q ⟧ → a ∉ support q
  ∉-∉-atoms p a∉dom a∈at = proj₂ q a∉dom
    where q = ∈-filter⁻ setoid (∈-dom? ⟦ p ⟧) (∈-dom-resp-≈ ⟦ p ⟧) {xs = atoms p} a∈at

  ∈-sup-dec : ∀ p a → Dec (a ∈ support p)
  ∈-sup-dec p a = a ∈? (support p)

  atoms! : FinPerm → List A
  atoms! p = proj₁ (setify (support p))

  fresh-atoms! : ∀ p → Fresh (atoms! p)
  fresh-atoms! p with setify (support p)
  ... | ats , ats# , _ = ats#

  dom⊆atoms! : ∀ p → (_∈-dom ⟦ p ⟧) ⊆ (_∈ atoms! p)
  dom⊆atoms! p {a} a∈dom with setify (support p)
  ... | ats , _ , sub , _ with a ∈? support p
  ... | yes p = sub p
  ... | no ¬q = contradiction (∉-support-∉ p ¬q) a∈dom

  dom⊇atoms! : ∀ p → (_∈ atoms! p) ⊆ (_∈-dom ⟦ p ⟧)
  dom⊇atoms! p {a} a∈at with setify (support p)
  ... | ats , _ , _ , sub = proj₂ (∈-filter⁻ setoid (∈-dom? ⟦ p ⟧) (∈-dom-resp-≈ ⟦ p ⟧) {xs = atoms p} (sub a∈at))

  _is-supp-of_ : List A → Perm → Set (ℓ ⊔ ℓ')
  xs is-supp-of π = Fresh xs × ((_∈-dom π) ⊆ (_∈ xs))

  fp-supp : ∀ p → atoms! p is-supp-of ⟦ p ⟧
  fp-supp p = fresh-atoms! p , dom⊆atoms! p

  _⊆ₛ_ : Rel FinPerm (ℓ ⊔ ℓ')
  p ⊆ₛ q = All (λ a → f ⟦ p ⟧ a ≈ f ⟦ q ⟧ a) (support p)

  ?⊆ₛ : ∀ p q → Dec (p ⊆ₛ q)
  ?⊆ₛ p q = all? (λ a → f ⟦ p ⟧ a ≟ f ⟦ q ⟧ a) (support p)

  _≈ₛ_ : Rel FinPerm (ℓ ⊔ ℓ')
  p ≈ₛ q = p ⊆ₛ q × q ⊆ₛ p

  ≈ₛ-dec : ∀ p q → Dec (p ≈ₛ q)
  ≈ₛ-dec p q = (?⊆ₛ p q) ×-dec (?⊆ₛ q p)

  ⊆ₛ-∈⁻ : ∀ {q p} → q ⊆ₛ p → ∀ {a} → a ∈ support q → f ⟦ q ⟧ a ≈ f ⟦ p ⟧ a
  ⊆ₛ-∈⁻ {q} {p} sub a∈q = all-∈⁻ (support q) sub qx=py a∈q
    where
    qx=py : (λ a → f ⟦ q ⟧ a ≈ f ⟦ p ⟧ a) Respects _≈_
    qx=py b=c qb=pb = trans (cong₁ ⟦ q ⟧ (sym b=c)) (trans qb=pb (cong₁ ⟦ p ⟧ b=c))

  ≈ₛ⇒≈-sup : ∀ p q → q ⊆ₛ p → ∀ a → (a ∉ support p → a ∉ support q)
  ≈ₛ⇒≈-sup p q rel a a∉p a∈q with ∈-filter⁻ setoid (∈-dom? ⟦ q ⟧) (∈-dom-resp-≈ ⟦ q ⟧) {xs = atoms q} a∈q
  ... | a∈atq , qa≉a = contradiction a∉domp (≉-resp-≈₁ (sym qa=pa) qa≉a)
    where
    a∉domp = ∉-support-∉ p a∉p
    qa=pa = ⊆ₛ-∈⁻ {q} {p} rel a∈q

  ≈ₛ⇒≈ₚ : ∀ p q → p ≈ₛ q → ⟦ p ⟧ ≈ₚ ⟦ q ⟧
  ≈ₛ⇒≈ₚ p q (p<q , q<p) a with a ∈? support p
  ... | yes a∈p = ⊆ₛ-∈⁻ {p} {q} p<q a∈p
  ... | no a∉p = trans (∉-support-∉ p a∉p) (sym (∉-support-∉ q (≈ₛ⇒≈-sup p q q<p a a∉p)))

  ≈ₚ⇒≈ₛ : ∀ p q → ⟦ p ⟧ ≈ₚ ⟦ q ⟧ → p ⊆ₛ q
  ≈ₚ⇒≈ₛ p q equ = eq (support p)
    where
    eq : ∀ xs → All (λ x → f ⟦ p ⟧ x ≈ f ⟦ q ⟧ x) xs
    eq [] = []
    eq (x ∷ xs) = equ x ∷ eq xs

  _≟ₚ_ : ∀ p q → Dec (⟦ p ⟧ ≈ₚ ⟦ q ⟧)
  p ≟ₚ q = map′ (≈ₛ⇒≈ₚ p q) (λ p≈q → (≈ₚ⇒≈ₛ p q p≈q) , ≈ₚ⇒≈ₛ q p (sym ∘ p≈q)) (≈ₛ-dec p q)

  -- This is our carrier, we use capital letters to refer to the
  -- image of ⟦_⟧ on the whole FinPerm. Notice that we could have
  -- used the _∋-Image_ type.

  PERM : Set (ℓ ⊔ ℓ')
  PERM = Σ[ p ∈ Perm ] (Σ[ q ∈ FinPerm ] ( p ≈ₚ ⟦ q ⟧))

  ID : PERM
  ID = idₚ setoid , Id , λ _ → refl

  _⁻¹P : Op₁ PERM
  (p , code , eq) ⁻¹P = p ⁻¹  , proj₁ (code ⁻¹ᵖ) , eq'
    where
    open ≈-Reasoning setoid
    eq' : (p ⁻¹) ≈ₚ ⟦ proj₁ (code ⁻¹ᵖ) ⟧
    eq' x = begin
        f⁻¹ p x
      ≈⟨ cong-⁻¹ {p} {⟦ code ⟧} eq x ⟩
        f⁻¹ ⟦ code ⟧ x
      ≈⟨ proj₂ (code ⁻¹ᵖ) x ⟩
        f ⟦ proj₁ (code ⁻¹ᵖ) ⟧ x ∎

  _∘P_ : Op₂ PERM
  (p , code , eq) ∘P (q , code' , eq') =
      q ∘ₚ p
    , Comp code code'
    , λ x → trans (cong₁ p (eq' x)) (eq (f ⟦ code' ⟧ x))

  SWAP : A → A → PERM
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

  open Group renaming (_⁻¹ to _′;_≈_ to _≈G_) using (Carrier;_∙_;ε;isGroup)
  Perm-A : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  Carrier Perm-A = PERM
  _≈G_ Perm-A = _≈ₚ_ on proj₁
  _∙_ Perm-A = _∘P_
  ε Perm-A = ID
  _′ Perm-A = _⁻¹P
  isGroup Perm-A = record {
                isMonoid = record {
                  isSemigroup = record {
                  isMagma = record {
                    isEquivalence = record {
                        refl = λ _ → refl
                      ; sym = λ x → sym ∘ x
                      ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂)
                    } ;
                    ∙-cong = λ {f} {g} {h} {k} f=g h=k →
                      Group.∙-cong Sym {proj₁ h} {proj₁ k} {proj₁ f} {proj₁ g} h=k f=g
                  }
                  ; assoc = λ _ _ _ _ → refl
                  }
                ; identity = (λ _ _ → refl) , λ _ _ → refl
                }
              ; inverse = inverseʳ ∘ proj₁ , inverseˡ ∘ proj₁
              ; ⁻¹-cong = λ {f} {g} → Group.⁻¹-cong Sym {proj₁ f} {proj₁ g}
              }

  ⁻¹ₚ-eq : ∀ (p q : FinPerm) →  (⟦ Comp p q ⟧ ⁻¹) ≈ₚ ((⟦ p ⟧ ⁻¹) ∘ₚ (⟦ q ⟧  ⁻¹))
  ⁻¹ₚ-eq p q x = refl

  inv-eq : ∀ p x → f⁻¹ ⟦ p ⟧ x ≈ f (⟦ p ⟧ ⁻¹) x
  inv-eq p x = refl

  atomsₚ : PERM → List A
  atomsₚ = support ∘ proj₁ ∘ proj₂

  comp-id : ∀ a p q → a ∉-dom ⟦ q ⟧ → f ⟦ Comp p q ⟧ a ≈ f ⟦ p ⟧ a
  comp-id a p q ∉dom = cong₁ ⟦ p ⟧ ∉dom

  comp-id₂ : ∀ a p q → f ⟦ q ⟧ a ∉-dom ⟦ p ⟧ → f ⟦ Comp p q ⟧ a ≈ f ⟦ q ⟧ a
  comp-id₂ a p q ∉dom = ∉dom

  ∈-PERM : (P : PERM) → (_∈-dom (proj₁ P)) ↔ (_∈-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∈-PERM (π , p , eq) = (λ {a} a∈domπ a∉domp → a∈domπ (trans (eq a) a∉domp)) ,
                          λ {a} a∈domp a∉domπ → a∈domp (trans (sym (eq a)) a∉domπ)

  ∉-PERM : (P : PERM) → (_∉-dom (proj₁ P)) ↔ (_∉-dom ⟦ proj₁ (proj₂ P) ⟧)
  ∉-PERM (π , p , eq) = (λ {a} → trans (sym (eq a))) , λ {a} → trans (eq a)

  -- Cycle representation
  -----------------------
  module _ where

    -- TODO: use a better representation; I tried to use Fresh lists
    -- but some proofs where difficult (or impossible).
    Cycle : Set ℓ
    Cycle = List A

    -- TODO: this can be used to ensure that cycles are disjoint.
    -- Alternatively, one can use Disjoint from the stdlib composed
    -- with toList :: Cycle → List A.
    Disj : Rel Cycle (ℓ ⊔ ℓ')
    Disj ρ ρ' = All (_∉ ρ') ρ

    disj-[]₁ : ∀ ρ → Disj ρ []
    disj-[]₁ [] = []
    disj-[]₁ (x ∷ ρ) = (λ ()) ∷ (disj-[]₁ ρ)

    disj-tl : ∀ {ρ} {ρ'} {a} → Disj (a ∷ ρ) ρ' → Disj ρ ρ'
    disj-tl {ρ} {ρ'} {a} disj = tailAll disj

    disj-∈ : ∀ {ρ} {ρ'} {a} → a ∈ ρ → Disj ρ ρ' → a ∉ ρ'
    disj-∈ (here a≈x) (x∉ρ' ∷ _) = ∉-resp-≈ setoid (sym a≈x) x∉ρ'
    disj-∈ (there a∈ρ) (_ ∷ disj) = disj-∈ a∈ρ disj

    disj-∉⁺ : ∀ {x a ρ ρ'} → Disj (x ∷ ρ') ρ → a ∉ x ∷ ρ' → x ∉ a ∷ ρ
    disj-∉⁺ {ρ = ρ} disj a∉ρ' = All¬⇒¬Any
      (≉-sym (∉-∷⁻ (here refl) a∉ρ') ∷ ¬Any⇒All¬ ρ (disj-∈ (here refl) disj))

    disj-∷⁺ : ∀ {ρ} {ρ'} {a} → a ∉ ρ' → Disj ρ' ρ → Disj ρ' (a ∷ ρ)
    disj-∷⁺ {ρ} {[]} {a} a∉ρ' disj = []
    disj-∷⁺ {ρ} {x ∷ ρ'} {a} a∉ρ' disj = disj-∉⁺ disj a∉ρ' ∷ (disj-∷⁺ (∉-∷⁻ᵗ a∉ρ') (disj-tl disj))

    disj⁺-sing₂ : ∀ ρ a → a ∉ ρ → Disj ρ (a ∷ [])
    disj⁺-sing₂ ρ a a∉ρ = disj-∷⁺ a∉ρ (disj-[]₁ ρ)

    disj-sym : Symmetric Disj
    disj-sym {y = ρ'} [] = disj-[]₁ ρ'
    disj-sym {y = []} (_ ∷ _) = []
    disj-sym {x = x ∷ ρ} {x' ∷ ρ'} (px ∷ disj) = disj-∷⁺ px (disj-sym disj)

    disj-concat : ∀ ρ ρs → All (Disj ρ) ρs → ∀ a → a ∈ ρ → a ∉ concat ρs
    disj-concat ρ ρs disj a a∈ρ a∈ρs with ∈-concat⁻′ setoid ρs a∈ρs
    disj-concat ρ (x ∷ _) (px ∷ disj) a a∈ρ a∈ρs | ρ' , a∈ρ' , here px₁ = disj-∈ a∈x (disj-sym px) a∈ρ
      where
      a∈x : a ∈ x
      a∈x = ∈-resp-≋ setoid px₁ a∈ρ'
    disj-concat ρ (_ ∷ ρs) (px ∷ disj) a a∈ρ a∈ρs | ρ' , a∈ρ' , there ρ'∈ρs =
      disj-concat ρ ρs disj a a∈ρ (∈-concat⁺′ setoid a∈ρ' ρ'∈ρs)

    disj-concat' : ∀ {ρ} {ρs} → All (Disj ρ) ρs → ∀ {a} → a ∈ concat ρs → a ∉ ρ
    disj-concat' {r} {r₁ ∷ rs} (px ∷ rel) a∈cs a∈r with ∈-concat⁻′ setoid (r₁ ∷ rs) a∈cs
    ... | r' , a∈r' , here r'=r₁ = disj-∈ a∈r px (∈-resp-≋ setoid r'=r₁ a∈r')
    ... | r' , a∈r' , there r'∈rs = disj-concat' rel (∈-concat⁺′ setoid a∈r' r'∈rs) a∈r

    -- We get rid of identities.
    comp : Op₂ FinPerm
    comp p Id = p
    comp p (Comp q q') = Comp p (Comp q q')
    comp p (Swap a b) = Comp p (Swap a b)

    comp-corr : ∀ p q → ⟦ comp p q ⟧ ≈ₚ ⟦ Comp p q ⟧
    comp-corr p Id =  λ x → refl
    comp-corr p (Comp q q₁) = λ x → refl
    comp-corr p (Swap a b) = λ x → refl

    cycle-to-FP' : A → Cycle → FinPerm
    cycle-to-FP' _ [] = Id
    cycle-to-FP' a (b ∷ as) = comp (Swap a b) (cycle-to-FP' b as)

    cycle-to-FP : Cycle → FinPerm
    cycle-to-FP [] = Id
    cycle-to-FP (a ∷ as) = cycle-to-FP' a as

    cycle'-support : ∀ {a as c} → c ≉ a → c ∉ as → c ∉-dom ⟦ cycle-to-FP' a as ⟧
    cycle'-support {as = []} a≉c c∉xs = refl
    cycle'-support {a = b} {as = a ∷ as} {c} b≉c c∉xs = begin
      f ⟦ comp P Q ⟧ c
      ≈⟨ comp-corr P Q c ⟩
      f ⟦ Comp P Q ⟧ c
      ≈⟨ transp-respects-≈ b a (cycle'-support c≉a (∉-∷⁻ᵗ c∉xs)) ⟩
      f ⟦ P ⟧ c
      ≈⟨ reflexive (transp-eq₃ b≉c c≉a) ⟩
      c ∎
      where
      open ≈-Reasoning setoid
      P = Swap b a
      Q = cycle-to-FP' a as
      c≉a : c ≉ a
      c≉a = ∉-∷⁻ (here refl) c∉xs

    cycle-support : ∀ as c → c ∉ as → c ∉-dom ⟦ cycle-to-FP as ⟧
    cycle-support [] c c∉xs = refl
    cycle-support (a ∷ as) c c∉xs = cycle'-support (∉-∷⁻ (here refl) c∉xs) (∉-∷⁻ᵗ c∉xs)

    to-FP : List Cycle → FinPerm
    to-FP [] = Id
    to-FP (ρ ∷ ρs) = comp (cycle-to-FP ρ) (to-FP ρs)

    toFP-support : ∀ ρs c → c ∉ concat ρs → c ∉-dom ⟦ to-FP ρs ⟧
    toFP-support [] c c∉ρs = refl
    toFP-support (ρ ∷ ρs) c c∉ρs = begin
      f ⟦ comp P Q ⟧ c
      ≈⟨ comp-corr P Q c ⟩
      f ⟦ Comp P Q ⟧ c
      ≈⟨ comp-id c P Q (toFP-support ρs c (∉-concat⁻' ρs c∉ρs)) ⟩
      f ⟦ P ⟧ c
      ≈⟨ cycle-support ρ c (∉-concat⁻ (ρ ∷ ρs) c∉ρs (here ≋-refl)) ⟩
      c ∎
      where
      open ≈-Reasoning setoid
      P = cycle-to-FP ρ
      Q = to-FP ρs

    -- Given a finite permutation, computes a prefix for the cycle
    -- starting at the atom a; the second component of the result
    -- is the last element.
    cycle : Perm → ℕ → (a : A) → Cycle × A
    cycle p ℕ.zero a = f p a ∷  [] , f p a
    cycle p (suc n) a with cycle p n a
    ... | ρ , aⁿ with a ≟ f p aⁿ
    ... | yes _ = ρ , aⁿ
    ... | no _ = ρ ∷ʳ f p aⁿ , f p aⁿ

    -- In fact, the last element belongs to the cycle.
    last-in-cycle : (p : Perm) → (n : ℕ) → (a : A) → a ∈-dom p →
      let (ρ , c) = cycle p n a in
      c ∈ ρ
    last-in-cycle p ℕ.zero a a∈p = here refl
    last-in-cycle p (suc n) a a∈p with cycle p n a | inspect (cycle p n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f p aⁿ
    ... | no _  = ∈-++⁺ʳ setoid ρ (here refl)
    ... | yes _ = ih
      where
      ih : aⁿ ∈ ρ
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = last-in-cycle p n a a∈p


    -- The length of the prefix is one more than the fuel
    -- argument if we haven't closed the cycle.
    length-cycle : ∀ π n a →
      let (ρ , c) = cycle π n a in
      f π c ≉ a → length ρ ≡ suc n
    length-cycle π ℕ.zero a πc≠a = _≡_.refl
    length-cycle π (suc n) a πc≠a with cycle π n a | inspect (cycle π n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f π aⁿ
    ... | yes a=πa = contradiction a=πa (≉-sym πc≠a)
    ... | no πan≠a =
      ≡-trans (length-++ ρ) (≡-trans (+-comm (length ρ) 1) (≡-cong suc ih))
      where
      ih : length ρ ≡ suc n
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = length-cycle π n a (≉-sym πan≠a)

    -- Every element of the cycle is the image of a previous one
    -- or the start element (which does not belong to the cycle).
    ∈-cycle⁻ : (p : Perm) → (n : ℕ) → (a : A) → a ∈-dom p →
      let (ρ , c) = cycle p n a in
       ∀ b → b ∈ ρ → f⁻¹ p b ≈ a ⊎ f⁻¹ p b ∈ ρ
    ∈-cycle⁻ p ℕ.zero a a∈p b (here px) = inj₁
      (trans (cong₂ p px) (inverseʳ p a))
    ∈-cycle⁻ p (suc n) a a∈p b px  with cycle p n a | inspect (cycle p n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f p aⁿ
    ... | yes _ = ih b px
      where
      ih : ∀ b → b ∈ ρ → f⁻¹ p b ≈ a ⊎ f⁻¹ p b ∈ ρ
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = ∈-cycle⁻ p n a a∈p
    ... | no a≠paⁿ = sum+ (λ x → x) (∈-++⁺ˡ setoid) ih
      where
      sum+ = Data.Sum.map
      eq₁ = ≡-sym (≡-cong proj₁ eq) ; eq₂ = ≡-sym (≡-cong proj₂ eq)
      aⁿ∈ρ' = last-in-cycle p n a a∈p
      aⁿ∈ρ : aⁿ ∈ ρ
      aⁿ∈ρ rewrite eq₁ | eq₂ = aⁿ∈ρ'
      ih : f⁻¹ p b ≈ a ⊎ f⁻¹ p b ∈ ρ
      ih with ∈-++⁻ setoid ρ px
      ... | inj₂ (here ppaⁿ=paⁿ) =
        inj₂ (∈-resp-≈ setoid (trans (sym (inverseʳ p aⁿ)) (cong₂ p (sym ppaⁿ=paⁿ))) aⁿ∈ρ )
      ... | inj₁ ppaⁿ∈ρ rewrite eq₁ = ∈-cycle⁻ p n a a∈p b ppa'
          where
          ppa' : b ∈ proj₁ (cycle p n a)
          ppa' rewrite ≡-sym eq₁ = ppaⁿ∈ρ

    -- Every element of the cycle is in the domain of the permutation.
    ∈-cycle⇒∈-dom : (p : Perm) → (n : ℕ) → (a : A) → a ∈-dom p →
      let (ρ , c) = cycle p n a
      in (∀ b → b ∈ ρ → b ∈-dom p) × c ∈-dom p
    ∈-cycle⇒∈-dom p ℕ.zero a a∈dom = (λ {b (here px) → ∈-dom-resp-≈ p (sym px) goal })  , goal
      where goal = ∈-dom⇒∈-dom-f p a∈dom
    ∈-cycle⇒∈-dom p (suc n) a a∈dom with cycle p n a | inspect (cycle p n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f p aⁿ
    ... | yes _ = ih
      where
      ih : (∀ b → b ∈ ρ → b ∈-dom p) × aⁿ ∈-dom p
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = ∈-cycle⇒∈-dom p n a a∈dom
    ... | no _ = goal , (∈-dom⇒∈-dom-f p (proj₂ ih))
      where
      ih : (∀ b → b ∈ ρ → b ∈-dom p) × aⁿ ∈-dom p
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = ∈-cycle⇒∈-dom p n a a∈dom
      goal : (b : A) → b ∈ (ρ ∷ʳ f p aⁿ) → b ∈-dom p
      goal b b∈ρ' with ∈-++⁻ setoid ρ b∈ρ'
      ... | inj₁ b∈ρ = proj₁ ih b b∈ρ
      ... | inj₂ (here b=paⁿ) = ∈-dom-resp-≈ p (sym b=paⁿ) (∈-dom⇒∈-dom-f p (proj₂ ih))

    -- The image of the last element doesn't belong to the cycle.
    img-last-not-in-cycle :  (p : Perm) → (n : ℕ) → (a : A) → a ∈-dom p →
      let (ρ , c) = cycle p n a in f p c ∉ ρ
    img-last-not-in-cycle p ℕ.zero a a∈p (here px) = contradiction px (∈-dom⇒∈-dom-f p a∈p)
    img-last-not-in-cycle p (suc n) a a∈p with cycle p n a | inspect (cycle p n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f p aⁿ
    ... | yes _ = ih
      where
      ih : f p aⁿ ∉ ρ
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = img-last-not-in-cycle p n a a∈p
    ... | no a≠paⁿ = ih
      where
      eq₁ = ≡-sym (≡-cong proj₁ eq) ; eq₂ = ≡-sym (≡-cong proj₂ eq)
      ih' : f p aⁿ ∉ ρ
      ih' rewrite eq₁ | eq₂ = img-last-not-in-cycle p n a a∈p
      ih : f p (f p aⁿ) ∉ ρ ∷ʳ f p aⁿ
      ih ppaⁿ∈ρ' with ∈-++⁻ setoid ρ ppaⁿ∈ρ'
      ... | inj₂ (here ppaⁿ=paⁿ) = contradiction ppaⁿ=paⁿ (∈-dom⇒∈-dom-f p aⁿ∈p)
        where
        aⁿ∈p : aⁿ ∈-dom p
        aⁿ∈p rewrite eq₂ = proj₂ (∈-cycle⇒∈-dom p n a a∈p)
      ... | inj₁ ppaⁿ∈ρ = absurd
        where
        paⁿ-inv' = ∈-cycle⁻ p n a a∈p (f p (f p aⁿ)) (≡-subst (f p (f p aⁿ) ∈_) eq₁ ppaⁿ∈ρ)
        paⁿ-inv : f⁻¹ p (f p (f p aⁿ)) ≈ a ⊎ f⁻¹ p (f p (f p aⁿ)) ∈ ρ
        paⁿ-inv rewrite eq₁ = paⁿ-inv'
        absurd : ⊥
        absurd with paⁿ-inv
        ... | inj₁ paⁿ=a = a≠paⁿ (trans (sym paⁿ=a) (inverseʳ p (f p aⁿ)))
        ... | inj₂ paⁿ∈ρ = ih' (∈-resp-≈ setoid (inverseʳ p (f p aⁿ)) paⁿ∈ρ)

    -- Good prefixes of cycles starting on a (not included in the
    -- cycle) and ending in b.
    data _,_~_,_ (π : Perm)  : (a b : A) → Cycle → Set (ℓ ⊔ ℓ') where
      sing~ : ∀ {a} → f π a ≉ a → π , a ~ f π a , (f π a ∷ [])
      ∷~ : ∀ {a c ρ} → f π a ≉ a → a ∉ ρ →
           π , (f π a) ~ c , ρ →
           π , a ~ c , (f π a ∷ ρ)

    -- We can concatenate two good cycles if they are disjoint.
    ++-~ : ∀ π {ρ ρ' a b c} → π , a ~ c , ρ → π , c ~ b , ρ' → a ∉ ρ' → Disj ρ ρ' →
      π , a ~ b , (ρ ++ ρ')
    ++-~ π (sing~ fa≠a) rel' a∉ρ' _ = ∷~ fa≠a a∉ρ' rel'
    ++-~ π (∷~ {ρ = ρ} fa≠a a∉ρ rel) rel' a∉ρ' disj = ∷~ fa≠a (∉-++⁺ ρ a∉ρ a∉ρ') ih
      where
      ih = ++-~ π rel rel' (disj-∈ (here refl) disj) (disj-tl disj)

    -- The prefix calculated by cycle is a good prefix.
    cycle-~ : ∀ π a n → a ∈-dom π → let (ρ , c) = cycle π n a in π , a ~ c , ρ
    cycle-~ π a zero a∈dom = sing~ {π = π} a∈dom
    cycle-~ π a (suc n) a∈dom with cycle π n a | inspect (cycle π n) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f π aⁿ
    ... | yes a=an = ih
      where
      ih : π , a ~ aⁿ , ρ
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq)= cycle-~ π a n a∈dom
    ... | no a≠an = ++-~ π ih ih₂ a≠πaⁿ (disj⁺-sing₂ ρ (f π aⁿ) πaⁿ∉ρ)
      where
      ih : π , a ~ aⁿ , ρ
      ih rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) = cycle-~ π a n a∈dom
      aⁿ∈π : aⁿ ∈-dom π
      aⁿ∈π rewrite ≡-sym (≡-cong proj₂ eq) = proj₂ (∈-cycle⇒∈-dom π n a a∈dom)
      ih₂ : π , aⁿ ~ f π aⁿ , (f π aⁿ ∷ [])
      ih₂ = cycle-~ π aⁿ ℕ.zero aⁿ∈π
      a≠πaⁿ : a ∉ f π aⁿ ∷ []
      a≠πaⁿ (here a=πaⁿ) = contradiction a=πaⁿ a≠an
      πaⁿ∉ρ : f π aⁿ ∉ ρ
      πaⁿ∉ρ rewrite ≡-sym (≡-cong proj₂ eq) | ≡-sym (≡-cong proj₁ eq) =
        img-last-not-in-cycle π n a a∈dom

    -- A closed and good prefix.
    _,_~ᶜ_,_ : (π : Perm) (a b : A) (ρ : Cycle) → Set (ℓ ⊔ ℓ')
    π , a ~ᶜ b , ρ = π , a ~ b , ρ × f π b ≈ a

    -- The starting point doesn't belong to a good cycle.
    ~⇒head-∉ : ∀ π {ρ a c} → π , a ~ c , ρ → a ∉ ρ
    ~⇒head-∉ π (sing~ fa≠a) = All¬⇒¬Any ((≉-sym fa≠a) ∷ [])
    ~⇒head-∉ π (∷~ {ρ = ρ} fa≠a a∉ρ _) = All¬⇒¬Any ((≉-sym fa≠a) ∷ (¬Any⇒All¬ ρ a∉ρ))

    -- But the image of the starting point does belong to the cycle.
    ~⇒h-closed : ∀ π {ρ a c} → π , a ~ c , ρ → f π a ∈ ρ
    ~⇒h-closed π (sing~ _) = here refl
    ~⇒h-closed π (∷~ _ _ _) = here refl

    -- A good prefix is fresh.
    ~⇒fresh : ∀ π {ρ a c} → π , a ~ c , ρ → Fresh ρ
    ~⇒fresh π (sing~ _) = [] ∷ []
    ~⇒fresh π (∷~ {ρ = ρ} _ _ rel) = ¬Any⇒All¬ ρ (~⇒head-∉ π rel) ∷ (~⇒fresh π rel)

    -- From which we conclude that prefixes as computed by cycles are fresh.
    cycle-fresh : ∀ π n a → a ∈-dom π →
      let ρ , c = cycle π n a
      in Fresh ρ
    cycle-fresh π n a a∈π = ~⇒fresh π (cycle-~ π a n a∈π)

    -- If we have a list of atoms for a permutation, we can compute a
    -- closed prefix.
    cycle-closed : ∀ (π : Perm)
      (as : List A)
      (a : A)
      (sup-π : as is-supp-of π)
      (a∈sup : a ∈-dom π) →
      let ρ , aⁿ = cycle π (length as) a in f π aⁿ ≈ a
    cycle-closed π as a sup-π a∈dom with cycle π (length as) a | inspect (cycle π (length as)) a
    ... | ρ , aⁿ | [ eq ] with a ≟ f π aⁿ
    ... | yes eq' = sym eq'
    ... | no a≠πaⁿ = contradiction 1+n≤n 1+n≰n
      where
      fresh-as = proj₁ sup-π
      dom⊆sup = proj₂ sup-π
      n = length as
      eq₁ = ≡-sym (≡-cong proj₁ eq) ; eq₂ = ≡-sym (≡-cong proj₂ eq)
      fresh-ρ : Fresh ρ
      fresh-ρ rewrite eq₁ = cycle-fresh π n a a∈dom
      |ρ|=1+n : length ρ ≡ suc (length as)
      |ρ|=1+n rewrite eq₁ | eq₂ = length-cycle π (length as) a (≉-sym a≠πaⁿ)
      |ρ|≤n : card ρ ≤ card as
      |ρ|≤n = card-mono fresh-ρ fresh-as ρ⊆as
        where
        ρ⊆as : (_∈ ρ) ⊆ (_∈ as)
        ρ⊆as {z} z∈ρ rewrite eq₁ = dom⊆sup (proj₁ (∈-cycle⇒∈-dom π n a a∈dom) z z∈ρ)
      1+n≤n : suc n ≤ n
      1+n≤n = ≤-trans
        (≤-reflexive (≡-sym |ρ|=1+n))
        (≤-trans (≤-reflexive (length-fresh=card ρ fresh-ρ))
                 (≤-trans |ρ|≤n (≤-reflexive (≡-sym (length-fresh=card as fresh-as)))))

    -- The last element belongs to the cycle.
    ~⇒last : ∀ π {ρ a c} → π , a ~ c , ρ → c ∈ ρ
    ~⇒last π (sing~ _) = here refl
    ~⇒last π (∷~ _ _ rel) = there (~⇒last π rel)


    -- If an element belongs to the init of the cycle, then its image
    -- also belongs.
    ~⇒img-closed : ∀ π {ρ a c} → π , a ~ c , ρ → ∀ {b} → b ≉ c → b ∈ ρ → f π b ∈ ρ
    ~⇒img-closed π (sing~ _) b≠c (here πx) = contradiction πx b≠c
    ~⇒img-closed π (∷~ _ _ rel) b≠c (here πx) =
      ∈-resp-≈ setoid (sym (cong₁ π πx)) (there (~⇒h-closed π rel))
    ~⇒img-closed π (∷~ _ _ rel) b≠c (there b∈ρ) =
      there (~⇒img-closed π rel b≠c b∈ρ)

    -- The FinPerm computed from a good cycle coincides with the
    -- permutation in all but the last element (including the
    -- starting point).
    out' : ∀ π {ρ} {a} {c} → π , a ~ c , ρ → ∀ {b} → b ≉ c → b ∈ (a ∷ ρ) →
      f π b ≈ f ⟦ cycle-to-FP' a ρ ⟧ b
    out' π (sing~ {a} _) b≠c (here b=a) =
      trans (cong₁ π b=a) (sym (reflexive (transp-eq₁ (f π a) b=a)))
    out' π (sing~ _) b≠c (there (here b=a)) = contradiction b=a b≠c
    out' π (∷~ {a} {_} {ρ} a≠πa a∉ρ rel) {b} b≠c (here b=a) = begin
        f π b
      ≈⟨ cong₁ π b=a ⟩
        f π a
      ≈⟨ sym (reflexive (transp-eq₁ (f π a) b=a)) ⟩
        f ⟦ P ⟧ b
      ≈⟨ sym (comp-id b P Q (cycle'-support b≉fπa (∉-resp-≈ setoid (sym b=a) a∉ρ))) ⟩
        f ⟦ Comp P Q ⟧ b
      ≈⟨  sym (comp-corr P Q b) ⟩
        f ⟦ comp P Q ⟧ b  ∎
      where
      open ≈-Reasoning setoid
      b≉fπa : b ≉ f π a
      b≉fπa = ≉-resp-≈₁ b=a (≉-sym a≠πa)
      P = Swap a (f π a)
      Q = cycle-to-FP' (f π a) ρ

    out' π R@(∷~ {a} {_} {ρ} a≠πa a∉ρ rel) {b} b≠c (there b∈ρ') =  begin
      f π b
      ≈⟨ ih ⟩
        f ⟦ Q ⟧ b
      ≈⟨ sym (comp-id₂ b P Q (∉-atoms-∉ {q = P} (at-swap-∉ Qb≠a Qb≠πa))) ⟩
        f ⟦ Comp P Q ⟧ b
      ≈⟨  sym (comp-corr P Q b) ⟩
        f ⟦ comp P Q ⟧ b  ∎
      where
      open ≈-Reasoning setoid
      P = Swap a (f π a)
      Q = cycle-to-FP' (f π a) ρ
      ih = out' π rel b≠c b∈ρ'
      Qb≠a : f ⟦ Q ⟧ b ≉ a
      Qb≠a Qb=a with ∈-++⁻ setoid (f π a ∷ []) b∈ρ'
      ... | inj₁ (here b=πa) = contradiction (∈-resp-≈ setoid (trans (cong₁ π (sym b=πa)) b≈a) j) a∉ρ
        where
        j : f π (f π a) ∈ ρ
        j = ~⇒h-closed π rel
        b≈a : f π b ≈ a
        b≈a = trans ih Qb=a
      ... | inj₂ b∈ρ = contradiction (∈-resp-≈ setoid b≈a (~⇒img-closed π rel b≠c b∈ρ)) a∉ρ
        where
        b≈a : f π b ≈ a
        b≈a = trans ih Qb=a
      Qb≠πa : f ⟦ Q ⟧ b ≉ f π a
      Qb≠πa Qb=πa = contradiction (∈-resp-≈ setoid b≈a b∈ρ')
                                  (All¬⇒¬Any ((≉-sym a≠πa) ∷ ¬Any⇒All¬ ρ a∉ρ))
        where
        b≈a : b ≈ a
        b≈a = trans  (sym (inverseʳ π b))
              (trans (cong₂ π (trans ih Qb=πa))
                     (inverseʳ π a))

    -- For the last element, we know that the action of the FinPerm is
    -- the starting point.
    out-closed-last : ∀ π {ρ a c} → π , a ~ c , ρ →
      a ≈ f ⟦ cycle-to-FP' a ρ ⟧ c
    out-closed-last π (sing~ {a} _) = sym (transp-eq₁' a refl)
    out-closed-last π (∷~ {a} {c} {ρ} _ _ rel) = begin
        a
      ≈⟨ sym (transp-eq₁' a refl) ⟩
        f ⟦ P ⟧ (f π a)
      ≈⟨ cong₁ ⟦ P ⟧ ih  ⟩
        f ⟦ Comp P Q ⟧ c
      ≈⟨  sym (comp-corr P Q c) ⟩
        f ⟦ comp P Q ⟧ c  ∎
      where
      open ≈-Reasoning setoid
      P = Swap a (f π a)
      Q = cycle-to-FP' (f π a) ρ
      ih : f π a ≈ f ⟦ cycle-to-FP' (f π a) ρ ⟧ c
      ih = out-closed-last π rel

    -- The previous two lemmas allows us to deduce the correctness for
    -- closed and good prefixes.
    out-closed : ∀ π {ρ a c} → π , a ~ᶜ c , ρ → ∀ {b} → b ∈ (a ∷ ρ) →
      f π b ≈ f ⟦ cycle-to-FP' a ρ ⟧ b
    out-closed π {ρ} {a} {c} (rel , πc=a) {b} b∈ρ' with b ≟ c
    ... | yes b=c = begin
      f π b
      ≈⟨ cong₁ π b=c ⟩
      f π c
      ≈⟨ πc=a ⟩
      a
      ≈⟨ out-closed-last π rel ⟩
      f ⟦ cycle-to-FP' a ρ ⟧ c
      ≈⟨ cong₁ ⟦ cycle-to-FP' a ρ ⟧ (sym b=c) ⟩
      f ⟦ cycle-to-FP' a ρ ⟧ b ∎
      where
      open ≈-Reasoning setoid
    ... | no b≠c = out' π rel b≠c b∈ρ'

    out-closed-fresh : ∀ {ρ a b} → b ∉ (a ∷ ρ) →
      b ≈ f ⟦ cycle-to-FP' a ρ ⟧ b
    out-closed-fresh b∉aρ = sym (cycle'-support (contr ∘ here) (contr ∘ there))
      where
      contr = flip contradiction b∉aρ

    out-inv : ∀ π {ρ a c b} →
      π , a ~ c , ρ →
      b ∈ ρ →
      f⁻¹ π b ∈ (a ∷ ρ)
    out-inv π (sing~ {a} _) (here px) = here (trans (cong₂ π px) (inverseʳ π a))
    out-inv π (∷~ {a} _ _ rel) (here px) = here (trans (cong₂ π px) (inverseʳ π a))
    out-inv π (∷~ _ _ rel) (there b∈) = there (out-inv π rel b∈)

    out-closed-inv : ∀ π {ρ a c b} →
      π , a ~ᶜ c , ρ →
      b ∈ (a ∷ ρ) →
      f⁻¹ π b ∈ (a ∷ ρ)
    out-closed-inv π {r} {a} {c} {b} (rel , closed) (here px) = ∈-resp-≈ setoid c=a' (there c∈r)
      where
      c∈r : c ∈ r
      c∈r = ~⇒last π rel
      c=a' : c ≈ f⁻¹ π b
      c=a' = begin
          c
        ≈⟨ sym (inverseʳ π c)  ⟩
          f⁻¹ π (f π c)
        ≈⟨ cong₂ π (out-closed π (rel , closed) (there c∈r))  ⟩
          f⁻¹ π (f ⟦ cycle-to-FP' a r ⟧ c)
        ≈⟨ cong₂ π (sym (out-closed-last π rel)) ⟩
          f⁻¹ π a
        ≈⟨ cong₂ π (sym px) ⟩
          f⁻¹ π b  ∎
        where
        open ≈-Reasoning setoid
    out-closed-inv π (rel , closed) (there px) = out-inv π rel px

    out-closed-fresh' : ∀ π {ρ a c b} →
      π , a ~ᶜ c , ρ →
      b ∉ (a ∷ ρ) →
      f π b ∉ (a ∷ ρ)
    out-closed-fresh' π {r} {a} {b = b} rel b∉ πb∈ = b∉ (∈-resp-≈ setoid (inverseʳ π b) b∈ar)
      where
      b∈ar : f⁻¹ π (f π b) ∈ (a ∷ r)
      b∈ar = out-closed-inv π rel πb∈

    disj-cycles : ∀ {π a b c d ρ ρ'} →
           π , a ~ c , ρ →
           π , b ~ᶜ d , ρ' →
           a ∉ (b ∷ ρ') →
           Disj (a ∷ ρ) (b ∷ ρ')
    disj-cycles {π} (sing~ {a} _) (rel' , b=πd) a∉ =
        (a∉ ∷ (λ x₁ → a∉ (∈-resp-≈ setoid (inverseʳ π a)
         (out-closed-inv π (rel' , b=πd) x₁))) ∷ [])
    disj-cycles {π} (∷~ {a} _ _ rel) (rel' , b=πd) a∉ =
      a∉ ∷ (disj-cycles rel ((rel' , b=πd)) ((λ x₁ → a∉ (∈-resp-≈ setoid (inverseʳ π a)
        (out-closed-inv π (rel' , b=πd) x₁)))))

    -- Given a permutation and a list of atoms we construct the list
    -- of cycles.
    to-cycles : Perm → ℕ → List A → List Cycle → List Cycle
    to-cycles π _ [] ρs = ρs
    to-cycles π n (x ∷ ls) ρs with any? (x ∈?_) ρs
    ... | yes _ = to-cycles π n ls ρs
    ... | no _ = to-cycles π n ls ((x ∷ proj₁ (cycle π n x)) ∷ ρs)

    private
        atoms-to-cycles : ∀ π n as rs y → y ∈ concat rs → y ∈ concat (to-cycles π n as rs)
        atoms-to-cycles π n [] rs y y∈ats = y∈ats
        atoms-to-cycles π n (x ∷ as) rs y y∈ats with any? (x ∈?_) rs
        ... | yes _ = atoms-to-cycles π n as rs y y∈ats
        ... | no _ = atoms-to-cycles π n as (r' ∷ rs) y (∈-++⁺ʳ setoid r' y∈ats)
          where
          r' = (x ∷ proj₁ (cycle π n x))

    ∈-atoms-to-cycles : ∀ π n as rs y → y ∈ as → y ∈ concat (to-cycles π n as rs)
    ∈-atoms-to-cycles π n (x ∷ as) rs y (here eq) with any? (x ∈?_) rs
    ... | yes ci = atoms-to-cycles π n as rs y (∈-resp-≈ setoid (sym eq) (∈-concat⁺ setoid ci))
    ... | no _ = atoms-to-cycles π n as ( ((x ∷ proj₁ (cycle π n x)) ∷ rs)) y
      (∈-concat⁺ setoid {xss = (x ∷ proj₁ (cycle π n x)) ∷ rs} (here  (here eq)))
    ∈-atoms-to-cycles π n (x ∷ as) rs y (there y∈ats) with any? (x ∈?_) rs
    ... | yes ci = ∈-atoms-to-cycles π n as rs y y∈ats
    ... | no _ = ∈-atoms-to-cycles π n as ( ((x ∷ proj₁ (cycle π n x)) ∷ rs)) y y∈ats

    data _~*_ (π : Perm) : List Cycle → Set (ℓ ⊔ ℓ') where
      []* : π ~* []
      ∷* : ∀ {a c ρ ρs} → π ~* ρs →
           π , a ~ᶜ c , ρ →
           All (Disj (a ∷ ρ)) ρs →
           π ~* ((a ∷ ρ) ∷ ρs)

    private
      disj-cycles* : ∀ {π} {a} {c} {ρ} {ρs} →
             π , a ~ᶜ c , ρ →
             π ~* ρs →
             a ∉ concat ρs →
             All (Disj (a ∷ ρ)) ρs
      disj-cycles* _ []* _ = []
      disj-cycles* {a = a} rel (∷* {a₁} {_} {ρ₁} {ρs}  rel* rel' _) a∉ =
        disj-cycles (proj₁ rel) rel' (∉-concat⁻ (((a₁ ∷ ρ₁) ∷ ρs)) a∉ (here ≋-refl)) ∷
        (disj-cycles* rel rel* (∉-concat⁻' {a} {a₁ ∷ ρ₁} ρs a∉))

      cycles-~* : ∀ π {rs} as a → π ~* rs → as is-supp-of π →
        a ∈-dom π →
        a ∉ concat rs →
        π ~* ((a ∷ proj₁ (cycle π (length as) a)) ∷ rs)
      cycles-~* π as a rel sup a∈ a∉rs = ∷* {π = π} rel (i , πc=a) r-disj-rs
        where
        r = proj₁ (cycle π (length as) a)
        c = proj₂ (cycle π (length as) a)
        i = cycle-~ π a (length as) a∈
        πc=a : f π c ≈ a
        πc=a = cycle-closed π as a sup a∈
        r-disj-rs = disj-cycles* (i , πc=a) rel a∉rs

    from-atoms-~* : ∀ π {rs} as {bs} → π ~* rs →
       as is-supp-of π →
       (_∈ bs) ⊆ (_∈-dom π) →
       π ~* to-cycles π (length as) bs rs
    from-atoms-~* π as {[]} rel sup bs⊆as = rel
    from-atoms-~* π {rs} as {x ∷ bs} rel sup bs⊆as with any? (x ∈?_) rs
    ... | yes _ = from-atoms-~* π as rel sup (bs⊆as ∘ there)
    ... | no x∉rs = from-atoms-~* π as
          (cycles-~* π as x rel sup (bs⊆as (here refl))
          (∉-concat⁺ rs x∉rs)) sup (bs⊆as ∘ there)

    ~*-out : ∀ π {ρs} → π ~* ρs → (∀ {a} → a ∈ concat ρs → f π a ≈ f ⟦ to-FP ρs ⟧ a)
    ~*-out π {ρs'@((b ∷ ρ) ∷ ρs)} (∷* rels rel disj) {a} a∈ρs with ∈-concat⁻′ setoid ρs' a∈ρs
    ... | ρ' , a∈ρ' , here ρ'=bρ =
      begin
        f π a
      ≈⟨ out-closed π rel (∈-resp-≋ setoid ρ'=bρ a∈ρ') ⟩
        f ⟦ P ⟧ a
      ≈⟨ sym (comp-id a P Q (toFP-support ρs a a∉c[ρs]))  ⟩
        f ⟦ Comp P Q ⟧ a
      ≈⟨  sym (comp-corr P Q a) ⟩
        f ⟦ comp P Q ⟧ a  ∎
      where
      open ≈-Reasoning setoid
      P = cycle-to-FP' b ρ
      Q = to-FP ρs
      a∉c[ρs] : a ∉ concat ρs
      a∉c[ρs] = disj-concat (b ∷ ρ) ρs disj a (∈-resp-≋ setoid ρ'=bρ a∈ρ')
    ... | ρ' , a∈ρ' , there ρ'∈lρs' =
      begin
        f π a
      ≈⟨ ih  ⟩
        f ⟦ Q ⟧ a
      ≈⟨ sym (comp-id₂ a P Q (∉-dom-resp-≈ ⟦ P ⟧ ih πa∉domP))  ⟩
        f ⟦ Comp P Q ⟧ a
      ≈⟨  sym (comp-corr P Q a) ⟩
        f ⟦ comp P Q ⟧ a  ∎
      where
      open ≈-Reasoning setoid
      P = cycle-to-FP' b ρ
      Q = to-FP ρs
      ih = ~*-out π rels (∈-concat⁺′ setoid a∈ρ' ρ'∈lρs')
      a∉bρ : a ∉ (b ∷ ρ)
      a∉bρ = disj-concat' disj (∈-concat⁺′ setoid a∈ρ' ρ'∈lρs')
      πa∉bρ = out-closed-fresh' π rel a∉bρ
      πa∉domP : f π a ∉-dom ⟦ P ⟧
      πa∉domP = cycle-support (b ∷ ρ) (f π a) πa∉bρ

    ~*-out-fresh : ∀ π {ρs} → π ~* ρs → (∀ {a} → a ∉ concat ρs → a ≈ f ⟦ to-FP ρs ⟧ a)
    ~*-out-fresh π []* _ = refl
    ~*-out-fresh π (∷* {b} {c} {ρ} {ρs} rel x x₁) {a} a∉rs =
          begin
        a
      ≈⟨ ih  ⟩
        f ⟦ Q ⟧ a
      ≈⟨ sym (∉-dom-resp-≈ ⟦ P ⟧ ih πa∉domP)  ⟩
        f ⟦ Comp P Q ⟧ a
      ≈⟨  sym (comp-corr P Q a) ⟩
        f ⟦ comp P Q ⟧ a  ∎
      where
      open ≈-Reasoning setoid
      P = cycle-to-FP' b ρ
      Q = to-FP ρs
      ih = ~*-out-fresh π rel (∉-concat⁻' ρs a∉rs )
      a∉bρ : a ∉ (b ∷ ρ)
      a∉bρ = ∉-concat⁻ ((b ∷ ρ) ∷ ρs) a∉rs (here ≋-refl)
      πa∉domP : a ∉-dom ⟦ P ⟧
      πa∉domP = sym (out-closed-fresh a∉bρ)


    fromFP : FinPerm → List Cycle
    fromFP p = to-cycles ⟦ p ⟧ n sup []
      where sup = atoms! p
            n = length sup

    norm : FinPerm → FinPerm
    norm = to-FP ∘ fromFP

    module Thm (p : FinPerm) where
      ats = atoms! p
      rel = from-atoms-~* ⟦ p ⟧ ats []* (fp-supp p) (dom⊇atoms! p)
      ρs = to-cycles ⟦ p ⟧ (length ats) ats []

      ∈-dom⇒∈ρs : (_∈-dom ⟦ p ⟧) ⊆ (_∈ concat ρs)
      ∈-dom⇒∈ρs {y} y∈dom = ∈-atoms-to-cycles ⟦ p ⟧ (length ats) ats [] y (proj₂ (fp-supp p) y∈dom)

      norm-corr : ⟦ p ⟧ ≈ₚ ⟦ norm p ⟧
      norm-corr x with x ∈? concat ρs
      ... | yes x∈at = ~*-out ⟦ p ⟧ rel x∈at
      ... | no x∉at = trans
          (¬∈-dom⇒∉-dom {⟦ p ⟧} (contraposition ∈-dom⇒∈ρs x∉at))
          (~*-out-fresh ⟦ p ⟧ rel x∉at)

    module Thm' (p : Perm) {ats : List A}
      (is-sup : ats is-supp-of p)
      (incl : (_∈ ats) ⊆ (_∈-dom p)) where

      rel = from-atoms-~* p ats {bs = ats} []* is-sup incl
      ρs = to-cycles p (length ats) ats []

      ∈-dom⇒∈ρs : (_∈-dom p) ⊆ (_∈ concat ρs)
      ∈-dom⇒∈ρs {y} y∈dom = ∈-atoms-to-cycles p (length ats) ats [] y (proj₂ is-sup y∈dom)

      norm-corr : p ≈ₚ ⟦ to-FP ρs ⟧
      norm-corr x with x ∈? concat ρs
      ... | yes x∈at = ~*-out p rel x∈at
      ... | no x∉at = trans
          (¬∈-dom⇒∉-dom { p} (contraposition ∈-dom⇒∈ρs x∉at))
          (~*-out-fresh p rel x∉at)
