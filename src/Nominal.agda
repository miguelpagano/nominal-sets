-- Nominal Sets
-- ============


module Nominal where
open import Level

open import Algebra hiding (Inverse)
open import Data.Empty
open import Data.List
import Data.List.Membership.DecSetoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any
open import Data.Product hiding (map)
open import Data.Sum
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;≢-sym)
open import Relation.Nullary
open import Relation.Unary hiding (_∈_;_∉_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)

open import GroupAction hiding (Id)
import Permutation
open import Setoid-Extra

variable
  ℓ ℓ' ℓx ℓx' ℓP : Level

-- Now we introduce the notion of support; in the following, A-setoid
-- is the set(oid) of atoms.

module Support (A-setoid : DecSetoid ℓ ℓ') where

  open module A-Perm = Permutation.Perm A-setoid
  open Membership A-setoid

  𝔸 : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  𝔸 = Perm-A

  open DecSetoid A-setoid
  A-carrier = Carrier
  open G-Action 𝔸
  module Act-Lemmas {X-set : GSet {ℓ₁ = ℓx} {ℓ₂ = ℓx'}} where
    open A-Sym
    open GSet X-set
    open Inverse
    open SetoidPredicate
    open Func

    private
      _≈X_ = Setoid._≈_ set
      X = Setoid.Carrier set

    -- Now we have a lemma proving that any permutation that
    -- behaves like the identiy acts like it (and analogous for
    -- swapping and compositions).
    id-act : ∀ (π : PERM) (x : X) → proj₁ π ≈ₚ ⟦ Id ⟧ → (π ∙ₐ x) ≈X x
    id-act π x eq = trans-X (congˡ {π} {ID} x eq) (idₐ x)
       where open Setoid set renaming (trans to trans-X)

    swap-act : ∀ (π : PERM) (x : X) a b →
      proj₁ π ≈ₚ ⟦ Swap a b ⟧ →
      (π ∙ₐ x) ≈X ((SWAP a b) ∙ₐ x)
    swap-act π x a b eq = congˡ {π} {SWAP a b} x eq

    comp-act : ∀ (π : PERM) (x : X) p q →
      proj₁ π ≈ₚ ⟦ Comp p q ⟧ →
      (π ∙ₐ x) ≈X (toPERM p ∙ₐ (toPERM q ∙ₐ x))
    comp-act π x p q eq = trans-X (congˡ {π} {toPERM (Comp p q)} x eq')
      (sym-X (compₐ (toPERM p) (toPERM q) x))
      where eq' : proj₁ π ≈ₚ proj₁ (toPERM p ∘P toPERM q)
            eq' x rewrite toPERM-eq p | toPERM-eq q = eq x
            open Setoid set renaming (trans to trans-X;sym to sym-X)


  module Support {ℓx ℓx' : Level}
    {X-set : GSet {ℓ₁ = ℓx} {ℓ₂ = ℓx'}}
    (P : SetoidPredicate {ℓ₃ = ℓP} setoid)
    where

    open Inverse
    open SetoidPredicate
    open Func

    infix 6 _≈X_
    private
      open GSet X-set
      _≈X_ = Setoid._≈_ set
      X = Setoid.Carrier set

    -- The subset (defined by the predicate) P is a support for x (an
    -- element of the (carrier) of the GSet if for every finite
    -- permutation that fixes every element in P acts as the identity
    -- on x. This is (2.1) in Pitts' book.

    is-supp : Pred X (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
    is-supp x = (π : PERM) → (predicate P ⊆ _∉-dom proj₁ π) → π ∙ₐ x ≈X x

    -- Alternatively, we can say that P supports x by using the computable
    -- notion of not being an atom in the domain of the FinPerm.
    private
      is-supp' : Pred X (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
      is-supp' x = (π : PERM) → (predicate P ⊆ (_∉ support (proj₁ (proj₂ π)))) →
        π ∙ₐ x ≈X x

    -- Both notions are equivalent.
      imp : is-supp ⊆ is-supp'
      imp pred π inv = pred π (λ {a} Pa → proj₂ (∉-PERM π)
         (∉-support-∉ (proj₁ (proj₂ π)) (inv {a} Pa)))

      imp' : is-supp' ⊆ is-supp
      imp' pred Π@(π , p , _) inv = pred Π (λ {a} Pa → ∉-∉-atoms p (proj₁ (∉-PERM Π) ((inv {a} Pa))))

    -- Finally, the characterization in terms of swapping: P supports x if,
    -- for every a and b in the complement of P, the action of (SWAP a b) in x
    -- fixes it.
    _supports_ : Pred X (ℓ ⊔ ℓP ⊔ ℓx')
    _supports_ x = ∀ {a b} → a ∉ₛ P → b ∉ₛ P → SWAP a b ∙ₐ x ≈X x

    -- Finally we can prove that is-supp implies supports.
    private
      open Act-Lemmas {X-set = X-set}

      is-supp⊆supports : ∀ x → is-supp x → _supports_ x
      is-supp⊆supports x inv {a} {b} a∉P b∉P = inv (SWAP a b) easy
        where
        easy : predicate P ⊆ (_∉-dom proj₁ (SWAP a b))
        easy {c} c∈P = DecSetoid.reflexive A-setoid (transp-eq₃ c≉a c≉b)
         where
         c≉a : c ≉ a
         c≉a c≈a = a∉P (predWellDef P c≈a c∈P)
         c≉b : c ≉ b
         c≉b c≈b = b∉P (predWellDef P c≈b c∈P)

      -- and also we can prove that it is almost equivalent.
      is-supp₃ : Pred X (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
      is-supp₃ x = ∀ p → predicate P ⊆ (_∉ atoms p) → (toPERM p ∙ₐ x) ≈X x

      supports⊆is-supp₃ : _supports_ ⊆ is-supp₃
      supports⊆is-supp₃ {x} inv Id pred = id-act (toPERM Id) x (λ a → refl)
      supports⊆is-supp₃ {x} inv (Comp p q) pred =
        begin
         toPERM (Comp p q) ∙ₐ x
        ≈⟨ comp-act (toPERM (Comp p q)) x p q (toPERM-eq' (Comp p q)) ⟩
         (toPERM p ∙ₐ (toPERM q ∙ₐ x))
        ≈⟨ congʳ (toPERM p) (supports⊆is-supp₃ {x = x} inv q predq) ⟩
         (toPERM p ∙ₐ x)
        ≈⟨ supports⊆is-supp₃ {x = x} inv p predp ⟩
         x ∎
        where open Setoid set
              open ≈-Reasoning set
              predp : predicate P ⊆ (_∉ atoms p)
              predp {a} Pa a∈atp = pred Pa (∈-++⁺ˡ setoid a∈atp)
              predq : predicate P ⊆ (_∉ atoms q)
              predq {a} Pa a∈atq = pred Pa (∈-++⁺ʳ setoid (atoms p) a∈atq)
      supports⊆is-supp₃ {x} inv (Swap a b) pred =
        inv {a} {b} (λ Pa → pred Pa (proj₁ (at-swap a b))) (λ Pb → pred Pb (proj₂ (at-swap a b)))


      supports⊆is-supp : _supports_ ⊆ is-supp
      supports⊆is-supp {x} inv π pred =
        Setoid.trans set
          (congˡ x (toPERM-eq-trans π p-norm norm-corr)) sup⊆sup₃
        where
        open Setoid set
        p = proj₁ (proj₂ π)
        p-norm = norm p
        open Thm p
        sup⊆sup₃ = supports⊆is-supp₃ inv p-norm (λ {a} a∈P a∈at → norm-atoms a a∈at (a∉domp a∈P))
          where
          a∉domp : ∀ {a} → a ∈ₛ P  → f ⟦ p ⟧ a A-Sym.≈A a
          a∉domp {a} a∈atP = Setoid.trans setoid (Setoid.sym setoid (proj₂ (proj₂ π) a)) (pred a∈atP)

  -- TODO: Thm. 2.3

  module _ where

    open SetoidPredicate

    -- Now we define the notion of being finite: P is finite if there is
    -- a list enumerating the elements of P (notice that _∈_ takes
    -- into account the underlying equality).

    -- TODO: move this to Setoid-Extra.
    finite : Pred (SetoidPredicate {ℓ₃ = ℓP} setoid) (ℓ ⊔ ℓ' ⊔ ℓP)
    finite P = Σ[ as ∈ List Carrier ] (predicate P ⊆ (_∈ as))

    𝒫f : {ℓpred : Level} → Set (suc (ℓ ⊔ ℓ' ⊔ ℓpred))
    𝒫f {ℓpred} = Σ (SetoidPredicate {ℓ₃ = ℓpred} setoid) finite

    variable
      ℓ₃ ℓ₄ : Level
      S : Setoid ℓ ℓ'
      P : SetoidPredicate {ℓ₃ = ℓ₃} S
      Q : SetoidPredicate {ℓ₃ = ℓ₄} S

    ⊥-finite : finite ⊥ₛ
    ⊥-finite = [] , ⊥-elim

    sing-finite : ∀ a → finite [ a ]ₛ
    sing-finite a = [ a ] , here

    ∩-finite : finite P → finite Q → finite (P ∩ₛ Q)
    ∩-finite {P = P} (xs , P⊆xs) _ = xs , P⊆xs ∘ proj₁

    ∪-finite : finite P → finite Q → finite (P ∪ₛ Q)
    ∪-finite {P = P} {Q = Q} (xs , P⊆xs) (ys , Q⊆ys) = (xs ++ ys) , inclusion
      where
      inclusion : predicate (P ∪ₛ Q) ⊆ (_∈ xs ++ ys)
      inclusion {x = x} (inj₁ x∈P) = ∈-++⁺ˡ setoid (P⊆xs x∈P)
      inclusion {x = x} (inj₂ x∈Q) = ∈-++⁺ʳ setoid xs (Q⊆ys x∈Q)

    -- A Nominal set is a GSet all whose elements are finitely supported.
    record Nominal (X-set : GSet {ℓ₁ = ℓx} {ℓ₂ = ℓx'}) :
                          Set (suc ℓ ⊔ suc ℓ' ⊔ ℓx ⊔ ℓx' ⊔ suc ℓP) where
      open GSet X-set
      open Support {ℓP = ℓP} {X-set = X-set}

      field
        sup : ∀ x → Σ[ P ∈ SetoidPredicate setoid ] (finite P × P supports x)

    open Nominal

    -- Nominal sets
    -- ============

    -- Discrete G-set
    Δ-nominal : Nominal (Δ S)
    sup (Δ-nominal {S = S}) x = ⊥ₛ , ⊥-finite , (λ _ _ → S-refl {x = x})
      where open Setoid S renaming (refl to S-refl)

    open GSet
    open Func
    open Inverse


    private
      variable
        ℓ₁ ℓ₂  ℓQ : Level
        B : GSet {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}
        C : GSet {ℓ₁ = ℓ₃} {ℓ₂ = ℓ₄}
        -- C : GSet {ℓ₁ = ℓ₅} {ℓ₂ = ℓ₆} G

    -- Product of two nominal sets.
    ×-nominal : Nominal {ℓP = ℓP} B →
                Nominal {ℓP = ℓQ} C → Nominal (GSet-× B C)
    sup (×-nominal nom-B nom-C) (x , y) =
        (PB ∪ₛ PC)
      , (∪-finite {P = PB} {Q = PC} finB finC)
      , λ a∉∪ b∉∪ → supB (∉-∪ₛ⁻ˡ PB PC a∉∪) (∉-∪ₛ⁻ˡ PB PC b∉∪)
                     , supC (∉-∪ₛ⁻ʳ PB PC a∉∪) (∉-∪ₛ⁻ʳ PB PC b∉∪)
      where Pb = sup nom-B x ; Pc = sup nom-C y
            PB = proj₁ Pb ; PC = proj₁ Pc
            finB = proj₁ (proj₂ Pb) ; finC = proj₁ (proj₂ Pc)
            supB = proj₂ (proj₂ Pb) ; supC = proj₂ (proj₂ Pc)

    -- The set of atoms is both a G-set and a nominal set.
    𝔸-set : GSet
    set 𝔸-set = setoid
    f (action 𝔸-set) (π , a) = f (proj₁ π) a
    cong (action 𝔸-set) {π , a} {π' , b} (π=π' , a=b) = trans (cong₁ (proj₁ π) a=b) (π=π' b)
    isAction 𝔸-set = record { idₐ = λ x → refl ; compₐ = λ g g' x → refl }

    𝔸-set-nominal : Nominal 𝔸-set
    sup (𝔸-set-nominal) x = [ x ]ₛ , ([ x ] , here) , λ a≠x b≠x → reflexive (transp-eq₃ (≉-sym a≠x) (≉-sym b≠x))
      where open Inequality setoid

    module _ (A : GSet {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}) (B : GSet {ℓ₁ = ℓ₃} {ℓ₄}) where

      open import Setoid-Extra
      open Func
      open ≈-Reasoning (set B)
      infix 8 _∙A_ _∙B_
      private
        open module BSetoid = Setoid (set B)
        _∙A_ = _∙ₐ_ A
        _∙B_ = _∙ₐ_ B
        _∙→_ = _∙ₐ_ (GSet-⇒ A B)
      →-nominal : Nominal (GSet-⇒ A B)
      sup (→-nominal) G = ⊥ₛ , (⊥-finite , λ _ _ → ab∙G[-]=G[-] )
        where
        postulate
          G-equiv : IsEquivariant (action A) (action B) G
        ab∙G[-]=G[-] : ∀ {a b : A-carrier} x → f ((SWAP a b) ∙→ G) x  BSetoid.≈ f G x
        ab∙G[-]=G[-] {a} {b} x = begin
          f (ab ∙→ G) x
          ≈⟨ BSetoid.refl  ⟩
          (ab ∙B f G (ab ′ ∙A x))
          ≈⟨ congʳ B ab (G-equiv x (ab ′)) ⟩
          (ab ∙B (ab ′ ∙B (f G x)))
          ≈⟨ act-inverseʳ B ab (f G x)  ⟩
            f G x
          ∎
          where ab = SWAP a b
