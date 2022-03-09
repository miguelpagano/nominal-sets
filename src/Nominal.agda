------------------------------------------------------------
-- Nominal Sets
--
-- Nominal Sets
------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
module Nominal where
open import Level
open import Data.Product hiding (map)
open import Data.List
open import Algebra hiding (Inverse)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;≢-sym)
open import Relation.Nullary
open import Relation.Unary hiding (_∈_;_∉_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)

variable
  ℓ ℓ' ℓx ℓx' ℓP : Level
open import Setoid-Extra

module Support (A-setoid : DecSetoid ℓ ℓ') where

  import Permutation
  open module A-Perm = Permutation.Perm A-setoid
  𝔸 : Group (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
  𝔸 = Perm-A

  open import Data.List.Membership.DecSetoid A-setoid
  open DecSetoid A-setoid
  A-carrier = Carrier

  open import GroupAction hiding (Id)
  module supp {ℓx ℓx' : Level}
    {X-set : G-Set {cℓ = (ℓ ⊔ ℓ') } {ℓ = ℓ ⊔ ℓ'} {ℓ₁ = ℓx} {ℓ₂ = ℓx'} 𝔸}
    (P : SetoidPredicate {ℓ₃ = ℓP} setoid)
    where

    open G-Set X-set
    open G-Action.Action act
    open Inverse
    open SetoidPredicate
    open Func

    _≈X_ = Setoid._≈_ set
    X = Setoid.Carrier set

    is-supp : (x : X) → Set (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
    is-supp x = (π : PERM) → (predicate P ⊆ _∉-dom (proj₁ π)) → (π ∙ₐ x) ≈X x

    private
      is-supp' : (x : X) → Set (ℓ ⊔ ℓ' ⊔ ℓP ⊔ ℓx')
      is-supp' x = (π : PERM) → (predicate P ⊆ (_∉ atoms' (proj₁ (proj₂ π)))) →
        (π ∙ₐ x) ≈X x

      imp : ∀ x → is-supp x → is-supp' x
      imp x pred π inv = pred π (λ {a} Pa → proj₂ (∉-PERM π a)
         (∉-atoms'-∉ (proj₁ (proj₂ π)) (inv {a} Pa)))

      imp' : ∀ x → is-supp' x → is-supp x
      imp' x pred Π@(π , p , _) inv = pred Π (λ {a} Pa → ∉-∉-atoms p (proj₁ (∉-PERM Π a) ((inv {a} Pa))))

    is-supp'' : (x : X) → Set (ℓ ⊔ ℓP ⊔ ℓx')
    is-supp'' x = ∀ (a b : A-carrier) → ¬ (a sats P) → ¬ (b sats P) → ((SWAP a b) ∙ₐ x) ≈X x

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
    comp-act π x p q eq = {!!} -- congˡ {π} {toPERM (Comp p q)} x eq'
      where eq' : proj₁ π ≈ₚ proj₁ (toPERM p ∘P toPERM q)
            eq' x rewrite toPERM-eq p | toPERM-eq q = eq x

    open import Data.Empty
    private
      is-supp⊆is_supp'' : ∀ x → is-supp x → is-supp'' x
      is-supp⊆is_supp'' x inv a b a∉P b∉P = inv (SWAP a b) easy
        where easy : predicate P ⊆ (_∉-dom proj₁ (SWAP a b))
              easy {c} c∈P = DecSetoid.reflexive A-setoid (transp-eq₃ c≉a c≉b)
               where
                c≉a : c ≉ a
                c≉a c≈a = a∉P (predWellDef P c≈a c∈P)
                c≉b : c ≉ b
                c≉b c≈b = b∉P (predWellDef P c≈b c∈P)

      -- by doing this exercise (Lemma 2.2) we discover that some
      -- lemmas should be done for FinPerms and then lifted to PERM.
      is-supp''⊆is-supp : ∀ x → is-supp'' x → (p : FinPerm) → (predicate P ⊆ (_∉ (atoms p)))
        → ((toPERM p) ∙ₐ x) ≈X x
      is-supp''⊆is-supp x inv Id pred = id-act (toPERM Id) x (λ a → refl)
      is-supp''⊆is-supp x inv (Comp p q) pred =
        begin
         toPERM (Comp p q) ∙ₐ x
        ≈⟨ comp-act (toPERM (Comp p q)) x p q (toPERM-eq' (Comp p q)) ⟩
         (toPERM p ∙ₐ (toPERM q ∙ₐ x))
        ≈⟨ congʳ (toPERM p) (is-supp''⊆is-supp x inv q predq) ⟩
         (toPERM p ∙ₐ x)
        ≈⟨ is-supp''⊆is-supp x inv p predp ⟩
         x ∎
        where open Setoid set
              open ≈-Reasoning set
              open import Data.List.Membership.Setoid.Properties
              predp : predicate P ⊆ (_∉ atoms p)
              predp {a} Pa a∈atp = pred Pa (∈-++⁺ˡ setoid a∈atp)
              predq : predicate P ⊆ (_∉ atoms q)
              predq {a} Pa a∈atq = pred Pa (∈-++⁺ʳ setoid (atoms p) a∈atq)
      is-supp''⊆is-supp x inv (Swap a b) pred =
        inv a b (λ Pa → pred Pa (proj₁ (at-swap a b))) (λ Pb → pred Pb (proj₂ (at-swap a b)))

      -- Thm. 2.2 should follow from the previous one, because:
      --  1. π ≈ toPERM (norm p) , p = proj₁ (proj₂ π)
      --  2. atoms (norm p) ≡ atoms' (norm p)
      --  3. atoms' (norm p) ≈ atoms' p
      
      is-supp''⊆is-supp-ok : ∀ x → is-supp'' x → (π : PERM) → (predicate P ⊆ (_∉ (atomsₚ π)))
        → (π ∙ₐ x) ≈X x
      is-supp''⊆is-supp-ok x inv π pred = {!is-supp''⊆is-supp x inv p!}
        where p = proj₁ (proj₂ π)
