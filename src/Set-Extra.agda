module Set-Extra where
open import Level
open import Algebra hiding (Inverse)
open import Data.List
open import Data.List.Properties

open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  renaming (head to head')
import Data.List.Membership.DecSetoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
  using (¬Any[];lift-resp)
open import Data.List.Relation.Unary.All.Properties
  using (All¬⇒¬Any;¬Any⇒All¬;Any¬⇒¬All)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function hiding (_↔_)
open import Function.Construct.Composition renaming (inverse to _∘ₚ_)
open import Function.Construct.Identity renaming (inverse to idₚ)
open import Function.Construct.Symmetry renaming (inverse to _⁻¹)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_;≢-sym;Reveal_·_is_;[_];inspect)
  renaming(sym to ≡-sym;subst to ≡-subst;cong to ≡-cong;trans to ≡-trans)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary hiding (_∈_;_∉_)

open import Setoid-Extra
import List-Extra

private
  variable
    ℓ ℓ' : Level

module Set (A-setoid : DecSetoid ℓ ℓ') where
  open DecSetoid A-setoid
  open import Data.Bool hiding (_≟_;_≤_)
  open import Data.Empty
  open import Data.Nat hiding (_⊔_;_≟_;_^_)

  open Membership A-setoid
  open List-Extra.Extra setoid
  open Inequality setoid

  Fresh : Pred (List Carrier) (ℓ ⊔ ℓ')
  Fresh = AllPairs _≉_

  card : List Carrier → ℕ
  card [] = 0
  card (x ∷ xs) with x ∈? xs
  ... | yes _ = card xs
  ... | no _ = 1 + card xs

  length-fresh=card : ∀ xs → Fresh xs → length xs ≡ card xs
  length-fresh=card [] fr = _≡_.refl
  length-fresh=card (x ∷ xs) (x∉xs ∷ fr) with x ∈? xs
  ... | yes x∈xs = contradiction x∈xs (All¬⇒¬Any x∉xs)
  ... | no _ = ≡-cong (1 +_) (length-fresh=card xs fr)

  _∖[_] : List Carrier → Carrier → List Carrier
  xs ∖[ x ] = filter (¬? ∘ (x ≟_)) xs

  any-cong : ∀ {ℓ ℓP ℓQ} {A : Set ℓ} {xs : List A}
           (P : Pred A ℓP) (Q : Pred A ℓQ) → P ⊆ Q → (Any P xs) → (Any Q xs)
  any-cong P Q sub (here px) = here (sub px)
  any-cong P Q sub (there any₁) = there (any-cong P Q sub any₁)

  ¬any-cong : ∀ {ℓ ℓP ℓQ} {A : Set ℓ} {xs : List A}
           (P : Pred A ℓP) (Q : Pred A ℓQ) → Q ⊆ P → ¬ (Any P xs) → ¬ (Any Q xs)
  ¬any-cong P Q sub nany px = nany (any-cong Q P sub px)


  length-minus-sing : ∀ xs x → Fresh xs → x ∈ xs →
    length xs ≡ 1 + length (xs ∖[ x ])
  length-minus-sing [] x xs# ()
  length-minus-sing (x ∷ xs) y (x# ∷ xs#) (here y=x) = ≡-cong (1 +_) (≡-cong length eq'')
    where
    y# : All (λ z → ¬ y ≈ z) xs
    y# = ¬Any⇒All¬ xs (¬any-cong ((λ z → x ≈ z)) ((λ z → y ≈ z)) (λ x₁ → trans (sym y=x) x₁) (All¬⇒¬Any x#))
    eq' : xs ≡ xs ∖[ y ]
    eq' = ≡-sym (filter-all (¬? ∘ (y ≟_)) y#)
    eq'' : xs ≡ (x ∷ xs) ∖[ y ]
    eq'' with y ≟ x
    ... | yes eq = eq'
    ... | no ¬eq = contradiction y=x ¬eq
  length-minus-sing (x ∷ xs) y (x# ∷ xs#) (there y∈xs) = begin
    length (x ∷ xs)
    ≡⟨ _≡_.refl ⟩
    (1 + length xs)
    ≡⟨ ≡-cong (1 +_) ih ⟩
    1 + length (x ∷ (xs ∖[ y ]))
    ≡⟨ ≡-cong (λ as → 1 + length as) (≡-sym eq') ⟩
    (1 + length ((x ∷ xs) ∖[ y ])) ∎
    where
    open import Relation.Binary.PropositionalEquality hiding (setoid)
    open ≡-Reasoning
    ih = length-minus-sing xs y xs# y∈xs
    eq' : (x ∷ xs) ∖[ y ] ≡ x ∷ (xs ∖[ y ])
    eq' with y ≟ x
    ... | yes p = ⊥-elim (All¬⇒¬Any x# (∈-resp-≈ setoid p y∈xs))
    ... | no ¬q = _≡_.refl

  fresh-minus-sing : ∀ xs x → Fresh xs → Fresh (xs ∖[ x ])
  fresh-minus-sing xs x #xs = filter⁺ ((¬? ∘ (x ≟_))) #xs
    where open import Data.List.Relation.Unary.AllPairs.Properties

  card-minus-sing : ∀ xs x → Fresh xs → x ∈ xs →
    card xs ≡ 1 + card (xs ∖[ x ])
  card-minus-sing xs x xs# x∈xs =
    ≡-trans
      (≡-sym (length-fresh=card xs xs#))
   (≡-trans
     (length-minus-sing xs x xs# x∈xs)
     (≡-cong (1 +_) (length-fresh=card (xs ∖[ x ]) (fresh-minus-sing xs x xs#))))

  card-mono : ∀ xs ys → Fresh xs → Fresh ys → (_∈ xs) ⊆ (_∈ ys) → card xs ≤ card ys
  card-mono [] ys _ _ sub = z≤n
  card-mono (x ∷ xs) ys (x# ∷ xs#) ys# sub with x ∈? xs
  ... | yes _ = card-mono xs ys xs#  ys# (λ z∈xs → sub (there z∈xs))
  ... | no x∉xs = ≤-trans (+-monoʳ-≤ 1 ih) (≤-reflexive (≡-sym (card-minus-sing ys x ys# (sub (here refl)))))
    where
    open import Data.Nat.Properties hiding (_≟_)
    xs⊆ys-[x] : (_∈ xs) ⊆ (_∈ (ys ∖[ x ]))
    xs⊆ys-[x] {z} z∈xs =
      ∈-filter⁺ setoid ((¬? ∘ (x ≟_))) ≉-resp-≈₂ (sub (there z∈xs))
        (λ z=x → ∉-resp-≈ setoid z=x (All¬⇒¬Any x#) z∈xs)
    ih : card xs ≤ card (ys ∖[ x ])
    ih = card-mono xs (ys ∖[ x ]) xs# (fresh-minus-sing ys x ys#) xs⊆ys-[x]

  setify : (xs : List Carrier) → Σ[ as ∈ List Carrier ] (Fresh as × (_∈ xs) ⊆ (_∈ as))
  setify [] = [] , [] , id
  setify (x ∷ xs) with setify xs
  ... | as , #as , incl with x ∈? as
  ... | yes x∈as = as , #as , incl'
    where
    incl' : (_∈ x ∷ xs) ⊆ (_∈ as)
    incl' (here z=x) = ∈-resp-≈ setoid (sym z=x) x∈as
    incl' (there z∈x:xs) = incl z∈x:xs
  ... | no ¬p = (x ∷ as) , ¬Any⇒All¬ as ¬p ∷ #as , incl'
    where
    incl' : (_∈ x ∷ xs) ⊆ (_∈ x ∷ as)
    incl' (here z=x) = here z=x
    incl' (there z∈x:xs) = there (incl z∈x:xs)
