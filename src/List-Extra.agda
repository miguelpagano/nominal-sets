------------------------------------------------------------
-- Nominal Sets
--
--
--
-- Taken from
--   https://github.com/miguelpagano/formalmetatheory-nominal-Church-Rosser/tree/agda-stdlib-1.6
------------------------------------------------------------
module List-Extra where

open import Level
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ)
open import Data.List hiding (any)
open import Data.List.Properties
import Data.List.Membership.Setoid as Any
open import Data.List.Membership.Setoid.Properties as AnyProp
open import Data.List.Relation.Unary.Any as AnyDef using ()
open import Data.List.Relation.Unary.Any.Properties hiding (concat⁺)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_)
open AnyDef.Any

module Extra {c ℓ : Level} (A : Setoid c ℓ) where

  open Any A -- renaming (_∈_ to _∈'_;_∉_ to _∉_)
  open Setoid A


  ∉-++⁻ : {v : Carrier} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ xs) × (v ∉ ys)
  ∉-++⁻ xs v∉xs++ys =
        (λ v∈xs → ⊥-elim (v∉xs++ys (++⁺ˡ v∈xs))) ,
        λ v∈ys → ⊥-elim (v∉xs++ys (++⁺ʳ xs v∈ys))

  ∉-++⁺ : {v : Carrier} → ∀ xs {ys} → (v ∉ xs) → (v ∉ ys) → v ∉ (xs ++ ys)
  ∉-++⁺ xs v∉xs v∉ys v∈++ with ∈-++⁻ A xs v∈++
  ... | inj₁ x = v∉xs x
  ... | inj₂ y = v∉ys y

  ∉-++⁻ˡ : {v : Carrier} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ xs)
  ∉-++⁻ˡ xs v∉xs++ys = proj₁ (∉-++⁻ xs v∉xs++ys)

  ∉-++⁻ʳ : {v : Carrier} → ∀ xs {ys} → v ∉ xs ++ ys → (v ∉ ys)
  ∉-++⁻ʳ xs v∉xs++ys = proj₂ (∉-++⁻ xs v∉xs++ys)

  ∉-∷⁼ : {a d : Carrier} {xs : List Carrier} → a ∈ xs → d ∉ xs → d ≉ a
  ∉-∷⁼ a∈xs d∉xs d≈a = d∉xs (∈-resp-≈ A (sym d≈a) a∈xs)

  ∉-∷⁺ : {a d : Carrier} {xs : List Carrier} → d ≉ a → d ∉ xs → d ∉ (a ∷ xs)
  ∉-∷⁺ d≢a d∉xs (here px) = d≢a px
  ∉-∷⁺ d≢a d∉xs (there d∈a∷xs) = d∉xs d∈a∷xs

  ∉-∷⁼ᵗ : {a d : Carrier} {xs : List Carrier} → d ∉ (a ∷ xs) → d ∉ xs
  ∉-∷⁼ᵗ d∉∷ d∈xs = d∉∷ (there d∈xs)

open import Relation.Unary renaming (Decidable to Decidableᵤ) hiding (_∈_;_∉_)
open import Relation.Nullary
import Data.List.Relation.Unary.Any.Properties as Any
import Data.List.Membership.Setoid as Membership
open Setoid using (Carrier)

private
  variable
    c c₁ c₂ c₃ p ℓ ℓ₁ ℓ₂ ℓ₃ : Level

module _ (S : Setoid c ℓ) {P : Pred (Carrier S) p}
         (P? : Decidableᵤ P) (resp : P Respects (Setoid._≈_ S)) where

  open Setoid S using (_≈_; sym; Carrier)
  open Membership S

  ∉-filter⁻ : ∀ {v} {xs} → v ∈ xs → v ∉ filter P? xs → ¬ (P v)
  ∉-filter⁻ {v} {xs = x ∷ xs} v∈xs v∉f[x∷xs] pv = v∉f[x∷xs] (∈-filter⁺ S P? resp v∈xs pv)
