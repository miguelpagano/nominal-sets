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
