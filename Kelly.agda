{-# OPTIONS --cubical --guardedness #-}

module Kelly where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Extras

module _ {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M
  open MonoidalExtras M
  open Cubical.Categories.Monoidal.Extras 
  open import Cubical.Categories.NaturalTransformation
  open NatIso
  open NatTrans
  open isIso
  
  kelly' : ∀ x y
         → η⟨ x ⊗ y ⟩ ≡ α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id{y}
  kelly' = _
  
  kelly : ηᵤ ≡ ρᵤ
  kelly = ⊗ₕid _ _ kelly1
    where
      kelly1 : ηᵤ ⊗ₕ idᵤ ≡ ρᵤ ⊗ₕ idᵤ
      kelly1 =
        ηᵤ ⊗ₕ idᵤ               ≡⟨ sym (⋆IdL _) ⟩
        id ⋆ ηᵤ ⊗ₕ idᵤ          ≡⟨ sym ⟨ α .nIso _ .sec ⟩⋆⟨ refl ⟩ ⟩
        (α-⁻¹ ⋆ α-) ⋆ ηᵤ ⊗ₕ idᵤ ≡⟨ ⋆Assoc _ _ _ ⟩
        α-⁻¹ ⋆ α- ⋆ ηᵤ ⊗ₕ idᵤ   ≡⟨ ⟨ refl ⟩⋆⟨ sym (kelly' _ _) ⟩ ⟩
        α-⁻¹ ⋆ η⟨ unit ⊗ unit ⟩ ≡⟨ _ ⟩
        α-⁻¹ ⋆ idᵤ ⊗ₕ ηᵤ        ≡⟨ ⟨ refl ⟩⋆⟨ sym (triangle _ _) ⟩ ⟩
        α-⁻¹ ⋆ (α- ⋆ ρᵤ ⊗ₕ idᵤ) ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (α-⁻¹ ⋆ α-) ⋆ ρᵤ ⊗ₕ idᵤ ≡⟨ ⟨ α .nIso _ .sec ⟩⋆⟨ refl ⟩ ⟩
        id ⋆ ρᵤ ⊗ₕ idᵤ          ≡⟨ ⋆IdL _ ⟩
        ρᵤ ⊗ₕ idᵤ               ∎
