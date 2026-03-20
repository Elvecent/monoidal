{-# OPTIONS --cubical --guardedness #-}

module Kelly where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
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
  
  Kelly : ∀ x y
        → η⟨ x ⊗ y ⟩
        ≡ α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id
  Kelly = _
  
  η≡ρ : ηᵤ ≡ ρᵤ
  η≡ρ = ⊗ₕIdR _ _ (⋆CancelL (α- , α .nIso _)
    (α- ⋆ ηᵤ ⊗ₕ idᵤ   ≡⟨ sym (Kelly _ _) ⟩
     η⟨ unit ⊗ unit ⟩ ≡⟨ η⊗ ⟩
     idᵤ ⊗ₕ ηᵤ        ≡⟨ sym (triangle _ _) ⟩
     α- ⋆ ρᵤ ⊗ₕ idᵤ   ∎))
