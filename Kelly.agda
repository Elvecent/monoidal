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
  open Functor ─⊗─ using (F-seq; F-id; F-hom)
  open Cubical.Categories.Monoidal.Extras 
  open import Cubical.Categories.NaturalTransformation
  open NatIso
  open NatTrans
  open isIso
  
  Kellyη : ∀ x y
         → η⟨ x ⊗ y ⟩
         ≡ α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id
  Kellyη x y =
    ⊗ₕCancelIdL η⟨ x ⊗ y ⟩ (α- ⋆ η⟨ x ⟩ ⊗ₕ id)
      (⋆CancelR watIso (sym pentId))
    where
      ρ⁻¹ = invIso (_ , (ρ .nIso _))

      wat = α⟨ unit , x , y ⟩ ⋆ ((ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id)
      watIso = ⋆Iso
        (_ , α .nIso ( unit , x , y ))
        (⊗ₕIso (⊗ₕIso ρ⁻¹ idCatIso) idCatIso)

      pentId =
        id ⊗ₕ (α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id) ⋆ wat ≡⟨ _ ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩  ⋆  α⟨ unit , unit ⊗ x , y ⟩  ⋆  α⟨ unit , unit , x ⟩ ⊗ₕ id ≡⟨ pentagon unit unit x y ⟩
        α⟨ unit , unit , x ⊗ y ⟩  ⋆  α⟨ unit ⊗ unit , x , y ⟩ ≡⟨ _ ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ wat ∎
  
  η≡ρ : ηᵤ ≡ ρᵤ
  η≡ρ = ⊗ₕCancelIdR _ _ (⋆CancelL (α- , α .nIso _)
    (α- ⋆ ηᵤ ⊗ₕ idᵤ   ≡⟨ sym (Kellyη _ _) ⟩
     η⟨ unit ⊗ unit ⟩ ≡⟨ η⊗ ⟩
     idᵤ ⊗ₕ ηᵤ        ≡⟨ sym (triangle _ _) ⟩
     α- ⋆ ρᵤ ⊗ₕ idᵤ   ∎))
