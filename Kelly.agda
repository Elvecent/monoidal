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
      ρρ⁻¹ =
        ρᵤ ⊗ₕ id ⋆ ρᵤ⁻¹ ⊗ₕ id    ≡⟨ sym (F-seq _ _) ⟩
        (ρᵤ ⋆ ρᵤ⁻¹) ⊗ₕ (id ⋆ id) ≡⟨ ⟨ ρ .nIso unit .ret ⟩⊗ₕ⟨ ⋆IdL id ⟩ ⟩
        id ⊗ₕ id                 ≡⟨ F-id ⟩
        id                       ∎

      wat = α⟨ unit , x , y ⟩ ⋆ ((ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id)
      watIso = ⋆Iso
        (_ , α .nIso ( unit , x , y ))
        (⊗ₕIso (⊗ₕIso ρ⁻¹ idCatIso) idCatIso)

      help =
        id ⊗ₕ η⟨ x ⟩ ⋆ ρᵤ⁻¹ ⊗ₕ id ≡⟨ ⟨ sym (triangle unit x) ⟩⋆⟨ refl ⟩ ⟩
        (α⟨ unit , unit , x ⟩ ⋆ ρᵤ ⊗ₕ id) ⋆ ρᵤ⁻¹ ⊗ₕ id    ≡⟨ ⋆Assoc _ _ _ ⟩
        α⟨ unit , unit , x ⟩ ⋆ ρᵤ ⊗ₕ id ⋆ ρᵤ⁻¹ ⊗ₕ id      ≡⟨ ⟨ refl ⟩⋆⟨ sym (F-seq _ _) ⟩ ⟩
        α⟨ unit , unit , x ⟩ ⋆ ((ρᵤ ⋆ ρᵤ⁻¹) ⊗ₕ (id ⋆ id)) ≡⟨ ⟨ refl ⟩⋆⟨ ⟨ ρ .nIso unit .ret ⟩⊗ₕ⟨ ⋆IdL id ⟩ ⟩ ⟩
        α⟨ unit , unit , x ⟩ ⋆ (id ⊗ₕ id)                 ≡⟨ ⟨ refl ⟩⋆⟨ F-id ⟩ ⟩
        α⟨ unit , unit , x ⟩ ⋆ id                         ≡⟨ ⋆IdR α⟨ unit , unit , x ⟩ ⟩
        α⟨ unit , unit , x ⟩                              ∎

      help2 =
        (id ⊗ₕ η⟨ x ⟩) ⊗ₕ id ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨ sym (F-seq _ _) ⟩
        ((id ⊗ₕ η⟨ x ⟩ ⋆ ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ (id ⋆ id))  ≡⟨ ⟨ refl ⟩⊗ₕ⟨ ⋆IdL id ⟩ ⟩
        ((id ⊗ₕ η⟨ x ⟩ ⋆ ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id)       ∎

      pentId =
        id ⊗ₕ (α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id) ⋆ wat ≡⟨ refl ⟩
        id ⊗ₕ (α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id) ⋆ α⟨ unit , x , y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨
          ⟨ ⟨ sym (⋆IdL id) ⟩⊗ₕ⟨ refl ⟩ ⟩⋆⟨ refl ⟩
        ⟩
        ((id ⋆ id) ⊗ₕ (α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id)) ⋆ α⟨ unit , x , y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨
          ⟨ F-seq _ _ ⟩⋆⟨ refl ⟩
        ⟩
        (id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id)) ⋆ α⟨ unit , x , y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨
          refl
        ⟩
        (id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id)) ⋆ (α⟨ unit , x , y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id) ≡⟨
          (⋆Assoc _ _ _) ∙ ⟨ refl ⟩⋆⟨ sym (⋆Assoc _ _ _) ⟩
        ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ (id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id) ⋆ α⟨ unit , x , y ⟩) ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ α .trans .N-hom _ ⟩⋆⟨ refl ⟩ ⟩
        ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ (α⟨ unit , unit ⊗ x , y ⟩ ⋆ (id ⊗ₕ η⟨ x ⟩) ⊗ₕ id) ⋆ (ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id ≡⟨
          ⟨ refl ⟩⋆⟨ ⋆Assoc _ _ _ ⟩
        ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ α⟨ unit , unit ⊗ x , y ⟩ ⋆ ((id ⊗ₕ η⟨ x ⟩) ⊗ₕ id ⋆ ((ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id)) ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ refl ⟩⋆⟨ help2 ⟩ ⟩
        ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ α⟨ unit , unit ⊗ x , y ⟩ ⋆ ((id ⊗ₕ η⟨ x ⟩ ⋆ ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id) ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ refl ⟩⋆⟨ ⟨ help ⟩⊗ₕ⟨ refl ⟩ ⟩ ⟩
        ⟩
        id ⊗ₕ α⟨ unit , x , y ⟩ ⋆ α⟨ unit , unit ⊗ x , y ⟩ ⋆ α⟨ unit , unit , x ⟩ ⊗ₕ id ≡⟨ pentagon unit unit x y ⟩
        α⟨ unit , unit , x ⊗ y ⟩ ⋆ α⟨ unit ⊗ unit , x , y ⟩ ≡⟨ ⟨ refl ⟩⋆⟨ sym (⋆IdL _) ⟩ ⟩
        α⟨ unit , unit , x ⊗ y ⟩ ⋆ id ⋆ α⟨ unit ⊗ unit , x , y ⟩ ≡⟨ ⟨ refl ⟩⋆⟨ ⟨ sym ρρ⁻¹ ⟩⋆⟨ refl ⟩ ⟩ ⟩
        α⟨ unit , unit , x ⊗ y ⟩ ⋆ (ρᵤ ⊗ₕ id ⋆ ρᵤ⁻¹ ⊗ₕ id) ⋆ α⟨ unit ⊗ unit , x , y ⟩ ≡⟨ (sym (⋆Assoc _ _ _)) ∙ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩ ∙ ⋆Assoc _ _ _ ⟩
        (α⟨ unit , unit , x ⊗ y ⟩ ⋆ ρᵤ ⊗ₕ id) ⋆ (ρᵤ⁻¹ ⊗ₕ id ⋆ α⟨ unit ⊗ unit , x , y ⟩) ≡⟨ ⟨ triangle _ _ ⟩⋆⟨ refl ⟩ ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id ⋆ α⟨ unit ⊗ unit , x , y ⟩) ≡⟨ ⟨ refl ⟩⋆⟨  ⟨ ⟨ refl ⟩⊗ₕ⟨ sym F-id ⟩ ⟩⋆⟨ refl ⟩ ⟩ ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ ( (ρᵤ⁻¹ ⊗ₕ (id ⊗ₕ id)) ⋆ α⟨ unit ⊗ unit , x , y ⟩ ) ≡⟨ ⟨ refl ⟩⋆⟨ α .trans .N-hom _ ⟩ ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ wat ∎
  
  η≡ρ : ηᵤ ≡ ρᵤ
  η≡ρ = ⊗ₕCancelIdR _ _ (⋆CancelL (α- , α .nIso _)
    (α- ⋆ ηᵤ ⊗ₕ idᵤ   ≡⟨ sym (Kellyη _ _) ⟩
     η⟨ unit ⊗ unit ⟩ ≡⟨ η⊗ ⟩
     idᵤ ⊗ₕ ηᵤ        ≡⟨ sym (triangle _ _) ⟩
     α- ⋆ ρᵤ ⊗ₕ idᵤ   ∎))
