{-# OPTIONS --cubical --guardedness #-}

module Kelly where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Constructions.BinProduct


open import Cubical.Categories.Monoidal.Extras

-- lemma from Kelly64
-- about not needed agreeing unitors as an axiom

module _ {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M
  open MonoidalExtras M
  open Functor ─⊗─ using (F-seq; F-id; F-hom)
  open Cubical.Categories.Monoidal.Extras 
  open import Cubical.Categories.NaturalTransformation
  open NatIso
  open NatTrans
  open isIso

  ρρ⁻¹ : ∀ {x} → ρᵤ ⊗ₕ id{x} ⋆ ρᵤ⁻¹ ⊗ₕ id ≡ id
  ρρ⁻¹ =
    ρᵤ ⊗ₕ id ⋆ ρᵤ⁻¹ ⊗ₕ id    ≡⟨ sym (F-seq _ _) ⟩
    (ρᵤ ⋆ ρᵤ⁻¹) ⊗ₕ (id ⋆ id) ≡⟨
      ⟨ ρ .nIso unit .ret ⟩⊗ₕ⟨ ⋆IdL id ⟩
    ⟩
    id ⊗ₕ id                 ≡⟨ F-id ⟩
    id                       ∎

  α=ρ⁻¹⊗ₕη : ∀ {x y}
           → α⟨ x , unit , y ⟩ ≡ ρ⁻¹⟨ x ⟩ ⊗ₕ η⟨ y ⟩
  α=ρ⁻¹⊗ₕη {x} {y} =
    ⋆InvRMove iso (triangle _ _) ∙ sym (⊗ₕSplitR _ _)
    where iso = (⊗ₕIso (_ , ρ .nIso x) idCatIso)

  ⋆AssocMid : ∀ {a b c d e}
              (f : C [ a , b ]) (g : C [ b , c ])
              (h : C [ c , d ]) (k : C [ d , e ])
            → f ⋆ (g ⋆ h) ⋆ k ≡ (f ⋆ g) ⋆ (h ⋆ k)
  ⋆AssocMid f g h k =
    f ⋆ (g ⋆ h) ⋆ k   ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (f ⋆ g ⋆ h) ⋆ k   ≡⟨ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩ ⟩
    ((f ⋆ g) ⋆ h) ⋆ k ≡⟨ ⋆Assoc _ _ _ ⟩
    (f ⋆ g) ⋆ (h ⋆ k) ∎
  
  private module _ {x y : ob} where
    α⋆ρ⁻¹⊗id :
      C [ unit ⊗ (x ⊗ y) , ((unit ⊗ unit) ⊗ x) ⊗ y ]
    α⋆ρ⁻¹⊗id =
      α- ⋆ ((ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id)

    α⋆ρ⁻¹⊗id-Iso : ∀ {x y}
                 → CatIso C
                     (unit ⊗ (x ⊗ y))
                     (((unit ⊗ unit) ⊗ x) ⊗ y)
    α⋆ρ⁻¹⊗id-Iso = ⋆Iso
      (_ , α .nIso _)
      (⊗ₕIso (⊗ₕIso inv-ρ idCatIso) idCatIso)
      where inv-ρ = invIso (_ , ρ .nIso _)

    ρ⁻¹id = (ρᵤ⁻¹ ⊗ₕ id{x}) ⊗ₕ id{y}

  Kellyη : ∀ x y
         → η⟨ x ⊗ y ⟩
         ≡ α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id
  Kellyη x y =
    ⊗ₕCancelIdL η⟨ x ⊗ y ⟩ (α- ⋆ η⟨ x ⟩ ⊗ₕ id)
      (⋆CancelR (α⋆ρ⁻¹⊗id-Iso {x} {y}) (sym pentId))
    where
      pentId =
        id ⊗ₕ (α⟨ unit , x , y ⟩ ⋆ η⟨ x ⟩ ⊗ₕ id) ⋆ α⋆ρ⁻¹⊗id ≡⟨
          ⟨ ⟨ sym (⋆IdL id) ⟩⊗ₕ⟨ refl ⟩ ∙ (F-seq _ _) ⟩⋆⟨ refl ⟩
        ⟩
        (id ⊗ₕ α- ⋆ id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id)) ⋆ α⋆ρ⁻¹⊗id ≡⟨
          (⋆Assoc _ _ _) ∙ ⟨ refl ⟩⋆⟨ sym (⋆Assoc _ _ _) ⟩
        ⟩
        id ⊗ₕ α- ⋆ (id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id) ⋆ α-) ⋆ ρ⁻¹id ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ α .trans .N-hom _ ⟩⋆⟨ refl ⟩ ∙ (⋆Assoc _ _ _) ⟩
        ⟩
        id ⊗ₕ α- ⋆ α- ⋆ ((id ⊗ₕ η⟨ x ⟩) ⊗ₕ id ⋆ ρ⁻¹id) ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ refl ⟩⋆⟨ sym (F-seq _ _) ∙ ⟨ refl ⟩⊗ₕ⟨ ⋆IdL _ ⟩ ⟩ ⟩
        ⟩
        id ⊗ₕ α- ⋆ α- ⋆ ((id ⊗ₕ η⟨ x ⟩ ⋆ ρᵤ⁻¹ ⊗ₕ id) ⊗ₕ id) ≡⟨
          ⟨ refl ⟩⋆⟨ ⟨ refl ⟩⋆⟨ ⟨ sym (α=ρ⁻¹⊗ₕη ∙ ⊗ₕSplitR _ _) ⟩⊗ₕ⟨ refl ⟩ ⟩ ⟩
        ⟩
        id ⊗ₕ α- ⋆ α- ⋆ α- ⊗ₕ id ≡⟨
          pentagon unit unit x y
        ⟩
        α⟨ unit , unit , x ⊗ y ⟩ ⋆ α⟨ unit ⊗ unit , x , y ⟩ ≡⟨
          ⟨ refl ⟩⋆⟨ sym (⋆IdL _) ∙ ⟨ sym ρρ⁻¹ ⟩⋆⟨ refl ⟩ ⟩
        ⟩
        α- ⋆ (ρᵤ ⊗ₕ id ⋆ ρᵤ⁻¹ ⊗ₕ id) ⋆ α- ≡⟨
          ⋆AssocMid _ _ _ _ ∙ ⟨ triangle _ _ ⟩⋆⟨ refl ⟩
        ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ (ρᵤ⁻¹ ⊗ₕ id ⋆ α-) ≡⟨
          ⟨ refl ⟩⋆⟨  ⟨ ⟨ refl ⟩⊗ₕ⟨ sym F-id ⟩ ⟩⋆⟨ refl ⟩ ⟩
        ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ ( (ρᵤ⁻¹ ⊗ₕ (id ⊗ₕ id)) ⋆ α- ) ≡⟨
          ⟨ refl ⟩⋆⟨ α .trans .N-hom _ ⟩
        ⟩
        id ⊗ₕ η⟨ x ⊗ y ⟩ ⋆ α⋆ρ⁻¹⊗id ∎
  
  η≡ρ : ηᵤ ≡ ρᵤ
  η≡ρ = ⊗ₕCancelIdR _ _ (⋆CancelL (α- , α .nIso _)
    (α- ⋆ ηᵤ ⊗ₕ idᵤ   ≡⟨ sym (Kellyη _ _) ⟩
     η⟨ unit ⊗ unit ⟩ ≡⟨ η⊗ ⟩
     idᵤ ⊗ₕ ηᵤ        ≡⟨ sym (triangle _ _) ⟩
     α- ⋆ ρᵤ ⊗ₕ idᵤ   ∎))
