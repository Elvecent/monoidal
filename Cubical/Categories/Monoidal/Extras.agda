{-# OPTIONS --cubical --guardedness #-}

module Cubical.Categories.Monoidal.Extras where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Data.Sigma

module MonoidalExtras {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M
  open Functor ─⊗─ using (F-seq; F-id; F-hom)
  open import Cubical.Categories.NaturalTransformation
  open NatIso
  open NatTrans
  open isIso

  module u_notation where
    ρᵤ   = ρ⟨ unit ⟩
    ηᵤ   = η⟨ unit ⟩
    ηᵤ⁻¹ = η⁻¹⟨ unit ⟩
    ρᵤ⁻¹ = ρ⁻¹⟨ unit ⟩
    idᵤ  = id{unit}

    α- : ∀ { x y z } → Hom[ x ⊗ (y ⊗ z) , (x ⊗ y) ⊗ z ]
    α- {x} {y} {z} = α⟨ x , y , z ⟩

    α-⁻¹ : ∀ { x y z } → Hom[ (x ⊗ y) ⊗ z , x ⊗ (y ⊗ z) ]
    α-⁻¹ {x} {y} {z} = α⁻¹⟨ x , y , z ⟩

  open u_notation public

  ⊗ₕid : ∀ {x y} (f g : C [ x , y ])
       → f ⊗ₕ idᵤ ≡ g ⊗ₕ idᵤ
       → f ≡ g
  ⊗ₕid {x} {y} f g e =
    f                       ≡⟨ sym (⋆IdL _) ⟩
    id ⋆ f                  ≡⟨ ⟨ sym (ρ .nIso _ .sec) ⟩⋆⟨ refl ⟩ ⟩
    (ρ⁻¹⟨ x ⟩ ⋆ ρ⟨ x ⟩) ⋆ f ≡⟨ ⋆Assoc _ _ _ ⟩
    ρ⁻¹⟨ x ⟩ ⋆ ρ⟨ x ⟩ ⋆ f   ≡⟨ ⟨ refl ⟩⋆⟨ nat_nat ⟩ ⟩
    ρ⁻¹⟨ x ⟩ ⋆ ρ⟨ x ⟩ ⋆ g   ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (ρ⁻¹⟨ x ⟩ ⋆ ρ⟨ x ⟩) ⋆ g ≡⟨ ⟨ ρ .nIso _ .sec ⟩⋆⟨ refl ⟩ ⟩
    id ⋆ g                  ≡⟨ ⋆IdL _ ⟩
    g                       ∎
    where
      nat_nat =
        ρ⟨ x ⟩ ⋆ f          ≡⟨ sym (ρ .trans .N-hom f) ⟩
        (f ⊗ₕ id ⋆ ρ⟨ y ⟩)  ≡⟨ ⟨ e ⟩⋆⟨ refl ⟩ ⟩
        (g ⊗ₕ id ⋆ ρ⟨ y ⟩)  ≡⟨ ρ .trans .N-hom g ⟩
        ρ⟨ x ⟩ ⋆ g          ∎

  id⊗ₕ : ∀ {x y} (f g : C [ x , y ])
       → idᵤ ⊗ₕ f ≡ idᵤ ⊗ₕ g
       → f ≡ g
  id⊗ₕ {x} {y} f g e =
    f                       ≡⟨ sym (⋆IdL _) ⟩
    id ⋆ f                  ≡⟨ ⟨ sym (η .nIso _ .sec) ⟩⋆⟨ refl ⟩ ⟩
    (η⁻¹⟨ x ⟩ ⋆ η⟨ x ⟩) ⋆ f ≡⟨ ⋆Assoc _ _ _ ⟩
    η⁻¹⟨ x ⟩ ⋆ η⟨ x ⟩ ⋆ f   ≡⟨ ⟨ refl ⟩⋆⟨ nat_nat ⟩ ⟩
    η⁻¹⟨ x ⟩ ⋆ η⟨ x ⟩ ⋆ g   ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (η⁻¹⟨ x ⟩ ⋆ η⟨ x ⟩) ⋆ g ≡⟨ ⟨ η .nIso _ .sec ⟩⋆⟨ refl ⟩ ⟩
    id ⋆ g                  ≡⟨ ⋆IdL _ ⟩
    g                       ∎
    where
      nat_nat =
        η⟨ x ⟩ ⋆ f          ≡⟨ sym (η .trans .N-hom f) ⟩
        (idᵤ ⊗ₕ f) ⋆ η⟨ y ⟩ ≡⟨ ⟨ e ⟩⋆⟨ refl ⟩ ⟩
        (idᵤ ⊗ₕ g) ⋆ η⟨ y ⟩ ≡⟨ η .trans .N-hom g ⟩
        η⟨ x ⟩ ⋆ g          ∎
