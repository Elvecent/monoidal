{-# OPTIONS --cubical --guardedness #-}

module Cubical.Categories.Monoidal.Extras where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Data.Sigma

module MonoidalExtras {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M
  open Functor ─⊗─ using (F-seq; F-id; F-hom)
  open import Cubical.Categories.NaturalTransformation
  open NatIso
  open NatTrans
  open isIso

  module ⊗notation where
    ρᵤ   = ρ⟨ unit ⟩
    ηᵤ   = η⟨ unit ⟩
    ηᵤ⁻¹ = η⁻¹⟨ unit ⟩
    ρᵤ⁻¹ = ρ⁻¹⟨ unit ⟩
    idᵤ  = id{unit}

    α- : ∀ { x y z } → Hom[ x ⊗ (y ⊗ z) , (x ⊗ y) ⊗ z ]
    α- {x} {y} {z} = α⟨ x , y , z ⟩

    α-⁻¹ : ∀ { x y z } → Hom[ (x ⊗ y) ⊗ z , x ⊗ (y ⊗ z) ]
    α-⁻¹ {x} {y} {z} = α⁻¹⟨ x , y , z ⟩

  open ⊗notation public

  -- the naturality of unitors and its consequences
  
  ⊗ₕIdR : ∀ {x y} (f g : C [ x , y ])
        → f ⊗ₕ idᵤ ≡ g ⊗ₕ idᵤ
        → f ≡ g
  ⊗ₕIdR {x} {y} f g e = ⋆CancelL (_ , ρ .nIso x)
    (ρ⟨ x ⟩ ⋆ f          ≡⟨ sym (ρ .trans .N-hom f) ⟩
     (f ⊗ₕ id ⋆ ρ⟨ y ⟩)  ≡⟨ ⟨ e ⟩⋆⟨ refl ⟩ ⟩
     (g ⊗ₕ id ⋆ ρ⟨ y ⟩)  ≡⟨ ρ .trans .N-hom g ⟩
     ρ⟨ x ⟩ ⋆ g          ∎)

  ⊗ₕIdL : ∀ {x y} (f g : C [ x , y ])
        → idᵤ ⊗ₕ f ≡ idᵤ ⊗ₕ g
        → f ≡ g
  ⊗ₕIdL {x} {y} f g e = ⋆CancelL (_ , η .nIso x)
    (η⟨ x ⟩ ⋆ f          ≡⟨ sym (η .trans .N-hom f) ⟩
     (idᵤ ⊗ₕ f) ⋆ η⟨ y ⟩ ≡⟨ ⟨ e ⟩⋆⟨ refl ⟩ ⟩
     (idᵤ ⊗ₕ g) ⋆ η⟨ y ⟩ ≡⟨ η .trans .N-hom g ⟩
     η⟨ x ⟩ ⋆ g          ∎)

  η⊗ : ∀ {x}
     → η⟨ unit ⊗ x ⟩ ≡ id ⊗ₕ η⟨ x ⟩
  η⊗ {x} = ⋆CancelR (_ , η .nIso _)
    (η⟨ _ ⟩ ⋆ η⟨ x ⟩         ≡⟨ sym (η .trans .N-hom _) ⟩
     (id ⊗ₕ η⟨ x ⟩ ⋆ η⟨ x ⟩) ∎)

  ρ⊗ : ∀ {x}
     → ρ⟨ x ⊗ unit ⟩ ≡ ρ⟨ x ⟩ ⊗ₕ id
  ρ⊗ {x} = ⋆CancelR (_ , ρ .nIso x)
    (ρ⟨ _ ⟩ ⋆ ρ⟨ x ⟩         ≡⟨ sym (ρ .trans .N-hom _) ⟩
     (ρ⟨ x ⟩ ⊗ₕ id ⋆ ρ⟨ x ⟩) ∎)
