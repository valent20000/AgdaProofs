{-# OPTIONS --cubical #-}
module Cat.Category.Abelian where

  open import Agda.Primitive --lsuc etc...
  open import Cat.Category

  open import Cat.Category.PreAbelian
  open import Cat.Category.ZeroCategory

  module _ {ℓa ℓb : Level} (c : Category ℓa ℓb) where

    record IsAbelian : Set (lsuc (ℓa ⊔ ℓb)) where

      open Category c

      field
        isPreAbelian : IsPreAbelian c

      --subjacent zero category.
      subjZC = IsPreAbelian.subjZC isPreAbelian

      field
        isKernel : {X Y : Object} (f : Arrow X Y) → isKer subjZC f
        isCoKernel : {X Y : Object} (f : Arrow X Y) → isCoKer subjZC f
