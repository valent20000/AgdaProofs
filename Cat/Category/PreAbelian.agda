{-# OPTIONS --cubical #-}
module Cat.Category.PreAbelian where

  open import Agda.Primitive --lsuc etc...

  open import Cat.Category
  open import Cat.Category.Additive
  open import Cat.Category.PreAdditive

  open import Cat.Category.ZeroCategory


  module _ {ℓa ℓb : Level} (c : Category ℓa ℓb) where

    record IsPreAbelian : Set (lsuc (ℓa ⊔ ℓb)) where

      open Category c

      field
        isAdditive : IsAdditive c

      -- The subjacent zero category.
      subjZC = (record { c = c ; isZeroCategory = isAdditive .IsAdditive.isPreAdditive .IsPreAdditive.isZeroCategory })

      field
        hasKer : {X Y : Object} (f : Arrow X Y) → Ker subjZC  f
        hasCoKer : {X Y : Object} (f : Arrow X Y) → CoKer subjZC f
