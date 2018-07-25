{-# OPTIONS --cubical #-}
module Cat.Category.PreAdditive where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.PathPrelude

  open import Cat.Category
  open import Cat.Category.Product


  open import Cat.Category.ZeroCategory
  open import Cat.Category.AbEnriched


  module _ {ℓa ℓb : Level} (c : Category ℓa ℓb) where

    record IsPreAdditive : Set (lsuc (ℓa ⊔ ℓb)) where

      field
        isAbEnriched : IsAbEnriched c
        isZeroCategory : IsZeroCategory c
