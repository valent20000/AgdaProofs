{-# OPTIONS --cubical #-}
module Cat.Category.Additive where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.PathPrelude

  open import Cat.Category
  open import Cat.Category.Product

  open import Cat.Category.PreAdditive

  module _ {ℓa ℓb : Level} (c : Category ℓa ℓb) where


    record IsAdditive : Set (lsuc (ℓa ⊔ ℓb)) where

      field
        isPreAdditive : IsPreAdditive c
        hasProducts : HasProducts c     --One can prove that products in a PreAdditive Category are actually bi-products. (& dual)

      
