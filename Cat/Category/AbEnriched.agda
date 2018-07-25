{-# OPTIONS --cubical #-}
module Cat.Category.AbEnriched where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.PathPrelude

  open import Cat.Category
  open import Cat.Category.Product

  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core

  open import Cat.Category.ZeroCategory



  module _ {ℓa ℓb : Level} (c : Category ℓa ℓb) where

    open Category c public

    record ArrowAbelianGroup (X Y : Object) : Set (lsuc ℓb) where
    
      infix  8 _⁻¹
      infixl 7 _∙_
      field
        _∙_            : Op₂ (Arrow X Y)
        ε              : (Arrow X Y)
        _⁻¹            : Op₁ (Arrow X Y)
        isAbelianGroup : IsAbelianGroup _≡_ _∙_ ε _⁻¹
        

    record IsAbEnriched : Set (lsuc (ℓa ⊔ ℓb)) where

      field
        homAb : (X Y : Object) → (ArrowAbelianGroup X Y)

      module M {X Y : Object} = ArrowAbelianGroup (homAb X Y)
      open M
      
      field
        bilin : {X Y Z : Object} (fg fg' : Arrow Y Z) (fd fd' : Arrow X Y) → (fg ∙ fg') <<< (fd ∙ fd') ≡ (fg <<< fd) ∙ (fg <<< fd') ∙ (fg <<< fd) ∙ (fg' <<< fd') 
        
