{-# OPTIONS --cubical #-}
module Kernel where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.FromStdLib renaming (_+_ to _+ℕ_) hiding (_×_)
  open import Cubical.Examples.Int 
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  
  open import Cat.Category
  open import Cat.Categories.Opposite

  open import Algebra
  open import Algebra.Structures
  open import Relation.Binary
  open import Algebra.FunctionProperties.Core

  open import Utils
  open import complexes2

  module _ {ℓa ℓb : Level} (c : ZeroCategory ℓa ℓb) where

    open ZeroCategory c
    
    record KerOn {X Y : Object} (K : Object) (k : (Arrow K X)) (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where

      field
        kOnf : ((f <<< k) ≡ (zeroFunc K Y))
        fact : (K' : Object) (k' : Arrow K' X) (pt : (f <<< k') ≡ (zeroFunc K' Y)) → isContr (Σ (Arrow K' K) (λ u → k' ≡ (k <<< u)))

    record Ker {X Y : Object} (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where
      
      field
        K : Object
        k : (Arrow K X)
        content : KerOn K k f

  module _ {ℓa ℓb : Level} (c : ZeroCategory ℓa ℓb) where

    open ZeroCategory (opposite c) public

    CoKerOn {X Y : Object} (N* : Object) (p : Arrow Y N*) (f : Arrow X Y) = KerOn {X = X}

    record CoKer {X Y : Object} (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where
