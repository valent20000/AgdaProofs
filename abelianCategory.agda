{-# OPTIONS --cubical #-}
module abelianCategory where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.FromStdLib renaming (_+_ to _+ℕ_) hiding (_×_)
  open import Cubical.Examples.Int 
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using

  open import Algebra
  open import Algebra.Structures
  open import Relation.Binary
  open import Algebra.FunctionProperties.Core

  open import Utils
  open import complexes2




-- Version 1.

  -- module AbelianCategoryProp (ℓa ℓb : Level) (c : ZeroCategory ℓa ℓb) where

  --   open ZeroCategory c public

  --   -- Taken from the Standard Library
    
  --   record ArrowAbelianGroup (X Y : Object) ℓ : Set (lsuc (ℓb ⊔ ℓ)) where
  --     infix  8 _⁻¹
  --     infixl 7 _∙_
  --     infix  4 _≈_
  --     field
  --       _≈_            : Rel (Arrow X Y) ℓ
  --       _∙_            : Op₂ (Arrow X Y)
  --       ε              : (Arrow X Y)
  --       _⁻¹            : Op₁ (Arrow X Y)
  --       isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹


  --   record KerOn {X Y : Object} (K : Object) (k : (Arrow K X)) (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where

  --     field
  --       kOnf : ((f <<< k) ≡ (zeroFunc K Y))
  --       fact : (K' : Object) (k' : Arrow K' X) (pt : (f <<< k') ≡ (zeroFunc K' Y)) → isContr (Σ (Arrow K' K) (λ u → k' ≡ (k <<< u)))

  --   record CoKerOn {X Y : Object} (N* : Object) (p : Arrow Y N*) (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where

  --     field
  --       pOnf : (p <<< f) ≡ (zeroFunc X N*)
  --       fact : (A : Object) (g : Arrow Y A) (pt : g <<< f ≡ zeroFunc X A) → isContr (Σ (Arrow N* A) (λ g' → g ≡ (g' <<< p)))

  --   record Ker {X Y : Object} (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where
      
  --     field
  --       K : Object
  --       k : (Arrow K X)
  --       content : KerOn K k f

  --   record CoKer {X Y : Object} (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where

  --     field
  --       N* : Object
  --       p : Arrow Y N*
  --       content : CoKerOn N* p f

  --   record Img {X Y : Object} (f : Arrow X Y) (kr : Ker f) (cokr : CoKer f) : Set (ℓa ⊔ ℓb) where

  --     field
  --       Im : Object

  --       fd : Arrow Im Y
  --       kerFd : KerOn Im fd (cokr .CoKer.p) -- Kernel of a Co-Kernel of f
        
  --       fg : Arrow X Im
  --       coKerFg : CoKerOn Im fg (kr .Ker.k) --CoK--Co-kernel of a Kernel of f
       
  --       comp : f ≡ (fd <<< fg)


  -- record AbelianCategory (ℓa ℓb ℓg : Level) : Set (lsuc (ℓa ⊔ ℓb ⊔ ℓg)) where

  --   field {{parentCat}} : (ZeroCategory ℓa ℓb)
    
  --   open AbelianCategoryProp ℓa ℓb parentCat public

  --   field
  --     homAb : (X Y : Object) → (ArrowAbelianGroup X Y ℓg)

  --   infixl 7 _op+_
    
  --   _op+_ : {X Y : Object} (f g : Arrow X Y) → Arrow X Y
  --   _op+_ {X} {Y} f g = ((homAb X Y) .ArrowAbelianGroup._∙_) f g
    
  --   field
  --     bilin : {X Y Z : Object} (fg fg' : Arrow Y Z) (fd fd' : Arrow X Y) → (fg op+ fg') <<< (fd op+ fd') ≡ (fg <<< fd) op+ (fg <<< fd') op+ (fg' <<< fd) op+ (fg' <<< fd')

  --   field
  --     kerOf : {X Y : Object} (f : Arrow X Y) → (Ker f)
  --     coKerOf : {X Y : Object} (f : Arrow X Y) → (CoKer f)
  --     imgOf : {X Y : Object} (f : Arrow X Y) → (Img f (kerOf f) (coKerOf f))



  -- -- -- record Kernel (ℓa ℓb : Level) (c : ZeroCategory ℓa ℓb) : Set (ℓa ⊔ ℓb) where

  -- -- --   open ZeroCategory c public

  -- -- --   field
  -- -- --     ker : {X Y : Object} (f : Arrow X Y) → Σ Object (λ K → Σ (Arrow K X) (λ k → ((f <<< k) ≡ (zeroFunc K Y)) × ((K' : Object) → (k' : Arrow K' X) → (f <<< k') ≡ (zeroFunc K' Y) → isContr (Σ (Arrow K' K) (λ u → k' ≡ (k <<< u)))) ))
