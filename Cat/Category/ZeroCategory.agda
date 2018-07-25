{-# OPTIONS --cubical #-}
module Cat.Category.ZeroCategory where

  open import Cat.Category
  open import Cat.Prelude
  open import Cat.Categories.Opposite

  module _ {ℓa ℓb : Level} (c : (Category ℓa ℓb)) where

    record IsZeroCategory : Set (lsuc (ℓa ⊔ ℓb)) where

      open Category c public

      field
        hasZero : Σ Object (λ zer → (IsInitial zer × IsTerminal zer))

      cZero = (fst hasZero)

      -- "Shortcuts" to make proofs clearer. Uniqueness of arrows from and to  (terminal and initial)
      
      proofTerm : {X : Object} → (y : Arrow X (fst hasZero)) → fst (snd (snd hasZero)) ≡ y
      proofTerm {X} = (snd ((snd (snd hasZero)) {X = X}))

  
      proofInit : {X : Object} → (y : Arrow (fst hasZero) X) → fst (fst (snd hasZero)) ≡ y
      proofInit {X} = (snd ((fst (snd hasZero)) {X = X}))
   

      --Gives the zero function associated to A and B
      zeroFunc : (A : Object) (C : Object) → (Arrow A C)  
      zeroFunc = λ A C → (fst ((fst (snd hasZero)) {X = C})) <<< (fst (snd (snd hasZero) {X = A}))


  record ZeroCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where

    field
      c : (Category ℓa ℓb)
      isZeroCategory : IsZeroCategory c

    open IsZeroCategory isZeroCategory public


  module _ {ℓa ℓb : Level} (cat : ZeroCategory ℓa ℓb) where

    ZC-opposite : ZeroCategory ℓa ℓb
    ZeroCategory.c ZC-opposite = opposite (ZeroCategory.c cat)
    ZeroCategory.isZeroCategory ZC-opposite = record { hasZero = (ZeroCategory.cZero cat) , ((snd (snd (ZeroCategory.hasZero cat))) , ((fst (snd (ZeroCategory.hasZero cat))))) }

    open ZeroCategory cat
    
    record KerOn {X Y : Object} (K : Object) (k : (Arrow K X)) (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where

      field
        kOnf : ((f <<< k) ≡ (zeroFunc K Y))
        fact : (K' : Object) (k' : Arrow K' X) (pt : (f <<< k') ≡ (zeroFunc K' Y)) → isContr (Σ (Arrow K' K) (λ u → k' ≡ (k <<< u)))

    isKer : {X Y K : Object} (k : (Arrow K X)) → Set (ℓa ⊔ ℓb)
    isKer {X} {Y} {K} k = Σ (Arrow X Y) (λ f → KerOn K k f)

    record Ker {X Y : Object} (f : Arrow X Y) : Set (ℓa ⊔ ℓb) where
      
      field
        K : Object
        k : (Arrow K X)
        content : KerOn K k f


  module _ {ℓa ℓb : Level} (cat : ZeroCategory ℓa ℓb) where

    open ZeroCategory (ZC-opposite cat)

    CoKerOn : {X Y : Object} (N* : Object) (p : Arrow N* Y) (f : Arrow Y X) → Set (ℓa ⊔ ℓb)
    CoKerOn {X} {Y} N* p f = KerOn (ZC-opposite cat) N* p f

    isCoKer : {X Y K : Object} (f : (Arrow K X)) → Set (ℓa ⊔ ℓb)
    isCoKer {X} {Y} {K} f = isKer (ZC-opposite cat) {X = X} {Y = Y} {K = K} f

    CoKer : {X Y : Object} (f : Arrow X Y) → Set (ℓa ⊔ ℓb)
    CoKer f = Ker (ZC-opposite cat) f
