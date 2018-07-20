{-# OPTIONS --cubical #-}
module chainComplexCategory where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.PathPrelude
  open import Cubical.Examples.Int 
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using

  open import Utils
  open import complexes2
  open import abelianCategory

  ℤ = Int

  module ChainMapM (ℓa ℓb : Level) (catZ : ZeroCategory ℓa ℓb) where

    open ZeroCategory catZ public
    
    record ChainMap (c1 c2 : ChainComplex ℓa ℓb {cat = catZ}) : Set (ℓa ⊔ ℓb) where
    
      field
        fn : (n : ℤ) → Arrow (c1 .ChainComplex.thisO n) (c2 .ChainComplex.thisO n)
        commute : (n : ℤ) → (fn (predℤ n)) <<< (c1 .ChainComplex.thisA n) ≡ ((c2 .ChainComplex.thisA n) <<< (fn n))

    module _ {c : ChainComplex ℓa ℓb {cat = catZ}} where

      idChainMap : (ChainMap c c)
      idChainMap = record { fn = λ n → catZ .ZeroCategory.identity {A = (c .ChainComplex.thisO n)} ; commute = λ n → begin
        identity <<< c .ChainComplex.thisA n ≡⟨ fst (catZ .ZeroCategory.isIdentity) ⟩
        c .ChainComplex.thisA n ≡⟨ sym ( snd (catZ .ZeroCategory.isIdentity)) ⟩
        c .ChainComplex.thisA n <<< identity ∎ }


  module ChainComplexCategoryM (ℓa ℓb : Level) (catZ : ZeroCategory ℓa ℓb) where
  
    open ChainMapM ℓa ℓb catZ public
    
    ChainComplexCategory : Category (ℓa ⊔ ℓb) (ℓa ⊔ ℓb)
    ChainComplexCategory = record { raw = record { Object = ChainComplex ℓa ℓb {cat = catZ} ; Arrow = ChainMapM.ChainMap ℓa ℓb catZ ; identity = idChainMap ; _<<<_ = λ bc ab → record { fn = λ n → bc .ChainMap.fn n <<< ab .ChainMap.fn n ; commute = λ n → begin
      {!bc .ChainMapM.ChainMap.fn (predℤ n) <<< ab .ChainMapM.ChainMap.fn (predℤ n) <<< .A .ChainComplex.thisA n!}
      
        ≡⟨ {! assoc!} ⟩

      {!bc .ChainMapM.ChainMap.fn (predℤ n) <<< (ab .ChainMapM.ChainMap.fn (predℤ n) <<< .A .ChainComplex.thisA n)!}

        ≡⟨ {! commuAB!} ⟩
        
      {!bc .ChainMapM.ChainMap.fn (predℤ n) <<< ((.B .ChainComplex.thisA n)  <<< (ab .ChainMapM.ChainMap.fn n))!}

        ≡⟨ {!assoc!} ⟩
        
      {!bc .ChainMapM.ChainMap.fn (predℤ n) <<< (.B .ChainComplex.thisA n)  <<< (ab .ChainMapM.ChainMap.fn n)!}

        ≡⟨ {!commuBC!} ⟩

      {!.C .ChainComplex.thisA n <<< bc .ChainMapM.ChainMap.fn n <<< ab .ChainMapM.ChainMap.fn n!}

        ≡⟨ {! assoc!} ⟩
        
      {!.C .ChainComplex.thisA n <<< (bc .ChainMapM.ChainMap.fn n <<< ab .ChainMapM.ChainMap.fn n) ∎!}  } } }

--Proof should be simple once nicely formalized because every diagram commutes...


      -- {!bc .ChainMapM.ChainMap.fn (predℤ n) <<< ab .ChainMapM.ChainMap.fn (predℤ n) <<< .A .ChainComplex.thisA n!}

      --   ≡⟨ {! assoc!} ⟩  

      -- {!{! bc .ChainMapM.ChainMap.fn (predℤ n) <<< (ab .ChainMapM.ChainMap.fn (predℤ n) <<< .A .ChainComplex.thisA n)!}

      --   ≡⟨ {! <| (λ x → bc .ChainMapM.ChainMap.fn (predℤ n) <<<  x!} ⟩

      
      -- {!{! bc .ChainMapM.ChainMap.fn (predℤ n) <<< ((.B .ChainComplex.thisA n)  <<< (ab .ChainMapM.ChainMap.fn n))!}
      
      --   ≡⟨ {!!} ⟩

      -- {!{!bc .ChainMapM.ChainMap.fn (predℤ n) <<< ((.B .ChainComplex.thisA n)  <<< (ab .ChainMapM.ChainMap.fn n))!}
      
      --   ≡⟨ {!!} ⟩
        
      -- {!.C .ChainComplex.thisA n <<< (bc .ChainMapM.ChainMap.fn n <<< ab .ChainMapM.ChainMap.fn n) ∎
