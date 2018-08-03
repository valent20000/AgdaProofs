{-# OPTIONS --cubical #-}
module Cat.Instance.IntCategory where

  open import Cubical.NType.Properties
  
  open import Cat.Category
  open import Cat.Equivalence
  open import Cat.Prelude --hiding (_×_) --using

  open import Cat.Category.ZeroCategory
  open import Cat.Categories.Fun

  import Data.Nat.Base as ℕ
  open import Data.Integer.Base renaming (+_ to pos) renaming (-[1+_] to negsuc)
  open import Data.Integer.Properties

  open import Utils

  module IntCategoryM where

    module Lemmas where

      open Data.Integer.Base

      postulate isSet-ℤ : isSet ℤ

      -- There is only one way to prove an equality
      isProp-arrow : ∀ k l → isProp (k ≤ l)
      isProp-arrow k l x y = eqTr (≤-irrelevance x y)


      isAssoc-arrow : {a b c d : ℤ} (p1 : a ≤ b) (p2 : b ≤ c) (p3 : c ≤ d) → ≤-trans (≤-trans p1 p2) p3 ≡ ≤-trans p1 (≤-trans p2 p3)
      isAssoc-arrow {a} {b} {c} {d} p1 p2 p3 = isProp-arrow a d (≤-trans (≤-trans p1 p2) p3) (≤-trans p1 (≤-trans p2 p3))
      

      trans-refl-arrowl : ∀ {A B} (f : A ≤ B)   → ≤-trans f ≤-refl ≡ f
      trans-refl-arrowl {A} {B} f = isProp-arrow A B (≤-trans f ≤-refl) f

      trans-refl-arrowr : ∀ {A B} (f : A ≤ B)   → ≤-trans ≤-refl f ≡ f
      trans-refl-arrowr {A} {B} f = isProp-arrow A B (≤-trans ≤-refl f) f


    rawIC : RawCategory lzero lzero
    RawCategory.Object rawIC =  ℤ
    RawCategory.Arrow rawIC k l = k ≤ l
    RawCategory.identity rawIC {A} = ≤-refl
    RawCategory._<<<_ rawIC p2 p1 = ≤-trans p1 p2

    isPreIC : IsPreCategory rawIC
    IsPreCategory.isAssociative isPreIC {a} {b} {c} {d} {p1} {p2} {p3}  = Lemmas.isAssoc-arrow p1 p2 p3
    fst (IsPreCategory.isIdentity isPreIC {A} {B} {f}) = Lemmas.trans-refl-arrowl f
    snd (IsPreCategory.isIdentity isPreIC {A} {B} {f}) = Lemmas.trans-refl-arrowr f
    IsPreCategory.arrowsAreSets isPreIC {A} {B} = HasLevel+1 ⟨-1⟩ (Lemmas.isProp-arrow A B)  

    open RawCategory rawIC
    open IsPreCategory hiding (_≊_)
    
    LemmaProp : {A B : ℤ} → isProp (A ≊ B)
    LemmaProp {A} {B} = propSig (Lemmas.isProp-arrow A B) λ f →
                    propSig (Lemmas.isProp-arrow B A) λ g →
                    propSig (HasLevel+1 ⟨-1⟩ (Lemmas.isProp-arrow A A) (≤-trans f g)  ≤-refl) λ _ →
                            (HasLevel+1 ⟨-1⟩ (Lemmas.isProp-arrow B B) (≤-trans g f)  ≤-refl)

    IntCategory : Category lzero lzero
    
    Category.raw IntCategory = rawIC
    (IsCategory.isPreCategory (Category.isCategory IntCategory)) = isPreIC
    (IsCategory.univalent (Category.isCategory IntCategory)) {A} {B} = IsPreCategory.univalenceFrom≃ isPreIC lemmaUniv
    
      where

        module _ {A B : ℤ} where
        
          -- To equivalence
          toEq : A ≡ B → A ≊ B 
          fst (toEq eg) = transp (λ i → A ≤ (eg i)) (≤-refl)
          fst (snd (toEq eg)) = transp (λ i → B ≤ (sym eg i)) (≤-refl)
          fst (snd (snd (toEq eg))) = Lemmas.isProp-arrow A (eg i0) _ _
          snd (snd (snd (toEq eg))) = Lemmas.isProp-arrow B (eg i1) _ _
  
  
          eqTo : A ≊ B → A ≡ B
          eqTo x = eqTr (≤-antisym (x .fst) (x .snd .fst))


          eqToEq : (y : A ≊ B) → toEq (eqTo y) ≡ y
          eqToEq y = LemmaProp (toEq (eqTo y)) y 
  
  
          egToEg : (x : A ≡ B) → eqTo (toEq x) ≡ x
          egToEg x = Lemmas.isSet-ℤ A B (eqTo (toEq x)) x
          


          lemmaUniv : (A ≡ B) ≃ (A ≊ B) ----.
        
          lemmaUniv .fst = toEq
          lemmaUniv .snd = gradLemma toEq eqTo eqToEq egToEg


    
    
  module IntFunc {ℓa ℓb} (catZ : ZeroCategory ℓa ℓb) where

    IntFunc : Category (lzero Cat.Prelude.⊔ lzero Cat.Prelude.⊔ ℓa Cat.Prelude.⊔ ℓb) (lzero Cat.Prelude.⊔ lzero Cat.Prelude.⊔ ℓb)
    IntFunc = Fun.Fun IntCategoryM.IntCategory (catZ .ZeroCategory.c)
