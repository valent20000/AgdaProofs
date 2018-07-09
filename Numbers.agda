{-# OPTIONS --cubical #-}
module Numbers where

  -- open import Cubical
  --open import Agda.Builtin.Nat
  open import Agda.Primitive --lsuc etc...
  open import Agda.Builtin.Equality renaming (_≡_ to _≡b_) renaming (refl to reflb)

  open import Data.Integer.Base renaming (suc to sucℤ) renaming (pred to predℤ) hiding (_⊔_)
  open import Data.Integer.Properties
  open import Data.Nat.Base hiding (_⊔_) hiding (_+_)
  open import Agda.Builtin.Int

  --open import Cubical.FromStdLib
  --open import Cubical.Examples.Int
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using

  open import Utils hiding (_<|_)

  ------- We first prove (ℤ, 0) ≡ (ℤ, i) for every i ∈ ℤ

  -- This lemma transforms equality from the standard library to Cubical equalities.
  
  eqTr : {A : Set} {a b : A} (p : a ≡b b) → a ≡ b
  eqTr reflb = refl


  -- Taken from Cubical.Examples.Int
  -- Adapted to work with the stdlib.

  sucPred : ∀ i → sucℤ (predℤ i) ≡ i
  sucPred (pos zero)       = refl
  sucPred (pos (suc n))    = refl
  sucPred (negsuc zero)    = refl
  sucPred (negsuc (suc n)) = refl

  predSuc : ∀ i → predℤ (sucℤ i) ≡ i
  predSuc (pos zero)       = refl
  predSuc (pos (suc n))    = refl
  predSuc (negsuc zero)    = refl
  predSuc (negsuc (suc n)) = refl

  sucPathℤ : ℤ ≡ ℤ
  sucPathℤ = equivToPath suc-equiv
    where
    suc-equiv : Σ _ (isEquiv ℤ ℤ)
    suc-equiv .fst = sucℤ
    suc-equiv .snd = gradLemma sucℤ predℤ sucPred predSuc

  module _ {ℓ} {ℓ'} where
    
    -- This operator is just application, but it makes proof easier to read. See later
    infix 4 _<|_

    _<|_ : {A : Set ℓ} {B : Set ℓ'} (a : A) (b : A → B) → B 
    a <| b = (b a)


  -- For natural numbers
  nPathℤ : (i : ℕ) → (ℤ ≡ ℤ)
  nPathℤ 0 = refl
  nPathℤ (suc n) = trans sucPathℤ (nPathℤ n)

  -- General case
  iPathℤ : (i : ℤ) → ℤ ≡ ℤ --Path from ℤ to ℤ using +i.
  iPathℤ (pos n) = (nPathℤ n)
  iPathℤ (negsuc n) = sym (nPathℤ (suc n))


  LemmaT : (n : ℕ) → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡ n
  LemmaT n = begin
  
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡⟨ (transp-refl n)  <|
         cong (λ x → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) x)) ⟩
         
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n) ≡⟨ (transp-refl n) <|
        cong (λ x → (primComp (λ i → ℕ) i0 (λ i → empty) x))⟩
        
      primComp (λ i → ℕ) i0 (λ i → empty) n ≡⟨ (transp-refl n) ⟩
      n ∎

  postulate LemmaCommN : {n : ℕ} → trans sucPathℤ (nPathℤ n) ≡ trans (nPathℤ n) sucPathℤ
  --LemmaCommN {0} = trans ((trans-id sucPathℤ)) ((sym (trans-id-l sucPathℤ)))
  --LemmaCommN {(suc n)} = begin
    --trans sucPathℤ (trans sucPathℤ (nPathℤ n)) ≡⟨ cong {! λ x → trans sucPathℤ x!} LemmaCommN ⟩
    --{!trans sucPathℤ (trans (nPathℤ n) sucPathℤ)!} ≡⟨ trans-assoc ⟩
    --{!(trans (trans sucPathℤ (nPathℤ n)) sucPathℤ) ∎!}

  whoZeroN : {i : ℕ} → transp (λ j → (nPathℤ i)j) (pos 0) ≡ (pos i)
  whoZeroN {0} = λ j → (pos 0) -- 
  whoZeroN {suc n} = begin
    transp (λ j → trans sucPathℤ (nPathℤ n) j) (pos 0)              ≡⟨ (LemmaCommN {n = n}) <| cong (λ x → transp (λ j → x j) (pos 0)) ⟩
    transp (λ j → trans (nPathℤ n) sucPathℤ j) (pos 0)              ≡⟨ transpOfTrans ℤ (nPathℤ n) ℤ (sucPathℤ) ⟩
    transp (λ j → sucPathℤ j) (transp (λ j → (nPathℤ n) j) (pos 0)) ≡⟨ (whoZeroN {n}) <| cong (λ x → transp (λ j → sucPathℤ j) x) ⟩
    transp (λ j → sucPathℤ j) (pos n)                               ≡⟨ (LemmaT n) <| cong (λ x → pos (suc x)) ⟩
    pos (suc n)∎

  LemmaNeg : {n : ℕ} → (transp (λ j → (nPathℤ (suc n)) (~ j)) (pos 0)) ≡ (negsuc n)
  LemmaNeg {0} = refl --transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) (pos 0)
  LemmaNeg {suc n} = begin
    transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) (pos 0)  ≡⟨⟩
    transp (λ j → (sym (trans sucPathℤ (trans sucPathℤ (nPathℤ n)))) j) (pos 0) ≡⟨
      cong ((λ x → transp (λ j → x j) (pos 0))) ((symOnTrans ℤ sucPathℤ ℤ ((trans sucPathℤ (nPathℤ n))))) ⟩
      
    transp (λ j → (trans (sym (trans sucPathℤ (nPathℤ n))) (sym sucPathℤ)) j) (pos 0) ≡⟨
      cong ( λ x → transp (λ j → (trans x (sym sucPathℤ)) j) (pos 0)) (symOnTrans ℤ sucPathℤ ℤ ((nPathℤ n))) ⟩
      
    transp (λ j → trans (trans (sym (nPathℤ n)) (sym sucPathℤ)) (sym sucPathℤ) j) (pos 0) ≡⟨
      transpOfTrans {ℤ} {(pos 0)} ℤ (trans (sym (nPathℤ n)) (sym sucPathℤ)) ℤ (sym sucPathℤ) ⟩
      
    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (trans (sym (nPathℤ n)) (sym sucPathℤ)) j) (pos 0)) ≡⟨
      cong (λ x → transp (λ j → (sym sucPathℤ) j) (transp (λ j → x j) (pos 0)))
      (sym (symOnTrans ℤ sucPathℤ ℤ (nPathℤ n))) ⟩

    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (trans sucPathℤ (nPathℤ n))) j) (pos 0)) ≡⟨⟩
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → trans sucPathℤ (nPathℤ n) (~ j)) (pos 0)) ≡⟨
      cong (λ x → transp (λ j → sucPathℤ (~ j)) x) (LemmaNeg {n = n}) ⟩
    transp (λ j → sucPathℤ (~ j)) (negsuc n) ≡⟨ cong (λ x → negsuc (suc x)) (LemmaT n) ⟩
    negsuc (suc n)∎
      

  whoZero : {i : ℤ} → transp (λ j → (iPathℤ i)j) (pos 0) ≡ i
  whoZero {pos n} = whoZeroN
  whoZero {(negsuc n)} = LemmaNeg

  {--

  Here would be an elegant way to prove LemmaPredTransp.
  Problem being, whoIsWho requires to prove a lemma simillar (for suc though)
 
  whoIsWho : {i p : ℤ} → transp (λ j → (iPathℤ i)j) p ≡ (i + p)
  whoIsWho {i} {(pos 0)} = trans whoZero (sym (eqTr (+-identityʳ i))) 
  whoIsWho {i} {(pos (suc n))} = {!!}
  whoIsWho {i} {(negsuc 0)} = {!!}
  whoIsWho {i} {(negsuc (suc n))} = {!!}

  -- Taking the path in the opposite direction.
  whoIsWhoRev : {i p : ℤ} → transp (λ j → (sym (iPathℤ i)) j) p ≡ (p - i)
  whoIsWhoRev = {!!}

  -- transp (λ j → transp P (p - i) ≡ p ≡ transp P (transp ~P p)

  LemmaPredTransp : {i p : ℤ} → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
  LemmaPredTransp {i} {p} = begin
    (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡⟨ whoIsWhoRev ⟩
    (predℤ p) - i                                 ≡⟨⟩
    negsuc 0 + p + - i                            ≡⟨ (+-assoc (negsuc 0) p (- i)) <| eqTr ⟩
    negsuc 0 + (p - i)                            ≡⟨⟩
    predℤ (p - i)                                 ≡⟨ (sym whoIsWhoRev) <| cong (λ x → (predℤ x)) ⟩
    (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))∎

  --}

  -- Uninteresting lemma; because of the computational properties of cubical we sometimes get 3 primComps of p on a constant path; We can eliminate them. 
  LemmaT2 : (p : ℤ)  → primComp (λ i → ℤ) i0 (λ i → empty) (primComp (λ _ → ℤ) i0 (λ i → empty) (primComp (λ i → ℤ) i0 (λ i → empty) p)) ≡ p
  LemmaT2 p = begin
    primComp (λ i → ℤ) i0 (λ i → empty)
      (primComp (λ _ → ℤ) i0 (λ i → empty)
       (primComp (λ i → ℤ) i0 (λ i → empty) p)) ≡⟨  transp-refl p <| cong (λ x → primComp (λ i → ℤ) i0 (λ i → empty) (primComp (λ _ → ℤ) i0 (λ i → empty) x)) ⟩
    primComp (λ i → ℤ) i0 (λ i → empty)
      (primComp (λ _ → ℤ) i0 (λ i → empty) p) ≡⟨ transp-refl p <| cong (λ x → primComp (λ i → ℤ) i0 (λ i → empty) x) ⟩
    primComp (λ i → ℤ) i0 (λ i → empty) p ≡⟨ transp-refl p ⟩
    p ∎

  LemmaPredSucP : (p : ℤ) → transp (λ j → sucPathℤ j) (predℤ p) ≡ predℤ (transp (λ j → sucPathℤ j) p) -- ≡ p
  LemmaPredSucP p = begin
    transp (λ j → sucPathℤ j) (predℤ p) ≡⟨ LemmaT2 (pos 1 + (negsuc 0 + p)) ⟩
    pos 1 + (negsuc 0 + p) ≡⟨ (+-assoc (pos 1) (negsuc 0) p) <| (λ x → sym (eqTr x)) ⟩
    pos 1 + negsuc 0 + p ≡⟨⟩
    negsuc 0 + pos 1 + p ≡⟨ (+-assoc (negsuc 0) (pos 1) p) <| eqTr ⟩
    negsuc 0 + (pos 1 + p) ≡⟨ ((LemmaT2 (pos 1 + p)) <| λ y → (sym (cong (λ x → negsuc 0 + x) y))) ⟩
    predℤ (transp (λ j → sucPathℤ j) p)∎

  abstract
      LemmaPredTransp : {i p : ℤ} → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
     
      LemmaPredTransp {pos 0} {p} = begin
        transp (λ j → sym (λ _ → ℤ) j) (predℤ p) ≡⟨ transp-refl (predℤ p) ⟩
        predℤ p                                  ≡⟨ sym (transp-refl p) <| cong (λ x → predℤ x) ⟩
        predℤ (transp (λ j → sym (λ _ → ℤ) j) p) ∎

      LemmaPredTransp {negsuc 0} {p} = begin
        transp (λ j → sym (λ i → trans sucPathℤ (λ _ → ℤ) (~ i)) j) (predℤ p)     ≡⟨⟩
        transp (λ j → trans sucPathℤ (λ _ → ℤ) j) (predℤ p)                       ≡⟨ transpOfTrans {a = (predℤ p)} ℤ sucPathℤ ℤ refl ⟩ --transpoftrans
        transp (λ j → ℤ)  (transp (λ j → sucPathℤ j) (predℤ p))                   ≡⟨  transp-refl (transp (λ j → sucPathℤ j) (predℤ p))  ⟩
        transp (λ j → sucPathℤ j) (predℤ p)                                       ≡⟨ (LemmaPredSucP p) ⟩ --Normal form + lemma of 3 primComp
        predℤ (transp (λ j →  sucPathℤ j) p)                                      ≡⟨ ((transp-refl (transp (λ j →  sucPathℤ j) p)) <| λ y → sym (cong (λ x → predℤ x) y)) ⟩
        predℤ (transp (λ j → ℤ) (transp (λ j →  sucPathℤ j) p))                   ≡⟨ (transpOfTrans {a = p} ℤ sucPathℤ ℤ refl <| λ y → sym (cong (λ x → predℤ x) y)) ⟩
        predℤ (transp (λ j →  trans sucPathℤ (λ _ → ℤ) j) p)                      ≡⟨⟩
        predℤ (transp (λ j → sym (λ i → trans sucPathℤ (λ _ → ℤ) (~ i)) j) p) ∎
        

      LemmaPredTransp {pos (suc n)} {p} = begin
        transp (λ j → sym (trans sucPathℤ (nPathℤ n)) j) (predℤ p) ≡⟨ symOnTrans ℤ sucPathℤ ℤ (nPathℤ n) <| cong (λ x → transp (λ j → x j) (predℤ p)) ⟩
        transp (λ j →  (trans (sym (nPathℤ n)) (sym sucPathℤ)) j) (predℤ p) ≡⟨ transpOfTrans {a = (predℤ p)} ℤ (sym (nPathℤ n)) ℤ  (sym sucPathℤ) ⟩
        transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) (predℤ p)) ≡⟨⟩
        transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) (predℤ p)) ≡⟨ (LemmaPredTransp {i = pos n} {p = p}) <| cong (λ x → transp (λ j → (sym sucPathℤ) j) x) ⟩
        transp (λ j → (sym sucPathℤ) j) (predℤ (transp (λ j → (sym (nPathℤ n)) j) p)) ≡⟨ (LemmaTranspRev {a = (transp (λ j → (sym (nPathℤ n)) j) p)} predℤ sucPathℤ LemmaPredSucP) ⟩
        predℤ (transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) p)) ≡⟨ sym (transpOfTrans {a = p} ℤ (sym (nPathℤ n)) ℤ  (sym sucPathℤ)) <| cong (λ x → predℤ x) ⟩
        predℤ (transp (λ j → trans (sym (nPathℤ n)) (sym sucPathℤ) j) p) ≡⟨ (sym (symOnTrans ℤ sucPathℤ ℤ (nPathℤ n))) <| cong (λ x → predℤ (transp (λ j → x j) p))  ⟩
        predℤ (transp (λ j → sym (trans sucPathℤ (nPathℤ n)) j) p)∎


      LemmaPredTransp {negsuc (suc n) } {p} = begin
        transp (λ j → sym (λ i → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ i)) j) (predℤ p) ≡⟨⟩
        transp (λ j →  trans sucPathℤ (trans sucPathℤ (nPathℤ n)) j) (predℤ p) ≡⟨  LemmaCommN {n = n} <| cong (λ x →  transp (λ j →  trans sucPathℤ x j) (predℤ p)) ⟩
        transp (λ j →  trans sucPathℤ (trans (nPathℤ n) sucPathℤ) j) (predℤ p) ≡⟨  trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ} <| cong (λ x → transp (λ j → x j) (predℤ p)) ⟩
        transp (λ j →  trans (trans sucPathℤ (nPathℤ n)) sucPathℤ j) (predℤ p) ≡⟨  transpOfTrans {a = predℤ p} ℤ (trans sucPathℤ (nPathℤ n)) ℤ sucPathℤ ⟩
        transp (λ j → sucPathℤ j) (transp (λ j → (trans sucPathℤ (nPathℤ n)) j) (predℤ p)) ≡⟨⟩
        transp (λ j → sucPathℤ j) (transp (λ j → sym (λ i → (trans sucPathℤ (nPathℤ n)) (~ i)) j) (predℤ p)) ≡⟨ (LemmaPredTransp {i = negsuc n} {p = p}) <| cong (λ x → transp (λ j → sucPathℤ j) x) ⟩
        transp (λ j → sucPathℤ j) (predℤ (transp (λ j → sym (λ i → trans sucPathℤ (nPathℤ n) (~ i)) j) p)) ≡⟨⟩
        transp (λ j → sucPathℤ j) (predℤ (transp (λ j → trans sucPathℤ (nPathℤ n) j) p)) ≡⟨ LemmaPredSucP  (transp (λ j → trans sucPathℤ (nPathℤ n) j) p) ⟩
        predℤ (transp (λ j → sucPathℤ j) (transp (λ j → trans sucPathℤ (nPathℤ n) j) p)) ≡⟨  sym (transpOfTrans {a = p} ℤ (trans sucPathℤ (nPathℤ n)) ℤ sucPathℤ) <| cong (λ x → predℤ x) ⟩
        predℤ (transp (λ j → trans (trans sucPathℤ (nPathℤ n)) sucPathℤ j) p) ≡⟨ sym (trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ}) <| cong (λ x → predℤ (transp (λ j → x j) p) )  ⟩
        predℤ (transp (λ j → trans sucPathℤ (trans (nPathℤ n) sucPathℤ) j) p) ≡⟨ sym (LemmaCommN {n = n} <| cong (λ x →  transp (λ j →  trans sucPathℤ x j) p)) <| cong (λ x → predℤ x) ⟩
        predℤ (transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) j) p) ≡⟨⟩
        predℤ (transp (λ j → sym (λ i → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ i)) j) p) ∎


  --LemmaPredTransp : {i p : ℤ} → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
  --LemmaPredTransp {i} {p} = LemmaPredTransp1 {i = i} {p = p}


  -- Theorem --
  ℤ,0 : Σ Set (λ x → x)
  ℤ,0 = (ℤ , (pos 0))

  allℤsame : {i : ℤ} →  ℤ,0 ≡ (ℤ , i)
  allℤsame {i} = λ j → (iPathℤ i)j , toPathP {A = (λ j → (iPathℤ i)j)} (whoZero {i = i}) j

  {--
  Singleton version:

  Sing : (i : ℤ) → Set
  Sing i = (Σ ℤ (λ y → y ≡ i))

  whoZeroS : {i : ℤ} → (Sing (pos 0)) ≡ (Sing i)
  whoZeroS {i} = λ j → {!!}

  ℤ,0 : Set
  ℤ,0 = ℤ × (Sing (pos 0))

  allℤsame : {i : ℤ} →  ℤ,0 ≡ (ℤ × (Sing i))
  allℤsame {i} = λ j → (iPathℤ i)j × whoZeroS{i = i} j
  
  --}
