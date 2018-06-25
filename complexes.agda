{-# OPTIONS --cubical #-}
module complexes where

  open import Cubical
  open import Agda.Builtin.Nat
  open import Cubical.PathPrelude
  open import Cubical.FromStdLib
  open import Cubical.Lemmas
  open import Cubical.Examples.Int

  ------- We first prove (ℤ, 0) ≡ (ℤ, i) for every i ∈ ℤ

  ℤ = Int -- alias

  -- For natural numbers
  nPathℤ : (i : ℕ) → (ℤ ≡ ℤ)
  nPathℤ 0 = refl
  nPathℤ (suc n) = trans sucPathℤ (nPathℤ n)

  -- General case
  iPathℤ : (i : ℤ) → ℤ ≡ ℤ --Path from ℤ to ℤ using +i.
  iPathℤ (pos n) = (nPathℤ n)
  iPathℤ (negsuc n) = sym (nPathℤ (suc n))

  transpOfTrans : {A : Set} {a : A} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (transp (λ j → (trans p q) j) a) ≡ (transp (λ j → q j) (transp (λ j → p j) a))
  transpOfTrans {A} {a} = pathJ _ (pathJ _
    (begin
      transp (λ j → trans (λ i → A) (λ i → A) j) a ≡⟨ cong (λ x → transp (λ j → x j) a) (trans-id refl) ⟩
      transp (λ j → A) a ≡⟨ (transp-refl a) ⟩ 
      a ≡⟨ sym (transp-refl a) ⟩
      (transp (λ j → refl j) a) ≡⟨ sym (transp-refl (transp (λ j → refl j) a)) ⟩
       (transp (λ j → refl j) (transp (λ j → refl {x = A} j) a)) ∎))


  LemmaT : (n : ℕ) → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡ n
  LemmaT n = begin
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡⟨ cong (λ x → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) x)) (transp-refl n) ⟩
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n) ≡⟨ cong (λ x → (primComp (λ i → ℕ) i0 (λ i → empty) x)) (transp-refl n) ⟩
     (primComp (λ i → ℕ) i0 (λ i → empty) n) ≡⟨ (transp-refl n) ⟩
     n ∎

  LemmaCommN : {n : ℕ} → trans sucPathℤ (nPathℤ n) ≡ trans (nPathℤ n) sucPathℤ
  LemmaCommN {0} = trans ((trans-id sucPathℤ)) ((sym (trans-id-l sucPathℤ)))
  LemmaCommN {(suc n)} = {!!}

{--
    {!trans sucPathℤ (trans sucPathℤ (nPathℤ n))!} ≡⟨ {!cong (λ x → trans sucPathℤ x) (LemmaCommN {n = n})!} ⟩
    {!trans sucPathℤ (trans (nPathℤ n) sucPathℤ)!} ≡⟨ trans-assoc ⟩
    {!(trans (trans sucPathℤ (nPathℤ n)) sucPathℤ) ∎!}
--}

  whoZeroN : {i : ℕ} → transp (λ j → (nPathℤ i)j) (pos 0) ≡ (pos i)
  whoZeroN {0} = λ j → (pos 0) -- 
  whoZeroN {suc n} = begin
    transp (λ j → trans sucPathℤ (nPathℤ n) j) (pos 0) ≡⟨  cong (λ x → transp (λ j → x j) (pos 0)) (LemmaCommN {n = n}) ⟩
    transp (λ j → trans (nPathℤ n) sucPathℤ j) (pos 0)  ≡⟨ (let r = transpOfTrans Int (nPathℤ n) Int (sucPathℤ) in r) ⟩
    transp (λ j → sucPathℤ j) (transp (λ j → (nPathℤ n) j) (pos 0)) ≡⟨ cong (λ x → transp (λ j → sucPathℤ j) x) (whoZeroN {n}) ⟩
    transp (λ j → sucPathℤ j) (pos n) ≡⟨  cong (λ x → pos (suc x)) (LemmaT n) ⟩
    pos (suc n)∎

  symOnTrans : {A : Set} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (sym (trans p q)) ≡ trans (sym q) (sym p)

  symOnTrans = pathJ _ (pathJ _ --Induction on q and then p.
    refl)

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
      (sym (symOnTrans ? ? ? ?)) ⟩ --  HERE IS THE 'GLITCH'
      -- 2nd ? : sucPathℤ, 4th: (nPathℤ n)

    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (trans sucPathℤ (nPathℤ n))) j) (pos 0)) ≡⟨⟩
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → trans sucPathℤ (nPathℤ n) (~ j)) (pos 0)) ≡⟨
      cong (λ x → transp (λ j → sucPathℤ (~ j)) x) (LemmaNeg {n = n}) ⟩
    transp (λ j → sucPathℤ (~ j)) (negsuc n) ≡⟨ cong (λ x → negsuc (suc x)) (LemmaT n) ⟩
    negsuc (suc n)∎
      
-- ? ≡⟨ ? ⟩ ?

{--

  LemmaNeg : {n : ℕ} → (transp (λ j → (nPathℤ (suc n)) (~ j)) (pos 0)) ≡ (negsuc n)
  LemmaNeg {0} = refl --transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) (pos 0)
  LemmaNeg {suc n} = begin
    transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) (pos 0)  ≡⟨
      cong (λ x → transp (λ j → trans sucPathℤ x (~ j)) (pos 0)) (LemmaCommN {n = n}) ⟩
    transp (λ j → trans sucPathℤ (trans (nPathℤ n) sucPathℤ) (~ j)) (pos 0) ≡⟨
      cong ((λ x → transp (λ j → x (~ j)) (pos 0))) (trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ}) ⟩
      
    transp (λ j → trans (trans sucPathℤ (nPathℤ n)) sucPathℤ (~ j)) (pos 0)  ≡⟨⟩
    transp (λ j → sym (trans (trans sucPathℤ (nPathℤ n)) sucPathℤ)  j) (pos 0)  ≡⟨⟩
    transp (λ j → sym (trans (trans sucPathℤ (nPathℤ n)) sucPathℤ)  j) (pos 0)  ≡⟨⟩
    
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → trans sucPathℤ (nPathℤ n) (~ j)) (pos 0)) ≡⟨
      cong (λ x → transp (λ j → sucPathℤ (~ j)) x) (LemmaNeg{n = n}) ⟩
    transp (λ j → sucPathℤ (~ j)) (negsuc n) ≡⟨ cong (λ x → negsuc (suc x)) (LemmaT n) ⟩
    negsuc (suc n)∎

--}

  whoZero : {i : ℤ} → transp (λ j → (iPathℤ i)j) (pos 0) ≡ i
  whoZero {pos n} = whoZeroN
  whoZero {(negsuc n)} = LemmaNeg


  -- Theorem --

  allℤsame : {i : ℤ} → (ℤ , i) ≡ (ℤ , (pos 0))
  allℤsame {i} = λ j → (iPathℤ i)j , whoZero


  -------------------------------
