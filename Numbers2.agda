{-# OPTIONS --cubical #-}
module Numbers2 where

  open import Agda.Primitive --lsuc etc...
  open import Cubical.FromStdLib renaming (_+_ to _+ℕ_)
  open import Cubical.Examples.Int 
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using

  open import Utils


  ℤ = Int

  -- For natural numbers
  nPathℤ : (i : ℕ) → (ℤ ≡ ℤ)
  nPathℤ 0 = refl
  nPathℤ (suc n) = trans sucPathℤ (nPathℤ n)

  -- General case
  iPathℤ : (i : ℤ) → ℤ ≡ ℤ --Path from ℤ to ℤ using +i.
  iPathℤ (pos n) = (nPathℤ n)
  iPathℤ (negsuc n) = sym (nPathℤ (suc n))

  infix 10 _+_
  
  _+_ : (a b : ℤ) → ℤ
  _+_ a (pos 0) = a
  _+_ a (pos (suc n)) = sucℤ (a + (pos n))
  _+_ a (negsuc 0) = (predℤ a)
  _+_ a (negsuc (suc n)) = predℤ( a + negsuc n )

  -- Trivial Lemma about +

  +-0 : (b : ℤ) → pos zero + b ≡ b

  +-0 (pos 0) =  refl
  +-0 (negsuc 0) = refl
  +-0 (pos (suc n)) = begin
    sucℤ (pos zero + pos n) ≡⟨ (+-0 (pos n) <| λ x → sucℤ x) ⟩
    sucℤ (pos n) ≡⟨⟩
    pos (suc n)∎
    
  +-0 (negsuc (suc n)) = begin
    predℤ (pos zero + negsuc n) ≡⟨ (+-0 (negsuc n) <| λ x → predℤ x) ⟩
    predℤ (negsuc n) ≡⟨⟩
    negsuc (suc n) ∎
      

  postulate LemmaCommN : (n : ℕ) → trans sucPathℤ (nPathℤ n) ≡ trans (nPathℤ n) sucPathℤ


  -- LemmaCommN (0) = trans ((trans-id sucPathℤ)) ((sym (trans-id-l sucPathℤ)))
  -- LemmaCommN (suc n) = begin
  --   trans sucPathℤ (trans sucPathℤ (nPathℤ n)) ≡⟨ cong (λ x → trans sucPathℤ x) (LemmaCommN n) ⟩
  --   trans sucPathℤ (trans (nPathℤ n) sucPathℤ) ≡⟨ trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ} ⟩
  --   (trans (trans sucPathℤ (nPathℤ n)) sucPathℤ) ∎
  --
  
  LemmaSucP : (x : ℤ) → transp (λ j → sucPathℤ j) x ≡ (sucℤ x)
  LemmaSucP (pos 0) = refl
  LemmaSucP (negsuc 0) = refl
  LemmaSucP (pos (suc n)) = ElimComp 3 n <| λ x → pos (suc (suc x))
  LemmaSucP (negsuc (suc n)) = ElimComp 3 n <| λ x → negsuc x

  LemmaIP : (i x : ℤ) → transp (λ j → (iPathℤ i) j) x ≡ x + i
  LemmaIP (pos 0) x = transp-refl x
  
  LemmaIP (negsuc 0) x = let A = ElimComp 4 (predℤ ((empCmp ^ 3) x)) ; B = ElimComp 3 x <| (λ e → predℤ e) in λ j → trans A B j

  LemmaIP (pos (suc n)) x = begin
    transp (λ j → trans sucPathℤ (nPathℤ n) j) x ≡⟨ (LemmaCommN n <| λ e → transp (λ j → e j) x ) ⟩
    transp (λ j → trans (nPathℤ n) sucPathℤ j) x ≡⟨ transpOfTrans ℤ (nPathℤ n) ℤ sucPathℤ ⟩
    transp (λ j → sucPathℤ j) (transp (λ j → (nPathℤ n) j) x) ≡⟨ ( LemmaIP (pos n) x <| λ e → transp (λ j → sucPathℤ j) e ) ⟩
    transp (λ j → sucPathℤ j) (x + (pos n)) ≡⟨ ElimComp 3 (sucℤ (x + pos n)) ⟩
    sucℤ (x + pos n) ∎

  LemmaIP (negsuc (suc n)) x = begin
    transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) x ≡⟨ transpOfTransRev sucPathℤ (trans sucPathℤ (nPathℤ n)) ⟩
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → (trans sucPathℤ (nPathℤ n)) (~ j)) x) ≡⟨ (LemmaIP (negsuc n) x <| λ e → transp (λ j → sucPathℤ (~ j)) e) ⟩
    transp (λ j → sucPathℤ (~ j)) (x + negsuc n) ≡⟨
    
    (let A = ElimComp 2 (x + negsuc n) <| (λ e → primComp (λ i → Int) i0 (λ i → empty) (predℤ e)) ; B = ElimComp 1 (predℤ (x + negsuc n)) in λ j →  (trans A B) j ) ⟩
         
    predℤ (x + negsuc n) ∎

  -- Consequence :

  whoZero : (i : ℤ) → transp (λ j → (iPathℤ i)j) (pos 0) ≡ i
  whoZero i = trans (LemmaIP i (pos 0)) (+-0 i)

  ---* Lemmas to move suc and pred around. *---
 
  suc+ : (a b : ℤ) → sucℤ (a + b) ≡ (sucℤ a) + b
 
  suc+ a (pos 0) = refl
    
  suc+ a (negsuc 0) = begin
  
    sucℤ (a + negsuc zero)                      ≡⟨ sucPred a ⟩
    a                                           ≡⟨ sym (predSuc a) ⟩
    sucℤ a + negsuc zero ∎
    
  suc+ a (pos (suc n)) = begin
  
    sucℤ (sucℤ (a + pos n))                     ≡⟨ (suc+ a (pos n) <| λ x → sucℤ x) ⟩
    sucℤ (sucℤ a + pos n) ∎

    
  suc+ a (negsuc (suc n)) = begin
  
    sucℤ (predℤ (a + negsuc n))                 ≡⟨ sucPred (a + negsuc n) ⟩
    (a + negsuc n)                              ≡⟨ sym(predSuc (a + negsuc n)) ⟩
    predℤ (sucℤ (a + negsuc n))                 ≡⟨ (suc+ a (negsuc n) <| λ x → predℤ x) ⟩
    predℤ (sucℤ a + negsuc n) ∎


  pred+ : (a b : ℤ) → predℤ (a + b) ≡ (predℤ a) + b
  pred+ a b = begin
  
    predℤ (a + b)                               ≡⟨ (sym(sucPred a) <| λ x → predℤ (x + b)) ⟩
    predℤ (sucℤ(predℤ a) + b)                   ≡⟨ (sym(suc+ (predℤ a) b) <| λ x → predℤ x) ⟩
    predℤ(sucℤ(predℤ a + b))                    ≡⟨ predSuc (predℤ a + b) ⟩
    predℤ a + b ∎


  -- Theorem: predℤ and transporting along +i can be exchanged.
  
  LemmaPredTranspA : (i p : ℤ) → (transp (λ j → (iPathℤ i) j) (predℤ p)) ≡ (predℤ (transp (λ j → (iPathℤ i) j) p))
  LemmaPredTranspA i p = begin
  
    transp (λ j → iPathℤ i j) (predℤ p)         ≡⟨ (LemmaIP i (predℤ p)) ⟩
    (predℤ p) + i                               ≡⟨ sym (pred+ p i) ⟩
    predℤ (p + i)                               ≡⟨ ( sym (LemmaIP i p) <| λ x → predℤ x) ⟩
    predℤ (transp (λ j → iPathℤ i j) p) ∎    


  -- Theorem: predℤ and transporting along -i can be exchanged.
  
  LemmaPredTransp : (i p : ℤ) → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
  LemmaPredTransp i p = LemmaTranspRev {a = p} predℤ (iPathℤ i) (LemmaPredTranspA i)



  ------ ------- Unused Lemmas:
 
  -- LemmaNeed : (i p : ℤ) → (predℤ p) + i ≡ predℤ (p + i)
  -- LemmaNeed (pos 0) p =  refl
  -- LemmaNeed (negsuc 0) p = refl
  -- LemmaNeed (pos (suc n)) p = begin
  --   sucℤ (predℤ p + pos n) ≡⟨ (sym( pred+ p (pos n) ) <| λ x → sucℤ x) ⟩
  --   sucℤ (predℤ (p + pos n)) ≡⟨ sucPred (p + pos n) ⟩
  --   p + pos n ≡⟨ sym (predSuc (p + pos n)) ⟩
  --   predℤ (sucℤ (p + pos n))∎
    
  -- LemmaNeed (negsuc (suc n)) p = begin
  --   predℤ (predℤ p + negsuc n) ≡⟨ (sym (pred+ p (negsuc n)) <| λ x → predℤ x) ⟩
  --   predℤ (predℤ (p + negsuc n)) ∎

  -- sucIs+ : (a : ℤ) → sucℤ a ≡ (pos 1) + a

  -- sucIs+ (pos 0) = refl
  
  -- sucIs+ (negsuc 0) = refl
  
  -- sucIs+ (pos (suc n)) = begin
  
  --   pos (suc (suc n))                          ≡⟨ ((sucIs+ (pos n)) <| λ x → sucℤ x) ⟩
  --   sucℤ (pos 1 + pos n)∎
    
  -- sucIs+ (negsuc (suc n)) = begin
  
  --   negsuc n                                   ≡⟨ sym (predSuc (negsuc n)) ⟩
  --   predℤ(sucℤ(negsuc n))                      ≡⟨ (sucIs+ (negsuc n) <| λ x → predℤ x) ⟩
  --   predℤ (pos 1 + negsuc n)∎


  -- predIs+ : (a : ℤ) → predℤ a ≡ (negsuc 0) + a

  -- predIs+ (pos 0) = refl
  
  -- predIs+ (negsuc 0) = refl
  
  -- predIs+ (pos (suc n)) = begin
  
  --   pos n                                      ≡⟨ sym(sucPred (pos n)) ⟩
  --   sucℤ( predℤ (pos n) )                      ≡⟨ (predIs+ (pos n) <| λ x → sucℤ x) ⟩
  --   sucℤ (negsuc 0 + pos n) ∎
    
  -- predIs+ (negsuc (suc n)) = begin
  
  --   negsuc (suc (suc n))                       ≡⟨ (predIs+ (negsuc n) <| λ x → predℤ x) ⟩
  --   predℤ (negsuc 0 + negsuc n) ∎
