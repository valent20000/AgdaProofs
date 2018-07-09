{-# OPTIONS --cubical #-}
module Utils where

  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cubical.FromStdLib

  module _ {ℓ} {ℓ'} where
    
    -- This operator is just application, but it makes proof easier to read. See later
    infix 4 _<|_

    _<|_ : {A : Set ℓ} {B : Set ℓ'} {x y : A} (a : x ≡ y) (cont : A → B) → cont x ≡ cont y  
    a <| cont = ((cong cont) a)

    infix 3 _∙_
    _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    a ∙ b = trans a b

  symOnTrans : {A : Set} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (sym (trans p q)) ≡ trans (sym q) (sym p)

  symOnTrans = pathJ _ (pathJ _ --Induction on q and then p.
    refl)

  module _ {ℓ} where

    symOnTransL : {A : Set ℓ} {a : A} (b : A) (p : a ≡ b) (c : A) (q : b ≡ c) → (sym (trans p q)) ≡ trans (sym q) (sym p)

    symOnTransL = pathJ _ (pathJ _ --Induction on q and then p.
      refl)

  module _ {ℓ} {ℓ'} {ℓ''} where

    LmCongCong : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {x : A} (g : B → C) (f : A → B) (y : A) (p : x ≡ y) → cong g (cong f p) ≡ cong (λ x → g (f x)) p
    
    LmCongCong g f = pathJ _ (refl)




      -- infix 8 _^_
      
      -- _^_ : {A : Set} (f : A ≡ A) (n : ℕ) → A ≡ A
      -- f ^ 0 = refl
      -- f ^ (suc n) = trans f (f ^ n)

      -- LemmaIt : {A : Set} (n : ℕ) (f : A ≡ A) (p : f ≡ refl) → (f ^ n) ≡ refl
      -- LemmaIt {A} (0) f p = refl
      -- LemmaIt {A} (suc n) f p = begin
      --   trans f (f ^ n) ≡⟨ (LemmaIt n f p) <| cong (λ x → trans f x)  ⟩
      --   trans f refl ≡⟨ trans-id f ⟩
      --   f ≡⟨ p ⟩
      --   refl ∎

  module _ {ℓ} where

    LmTransSym : {A : Set ℓ} {a : A} (b : A) (q : a ≡ b) → trans q (sym q) ≡ refl
    LmTransSym {A} = pathJ _ (trans-id refl) 

    infix 8 _^_
         
    _^_ : {A :  Set ℓ} (f : A → A) (n : ℕ) → A → A
    f ^ 0 = λ x → x
    f ^ (suc n) = λ a → f ((f ^ n) a)
  
    LemmaIt : {A :  Set ℓ} {x : A} (n : ℕ) (f : A → A) (p : f x ≡ x) → ((f ^ n) x) ≡ x
    LemmaIt {A} {x} (0) f p = refl
    LemmaIt {A} {x} (suc n) f p = begin
      f ((f ^ n) x) ≡⟨ (LemmaIt n f p) <| (λ x → f x) ⟩
      f x ≡⟨ p ⟩
      x ∎

    ElimCompL : {A : Set ℓ} (n : ℕ) (e : A) → PathP _ _ _
    ElimCompL {A} n e = LemmaIt n (λ x → (primComp (λ _ → A) i0 (λ i → empty) x)) (transp-refl e)

-- You can change a transport over a composition of path in two successive transports;
  transpOfTrans : {A : Set} {a : A} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (transp (λ j → (trans p q) j) a) ≡ (transp (λ j → q j) (transp (λ j → p j) a))
  transpOfTrans {A} {a} = pathJ _ (pathJ _  (begin --Par induction sur p et q.
  
      transp (λ j → trans (λ i → A) (λ i → A) j) a                     ≡⟨ (trans-id refl) <|  (λ x → transp (λ j → x j) a) ⟩
      transp (λ j → A) a                                               ≡⟨ (transp-refl a) ⟩ 
      a                                                                ≡⟨ sym (transp-refl a) ⟩
      (transp (λ j → refl j) a)                                        ≡⟨ sym (transp-refl (transp (λ j → refl j) a)) ⟩
      (transp (λ j → refl j) (transp (λ j → refl {x = A} j) a)) ∎))

  -- Lemma to reverse the path:
  -- Saying is something is true on a path then so is it on the reverse path.
  -- To optimize our proof here we might've shown a more powerful lemma; stating that if two function 'cancel' each others; then we can obtain smth.
  -- We would then obtain a proof for pred+ as well with the same lemma for example (same principle) 
  
  LemmaTranspRev : {A : Set} {a : A} (f : A → A) (q : A ≡ A) (p : (b : A)  → transp (λ j → q j) (f b) ≡ f (transp (λ j → q j) b))  → transp (λ j → (sym q) j) (f a) ≡ f (transp (λ j → (sym q) j) a)

  LemmaTranspRev {A} {a} f q p = sym (begin
    f (transp (λ j → sym q j) a) ≡⟨  sym (transp-iso (λ i → q i) (f (transp (λ j → sym q j) a))) ⟩
    transp (\ i → q (~ i)) (transp (λ i → q i) (f (transp (λ j → sym q j) a))) ≡⟨  (p (transp (λ j → sym q j) a)) <| (λ x → transp (\ i → q (~ i)) x )  ⟩
    transp (\ i → q (~ i)) (f (transp (λ i → q i) (transp (λ j → sym q j) a))) ≡⟨ (transp-iso (λ i → q (~ i)) a) <| (λ x → transp (\ i → q (~ i)) (f x)) ⟩
    transp (\ i → q (~ i)) (f a)∎)

  transpOfTransRev : {A B C : Set} {a : C} (p : A ≡ B) (q : B ≡ C) → (transp (λ j → (trans p q) (~ j)) a) ≡ (transp (λ j → p (~ j)) (transp (λ j → q (~ j)) a))

  transpOfTransRev {A} {B} {C} {a} p q = begin
    transp (λ j → trans p q (~ j)) a ≡⟨ (symOnTrans _ p _ q <| λ x → transp (λ j → x j) a) ⟩
    transp (λ j → trans (sym q) (sym p) j) a ≡⟨ transpOfTrans _ (sym q) _ (sym p) ⟩
    transp (λ j → (sym p) j) (transp (λ j → (sym q) j) a) ≡⟨⟩
    transp (λ j → p (~ j)) (transp (λ j → q (~ j)) a)∎


  -- Use the iteration lemma to elminate comps of comps...
 
  ElimComp : {A : Set} (n : ℕ) (e : A) → PathP _ _ _
  ElimComp {A} n e = LemmaIt n (λ x → (primComp (λ _ → A) i0 (λ i → empty) x)) (transp-refl e)

  -- Could also be proven by transp-iso
  LmExchgPath : {A : Set} {a : A}  (B : Set) (p : A ≡ B) (b : B) (e : transp (λ i → p i) a ≡ b) → a ≡ transp (λ i → (sym p) i) b
  LmExchgPath {A} {a} = pathJ _ λ b e → begin
    a ≡⟨ trans (sym (transp-refl a)) e ⟩
    b ≡⟨ sym (transp-refl b) ⟩
    transp (λ i → sym (λ i₁ → A) i) b ∎