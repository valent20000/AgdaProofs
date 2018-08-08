{-# OPTIONS --cubical #-}

{-# OPTIONS --allow-unsolved-metas #-}

module Cat.Instance.NatLemmas where

  open import Agda.Primitive --lsuc etc...
  
  open import Cubical.PathPrelude
  open import Cat.Prelude --hiding (_×_) --using

  open import Utils

  open import Data.Nat.Base hiding (_⊔_) hiding (_^_) renaming (_≤_ to _ℕ≤_) renaming (_+_ to _+ℕ_)
  open import Data.Nat.Properties.Simple using (+-right-identity) --hiding (+-comm ; +-assoc)
  import Data.Nat.Properties as Np

  open import Data.Integer.Base hiding (_⊔_) renaming (suc to sucℤ) renaming (pred to predℤ) renaming (+_ to pos) renaming (-[1+_] to negsuc)

  open import Data.Integer.Properties

  import Cat.Instance.IntCategory as IC

  lemma-n : ∀ n k → negsuc (n +ℕ (suc k)) ≡ (negsuc n) + (negsuc k)
  lemma-n zero k = refl
  lemma-n (suc n) k = begin
    negsuc (suc (n +ℕ suc k))                      ≡⟨ ((Np.+-comm n (suc k) >| eqTr) <| \ x → negsuc (suc x)) ⟩
    negsuc (suc (suc k +ℕ n))                      ≡⟨ sym ((Np.+-comm n  k >| eqTr) <| \ x → negsuc (suc (suc x))) ⟩
    negsuc (suc (suc (n +ℕ k))) ∎

  ineq-cmp : {i j : ℤ} (p : j ≤ i) → Σ[ n ∈ ℕ ] (j + pos n ≡ i)
  ineq-cmp {pos n} {pos m} (+≤+ m≤n) = ((Np.≤⇒≤″ m≤n) ._≤″_.k) , (eqTr ((Np.≤⇒≤″ m≤n) ._≤″_.proof) <| \ x → pos x)
  ineq-cmp {pos n} {negsuc m} -≤+ = n +ℕ (suc m) , (begin
    n +ℕ suc m ⊖ suc m        ≡⟨ ((Np.+-comm n (suc m) >| eqTr) <| \ x → x ⊖ suc m) ⟩
    suc m +ℕ n ⊖ suc m        ≡⟨ ((Np.+-comm 0 (suc m) >| eqTr) <| \ x → suc m +ℕ n ⊖ x) ⟩
    suc m +ℕ n ⊖ (suc m +ℕ 0) ≡⟨ +-cancelˡ-⊖ (suc m) n 0 >| eqTr ⟩
    pos n ∎)
    
  ineq-cmp {negsuc n} {negsuc m} (-≤- n≤m) with inspect ((Np.≤⇒≤″ n≤m) ._≤″_.k)
  ...  | 0 with≡ eq = 0 ,
    (begin
      negsuc m                       ≡⟨ (sym (eqTr ((Np.≤⇒≤″ n≤m) ._≤″_.proof)) <|  \ x → negsuc x ) ∙ (eq <| \ x → negsuc (n +ℕ x)) ⟩
      negsuc (n +ℕ 0)                ≡⟨ ((Np.+-comm n 0 >| eqTr) <| \ x → negsuc x) ⟩                        
      negsuc n  ∎)
  ...  | (suc j) with≡ eq = (suc j) ,
    (begin
      negsuc m + pos (suc j)                  ≡⟨ (sym (eqTr ((Np.≤⇒≤″ n≤m) ._≤″_.proof)) <|  \ x → negsuc x + pos (suc j)) ∙ (eq <| \ x → j ⊖ (n +ℕ x)) ⟩
      negsuc (n +ℕ (suc j)) + pos (suc j)     ≡⟨ (lemma-n n j <| \ x → x + pos (suc j)) ⟩
      (negsuc n) + (negsuc j) + pos (suc j)   ≡⟨ +-assoc (negsuc n) (negsuc j) (pos (suc j)) >| eqTr ⟩
      (negsuc n) + ((negsuc j) + pos (suc j)) ≡⟨ ((n⊖n≡0 j >| eqTr) <| \ x → negsuc n + x) ⟩
      negsuc n + (pos 0)                      ≡⟨ +-comm (negsuc n) (pos 0) >| eqTr ⟩
      negsuc n  ∎)

  predℤ-pred : ∀ n i → (predℤ ^ n) (predℤ i) ≡ (predℤ ^ (suc n)) i
  predℤ-pred zero i = refl
  predℤ-pred (suc n) i = begin
    predℤ ((predℤ ^ n) (predℤ i)) ≡⟨ (predℤ-pred n i <| \ x → predℤ x) ⟩
    predℤ ((predℤ ^ (suc n)) i)  ≡⟨⟩
    predℤ (predℤ ((predℤ ^ n) i)) ∎

  lm-arithm : ∀ i j n (p : j + pos (suc n) ≡ i) → j + pos n ≡ predℤ i
  lm-arithm i j n p = begin
    j + pos n                    ≡⟨ (+-assoc j (pos (suc n)) (negsuc 0) >| \ x → sym (eqTr x)) ⟩
    j + pos (suc n) + negsuc 0   ≡⟨ (+-comm (negsuc 0) (j + pos (suc n)) >| \ x → sym (eqTr x)) ⟩
    negsuc 0 + (j + pos (suc n)) ≡⟨ (p <| \ x → predℤ x) ⟩
    predℤ i ∎

  lm-recp : ∀ n i j (p : (j + pos n ≡ i)) → ( ((predℤ ^ n) i) ≡ j)
  lm-recp 0 i j p = sym (trans (sym (eqTr (+-identityʳ j))) p)
  lm-recp (suc n) i j p = begin
    predℤ ((predℤ ^ n) i) ≡⟨ sym (predℤ-pred n i) ⟩
    (predℤ ^ n) (predℤ i) ≡⟨ lm-recp n (predℤ i) j (lm-arithm i j n p) ⟩
    j ∎ 

  ineq-cmp-onpred : {i j : ℤ} (p : j ≤ i) → Σ[ n ∈ ℕ ] ( ((predℤ ^ n) i) ≡ j) 
  ineq-cmp-onpred {i} {j} p = (ineq-cmp p .fst) , (lm-recp _ _ _ (ineq-cmp p .snd))

  ineq-cmp-type-unicity : ∀ i j (a b : Σ[ n ∈ ℕ ] (j + pos n ≡ i)) → a .fst ≡ b .fst --Annoying but easy arithmetic...x
  ineq-cmp-type-unicity i j a b = begin
    a .fst ≡⟨ {!a .snd!} ⟩
    {!!}   ≡⟨ {!!} ⟩
    b .fst ∎
    where
      lm : j + pos (fst a) ≡ j + pos (fst b)
      lm = a .snd ∙ sym (b .snd)

      lm' : ∀ j → - j + j ≡ pos 0
      lm' j = {!j + - j!}

      lm2 :  pos (fst a) ≡  pos (fst b)
      lm2 = begin
        pos (fst a)             ≡⟨ {!!} ⟩
        (- j + j) + pos (fst a) ≡⟨ +-assoc (- j) j _ >| eqTr ⟩
        - j + (j + pos (fst a)) ≡⟨ (lm <| \ x → - j + x) ⟩
        - j + (j + pos (fst b)) ≡⟨ (+-assoc (- j) j _ >| \ x → sym (eqTr x)) ⟩
        - j + j + pos (fst b)   ≡⟨ {!!} ⟩
        pos (fst b) ∎ 

      pos-inj : ∀ a b (e :  pos a ≡ pos b) → a ≡ b
      pos-inj a b e = pathJ {!!} refl (pos b) e

  ineq-cmp-type-Prop : ∀ k l → isProp (Σ[ n ∈ ℕ ] (l + pos n ≡ k)) --IC.IntCategoryM.Lemmas.isSet-ℤ
  ineq-cmp-type-Prop k l x y j = (ineq-cmp-type-unicity k l x y j) , {!!}

  lemmaInf : ∀ i → predℤ i ≤ i
  lemmaInf (pos 0) = -≤+
  lemmaInf (pos (suc n)) = +≤+ (Np.≤″⇒≤ (less-than-or-equal {k = 1} (Np.+-comm n 1)))
  lemmaInf (negsuc n) = -≤- (Np.≤″⇒≤ ((less-than-or-equal {k = 1} (Np.+-comm n 1))))

  ineq-cmp-onInf : ∀ k → ineq-cmp-onpred (lemmaInf k) .fst ≡ (suc 0)
  ineq-cmp-onInf k = ineq-cmp-type-unicity k (predℤ k) (ineq-cmp (lemmaInf k)) ((suc 0) , (begin
    predℤ k + pos 1 ≡⟨ +-comm (predℤ k) (pos 1) >| eqTr ⟩
    pos 1 + predℤ k ≡⟨ (+-assoc (pos 1) (negsuc 0) k >| \ x → sym (eqTr x)) ⟩
    pos 0 + k       ≡⟨ +-identityˡ k >| eqTr ⟩
    k ∎))
  


--   -- Maybe use +-injective; but we have a cubical equality so...
--   postulate pos-inj : ∀ j n m (e : j + pos n ≡ j + pos m) → n ≡ m

--   ineq-cmp-unicity : {i j : ℤ} (p q : j ≤ i) → (ineq-cmp p) .fst ≡ (ineq-cmp q) .fst
--   ineq-cmp-unicity {i} {j} p q =
--     let n = (ineq-cmp p) .fst
--         pn = (ineq-cmp p) .snd
--         k = (ineq-cmp q) .fst
--         pk = (ineq-cmp q) .snd
--         lm1 : j + (pos n) ≡ j + (pos k)
--         lm1 = begin
--           j + pos n ≡⟨ pn ⟩
--           i ≡⟨ sym pk ⟩
--           j + pos k ∎
          
--         lm : (pos n) ≡ (pos k)
--         lm = pos-inj j n k lm1 <| \ x → pos x
          
--     in begin
--          n ≡⟨ pos-inj (pos 0) n k lm ⟩
--          k ∎
-- -- -- 
-- --   predℤ-n-+ : (n : ℕ) (i : ℤ) → ((predℤ ^ (suc n)) i) ≡ (i + (negsuc n))
-- --   predℤ-n-+ zero i = sym (eqTr (+-comm i (negsuc 0)))
-- --   predℤ-n-+ (suc n) i = begin
-- --     predℤ (((predℤ ^ (suc n)) i) ) ≡⟨ (predℤ-n-+ n i <| λ x → predℤ x) ⟩
-- --     predℤ (i + (negsuc n))         ≡⟨ (+-comm (negsuc 0) (i + (negsuc n))) >| eqTr ⟩
-- --     i + negsuc n + negsuc 0        ≡⟨ +-assoc i (negsuc n) (negsuc 0) >| eqTr ⟩
-- --     i + (negsuc n + negsuc 0)      ≡⟨ ((+-right-identity n >| eqTr) <| λ x → i + negsuc (suc x)) ⟩
-- --     i + negsuc (suc n) ∎

-- --   predℤ-^-pos : (n : ℕ) (i : ℕ) → (predℤ ^ n) (pos (suc i)) ≡ sucℤ ((predℤ ^ n) (pos i))
-- --   predℤ-^-pos zero i    = refl
-- --   predℤ-^-pos (suc n) i = begin
-- --     predℤ ((predℤ ^ n) (pos (suc i)))    ≡⟨ (predℤ-^-pos n i <| λ x → predℤ x ) ⟩
-- --     predℤ (sucℤ ((predℤ ^ n) (pos i)))   ≡⟨ predSuc _ ⟩
-- --     ((predℤ ^ n) (pos i))                ≡⟨ sucPred _ >| sym ⟩
-- --     sucℤ (predℤ ((predℤ ^ n) (pos i))) ∎

-- --   predℤ-pos : (n : ℕ) → ((predℤ ^ n) (pos n)) ≡ (pos 0)
-- --   predℤ-pos zero = refl
-- --   predℤ-pos (suc n) = begin
-- --     predℤ ((predℤ ^ n) (pos (suc n)))  ≡⟨ (predℤ-^-pos n n <| \ x → predℤ x) ⟩
-- --     predℤ (sucℤ ((predℤ ^ n) (pos n))) ≡⟨ predSuc ((predℤ ^ n) (pos n)) ⟩
-- --     (predℤ ^ n) (pos n)                ≡⟨ predℤ-pos n ⟩
-- --     pos 0 ∎


-- --   -- Do induction on n not m and see how it's nice that things compute...
  
-- --   predℤ-^-+ : (m n : ℕ) (i : ℤ) → ((predℤ ^ (m +ℕ n)) i) ≡ (predℤ ^ m) ((predℤ ^ n) i)
-- --   predℤ-^-+ zero n i = refl
-- --   predℤ-^-+ (suc m) n i = predℤ-^-+ m n i <| \ x → predℤ x

-- --   ineq-cmp-ℕ :{i j : ℕ} (p : j ℕ≤ i) → Σ[ n ∈ ℕ ] ( ((predℤ ^ n) (pos i)) ≡ (pos j) )
-- --   ineq-cmp-ℕ {zero} (z≤n) = zero , refl
-- --   ineq-cmp-ℕ {suc n} (z≤n) = suc n , (begin
-- --                                      (predℤ ^ (suc n)) (pos (suc n)) ≡⟨ predℤ-n-+ n (pos (suc n)) ⟩
-- --                                      pos (suc n) + negsuc n          ≡⟨ eqTr (+-inverseˡ (pos (suc n))) ⟩
-- --                                      pos 0 ∎)
  
-- --   ineq-cmp-ℕ {suc n} {suc m} (s≤s p) =
-- --     let a = ineq-cmp-ℕ p .fst
-- --         pa = ineq-cmp-ℕ p .snd
-- --     in a , (begin
-- --            (predℤ ^ a) (pos (suc n))  ≡⟨ predℤ-^-pos a n ⟩
-- --            sucℤ ((predℤ ^ a) (pos n)) ≡⟨ (pa <| λ x → sucℤ x) ⟩
-- --            sucℤ (pos m)               ≡⟨⟩
-- --            pos (suc m) ∎)

-- --   predℤ-pred : ∀ n i → (predℤ ^ n) (predℤ i) ≡ (predℤ ^ (suc n)) i
-- --   predℤ-pred zero i = refl
-- --   predℤ-pred (suc n) i = begin
-- --     predℤ ((predℤ ^ n) (predℤ i)) ≡⟨ (predℤ-pred n i <| \ x → predℤ x) ⟩
-- --     predℤ ((predℤ ^ (suc n)) i)  ≡⟨⟩
-- --     predℤ (predℤ ((predℤ ^ n) i)) ∎  
  
-- --   ineq-cmp-ℕ2 :{i j : ℕ} (p : j ℕ≤ i) → Σ[ n ∈ ℕ ] ( ((predℤ ^ n) (negsuc j)) ≡ (negsuc i) )
  
-- --   ineq-cmp-ℕ2 {zero} (z≤n) = zero , refl
-- --   ineq-cmp-ℕ2 {suc n} (z≤n) = suc n , (begin
-- --                                       ((predℤ ^ (suc n)) (negsuc 0)) ≡⟨ predℤ-n-+ n (negsuc 0) ⟩
-- --                                       negsuc (suc n) ∎)
                                     
-- --   ineq-cmp-ℕ2 {suc n} {suc m} (s≤s p) =
-- --     let a = ineq-cmp-ℕ2 p .fst
-- --         pa = ineq-cmp-ℕ2 p .snd
-- --     in  a , (begin
-- --             (predℤ ^ a) (negsuc (suc m))               ≡⟨ predℤ-pred a (negsuc m) ⟩
-- --             predℤ ((predℤ ^  a) (negsuc m))            ≡⟨ (pa <| \ x → predℤ x) ⟩
-- --             negsuc (suc n) ∎)
  
-- --   --- cmp for 'completion'
-- --   ineq-cmp : {i j : ℤ} (p : j ≤ i) → Σ[ n ∈ ℕ ] ( ((predℤ ^ n) i) ≡ j)   
-- --   ineq-cmp {pos n} {negsuc m} -≤+ = (suc m) +ℕ n , (begin
-- --                                              (predℤ ^ ((suc m) +ℕ n)) (pos n)        ≡⟨ predℤ-^-+ (suc m) n (pos n) ⟩
-- --                                              (predℤ ^ (suc m)) ((predℤ ^ n) (pos n)) ≡⟨ (predℤ-pos n <| λ x → (predℤ ^ (suc m)) x) ⟩
-- --                                              (predℤ ^ (suc m)) (pos 0)               ≡⟨  predℤ-n-+ m (pos 0) ⟩
-- --                                              negsuc m ∎ )
                                                    
-- --   ineq-cmp {negsuc n} {negsuc m} (-≤- n≤m) = ineq-cmp-ℕ2 n≤m
-- --   ineq-cmp {pos n} {pos m} (+≤+ m≤n) = ineq-cmp-ℕ m≤n

-- --   ineq-cmp-ℕ-refl : (i : ℕ) → ineq-cmp-ℕ {i = i} {j = i} Np.≤-refl .fst ≡ zero
-- --   ineq-cmp-ℕ-refl 0 = refl
-- --   ineq-cmp-ℕ-refl (suc n) = {!!}

-- --   ineq-cmp-refl1 : (i : ℤ) → ineq-cmp {i = i} {j = i} ≤-refl .fst ≡ zero
-- --   ineq-cmp-refl1 (pos 0) = refl
-- --   ineq-cmp-refl1 (negsuc 0) = refl
-- --   ineq-cmp-refl1 (pos (suc n)) = {!!}
-- --   ineq-cmp-refl1 (negsuc (suc n)) = {!!}

-- --   lemmaInf : ∀ i → predℤ i ≤ i
-- --   lemmaInf (pos 0) = -≤+
-- --   lemmaInf (pos (suc n)) = +≤+ (Np.≤″⇒≤ (less-than-or-equal {k = 1} (Np.+-comm n 1)))
-- --   lemmaInf (negsuc n) = -≤- (Np.≤″⇒≤ ((less-than-or-equal {k = 1} (Np.+-comm n 1))))
