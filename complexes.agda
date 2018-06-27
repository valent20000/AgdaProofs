{-# OPTIONS --cubical #-}
module complexes where

  open import Cubical
  open import Agda.Builtin.Nat
  open import Agda.Primitive --lsuc etc...
  
  open import Cubical.PathPrelude
  open import Cubical.FromStdLib
  open import Cubical.Lemmas
  open import Cubical.Examples.Int
  open import Cat.Category

  ------- We first prove (ℤ, 0) ≡ (ℤ, i) for every i ∈ ℤ

  ℤ = Int -- alias

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

  transpOfTrans : {A : Set} {a : A} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (transp (λ j → (trans p q) j) a) ≡ (transp (λ j → q j) (transp (λ j → p j) a))
  transpOfTrans {A} {a} = pathJ _ (pathJ _ --Par induction sur p et q.
    (begin
      transp (λ j → trans (λ i → A) (λ i → A) j) a ≡⟨ (trans-id refl) <| (cong (λ x → transp (λ j → x j) a)) ⟩
      transp (λ j → A) a                           ≡⟨ (transp-refl a) ⟩ 
      a                                            ≡⟨ sym (transp-refl a) ⟩
      (transp (λ j → refl j) a)                    ≡⟨ sym (transp-refl (transp (λ j → refl j) a)) ⟩
      (transp (λ j → refl j) (transp (λ j → refl {x = A} j) a)) ∎))


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
    transp (λ j → trans (nPathℤ n) sucPathℤ j) (pos 0)              ≡⟨ transpOfTrans Int (nPathℤ n) Int (sucPathℤ) ⟩
    transp (λ j → sucPathℤ j) (transp (λ j → (nPathℤ n) j) (pos 0)) ≡⟨ (whoZeroN {n}) <| cong (λ x → transp (λ j → sucPathℤ j) x) ⟩
    transp (λ j → sucPathℤ j) (pos n)                               ≡⟨ (LemmaT n) <| cong (λ x → pos (suc x)) ⟩
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
      (sym (symOnTrans ℤ sucPathℤ ℤ (nPathℤ n))) ⟩

    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (trans sucPathℤ (nPathℤ n))) j) (pos 0)) ≡⟨⟩
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → trans sucPathℤ (nPathℤ n) (~ j)) (pos 0)) ≡⟨
      cong (λ x → transp (λ j → sucPathℤ (~ j)) x) (LemmaNeg {n = n}) ⟩
    transp (λ j → sucPathℤ (~ j)) (negsuc n) ≡⟨ cong (λ x → negsuc (suc x)) (LemmaT n) ⟩
    negsuc (suc n)∎
      

  whoZero : {i : ℤ} → transp (λ j → (iPathℤ i)j) (pos 0) ≡ i
  whoZero {pos n} = whoZeroN
  whoZero {(negsuc n)} = LemmaNeg


  -- Theorem --
  --ℤ,0 : Σ Set (λ x → x)
  --ℤ,0 = (ℤ , (pos 0))

  --allℤsame : {i : ℤ} →  ℤ,0 ≡ (ℤ , i)
  --allℤsame {i} = λ j → (iPathℤ i)j , toPathP {A = (λ j → (iPathℤ i)j)} (whoZero {i = i}) j

  Sing : (i : ℤ) → Set
  Sing i = (Σ ℤ (λ y → y ≡ i))

  whoZeroS : {i : ℤ} → (Sing (pos 0)) ≡ (Sing i)
  whoZeroS {i} = λ j → {!!}

  ℤ,0 : Set
  ℤ,0 = ℤ × (Sing (pos 0))

  allℤsame : {i : ℤ} →  ℤ,0 ≡ (ℤ × (Sing i))
  allℤsame {i} = λ j → (iPathℤ i)j × whoZeroS{i = i} j


  ------------------------------- End of Section

  ----------------------------------------------------------------------


  --- We now define what a chain complex is.
  {-- In idea :

    Convention: (chain i) is the ith object and the ith Arrow.

    chain : {c : Category} → ℤ → (c.Object, c.Arrow)
    
    With the constraint :
      - hasZero :
        ∃ 0 ∈ c.ArrowObject | (IsInitial 0) /\ (IsTerminal 0)

      ie we want a pointed Category

      - isChain:
        ∀ i ∈ ℤ; (chain i) ∙ (chain (i+1)) = 0 (arrow)   
  --}

  record ZeroCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where

    field {{c}} : (Category ℓa ℓb)
    open Category c public

    field
      hasZero : Σ Object (λ zer → (IsInitial zer × IsTerminal zer))

    cZero = (fst hasZero)

    --Gives the zero function associated to A and B
    zeroFunc : (A : Object) (C : Object) → (Arrow A C)  
    zeroFunc = λ A C → (fst ((fst (snd hasZero)) {X = C})) <<< (fst (snd (snd hasZero) {X = A}))
    

  record ChainComplex (ℓa ℓb : Level) {cat : ZeroCategory ℓa ℓb} : Set (lsuc (ℓa ⊔ ℓb)) where

    open ZeroCategory cat public
    
    field
      thisO : ℤ → Object
      thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
      
      isChain : (i : ℤ) → (thisA (predℤ i)) <<< (thisA i) ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i)))


  {--
    
    Now we are going to define a certain type of chain complexes;

    .. ← 0 ← .. ← 0 ← A ← 0 ← .. ← 0 ← ..

    With A in the i ∈ ℤ position.

  --}
  
  -- We now assume we have a ZeroCategory
  
  module _ (ℓa ℓb : Level) (cat : ZeroCategory ℓa ℓb) where

    open ZeroCategory cat
    
    module zChain (A : Object) (i : ℤ) where

      thisO : ℤ,0 → Object
      thisO ((pos 0) , _) = A
      thisO (n , _) = cZero

      thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
      thisA (pos 0) = (zeroFunc A cZero)
      thisA (pos 1) = (zeroFunc cZero A)
      thisA (pos (suc (suc n))) = (zeroFunc cZero cZero)
      thisA (negsuc n) = (zeroFunc cZero cZero)
      
       -- For now we admit that the chain in zero is a chain.
       
      postulate isChain0Post : (i : ℤ) → (thisA (predℤ i)) <<< (thisA i) ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i)))
      
      zeroChain : (ChainComplex ℓa ℓb {cat = cat})
      zeroChain = record {thisA = thisA; thisO = thisO; isChain = isChain0Post}

    module iChain (A : Object) (i : ℤ) where

      -- Here we create the i-chain based on the 0-chain.

      open zChain A

      --iPathO : (ℤ → Object) ≡ (ℤ → Object)
      --iPathO = {!!}

      --thisOi = transp iPathO thisO
      
      --thisAi = transp (iPathℤ i) thisA
      
      --isChain : (p : ℤ) → (thisAi p) <<< (thisAi (sucℤ p)) ≡ zeroFunc (thisOi (sucℤ p)) (thisOi (predℤ p))
      --isChain = ? --We transport the proof

      -- TH
      -- baseChain : (ChainComplex ℓa ℓb {cat = cat})
      -- baseChain = record {thisA = thisAi; thisO = thisOi; isChain = isChain}
