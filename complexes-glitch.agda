{-# OPTIONS --cubical #-}
module complexes where

  -- open import Cubical
  --open import Agda.Builtin.Nat
  open import Agda.Primitive --lsuc etc...
  open import Agda.Builtin.Equality renaming (_≡_ to _≡b_) renaming (refl to reflb)

  open import Data.Integer.Base renaming (suc to sucℤ) renaming (pred to predℤ) hiding (_⊔_)
  open import Data.Integer.Properties
  open import Data.Nat.Base hiding (_⊔_) hiding (_+_)
  open import Agda.Builtin.Int

  --open import Cubical.FromStdLib
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using
  ------- We first prove (ℤ, 0) ≡ (ℤ, i) for every i ∈ ℤ

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
    transp (λ j → trans (nPathℤ n) sucPathℤ j) (pos 0)              ≡⟨ transpOfTrans ℤ (nPathℤ n) ℤ (sucPathℤ) ⟩
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

  eqTr : {A : Set} {a b : A} (p : a ≡b b) → a ≡ b
  eqTr reflb = ?

  whoIsWho : {i p : ℤ} → transp (λ j → (iPathℤ i)j) p ≡ (i + p)
  whoIsWho {i} {(pos 0)} = trans whoZero {!(+-identityʳ i)!} 
  whoIsWho {i} {(pos (suc n))} = {!!}
  whoIsWho {i} {(negsuc 0)} = {!!}
  whoIsWho {i} {(negsuc (suc n))} = {!!}

  -- Par induction N puis Z ?
  LemmaPredTransp : {i p : ℤ} → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
  LemmaPredTransp {i} {p} = {!(predℤ (transp (λ j → (sym (iPathℤ i)) j) p))!}

  --primComp (λ j → iPathℤ i (~ j)) i0 (λ i₁ → empty) (predℤ p)
  --predℤ (primComp (λ j → iPathℤ i (~ j)) i0 (λ i₁ → empty) p)

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
      hasZero : Σ Object (λ zer → (IsInitial zer × IsTerminal zer)) -- 

    cZero = (fst hasZero)

    -- "Shortcuts" to make proofs clearer.
    proofTerm : {X : Object} → (y : Arrow X (fst hasZero)) → fst (snd (snd hasZero)) ≡ y
    proofTerm {X} = (snd ((snd (snd hasZero)) {X = X}))


    proofInit : {X : Object} → (y : Arrow (fst hasZero) X) → fst (fst (snd hasZero)) ≡ y
    proofInit {X} = (snd ((fst (snd hasZero)) {X = X}))


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
    
    module zChain (A : Object)  where

      thisO : ℤ → Object
      thisO (pos 0) = A
      thisO n = cZero

      {--
      thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
      thisA (pos 0) = (zeroFunc A cZero)
      thisA (pos 1) = (zeroFunc cZero A)
      thisA (pos (suc (suc n))) = (zeroFunc cZero cZero)
      thisA (negsuc n) = (zeroFunc cZero cZero)
      --}

      thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
      thisA i = (zeroFunc (thisO i) (thisO (predℤ i)))
      
      -- We want to proove now that the zero chain is indeed a chain.

      -- Those proofs are really trivial. We just say that both members are equal to a canonical element of their type.
      -- (In maths we would say that they are 'equal' because there is unicty up to isomorphism)
      -- We just have to look at every case. But it's simple because here we are at 0 who as a special place in ℤ
      -- We don't have to consider j = i, j = i + 2, j < i etc... Wich would make things extremely complicated. 

      --First we prove the result for 0 → 0
      -- Note that using proofTerm or proofInit both works...
      
      ProofZ : (A : Arrow cZero cZero) → A ≡ zeroFunc cZero cZero
      ProofZ A = begin
        A ≡⟨ sym (proofTerm A) ⟩
        fst (snd (snd hasZero)) ≡⟨ proofTerm (zeroFunc cZero cZero) ⟩
        zeroFunc cZero cZero ∎
       
      isChain0Post : (i : ℤ) → (thisA (predℤ i)) <<< (thisA i) ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i)))
      
      isChain0Post (pos 0) = begin
        thisA (negsuc zero) <<< thisA (pos zero) ≡⟨ sym (proofTerm ((thisA (predℤ (pos 0))) <<< (thisA (pos 0)))) ⟩
        fst (snd (snd hasZero)) ≡⟨  proofTerm (zeroFunc A cZero)  ⟩
        zeroFunc A cZero ∎
        
      isChain0Post (pos 2) = begin
         thisA (pos 1) <<< thisA (pos 2) ≡⟨ sym (proofInit (thisA (pos 1) <<< thisA (pos 2))) ⟩
         fst (fst (snd hasZero)) ≡⟨ proofInit (zeroFunc cZero A) ⟩
         zeroFunc cZero A ∎

      -- Chains between zeros.      
      isChain0Post (pos 1) = ProofZ (thisA (pos 0) <<< thisA (pos 1))
      isChain0Post (pos (suc (suc (suc n)))) = ProofZ (thisA (pos (suc (suc n))) <<< thisA (pos (suc (suc (suc n)))))
      isChain0Post (negsuc n) = ProofZ (thisA (negsuc (suc n)) <<< thisA (negsuc n))


      -- THEOREM : The zeroChain is a Chain Complex.

      zeroChain : (ChainComplex ℓa ℓb {cat = cat})
      zeroChain = record {thisA = thisA; thisO = thisO; isChain = isChain0Post}

    module iChain (A : Object) where

      -- Here we create the i-chain based on the 0-chain.

      i = (pos 1)

      open zChain A

      path1 : (ℤ → Object) ≡ (ℤ → Object)
      path1 = cong (λ X → (X → Object)) (iPathℤ i)
 
      thisOi = transp (λ j → path1 j) thisO
  
      thisAi :  (p : ℤ) → Arrow (thisOi p) (thisOi (predℤ p))
      thisAi p = (zeroFunc (thisOi p) (thisOi (predℤ p)))

      --Looking at the normal forms sure is useful sometimes :)
      
      LemmaTrans : (p : ℤ)  → (thisOi p) ≡ thisO (transp (λ j → (sym (iPathℤ i)) j) p)
      LemmaTrans p =  transp-refl ( thisO (primComp (λ j → iPathℤ i (~ j)) i0 (λ i₁ → empty) p))

      

      isChainG : (p : ℤ) → (λ _ → Σ Object (λ a → Σ Object (λ b → (Arrow a b)))) [ ((thisOi p), (thisOi (predℤ (predℤ p))), (thisAi (predℤ p)) <<< (thisAi p) ) ≡ ((thisOi p), (thisOi (predℤ (predℤ p))), zeroFunc (thisOi p) (thisOi (predℤ (predℤ p))) ) ]

      isChainG p = sym (begin
      
        ((thisOi p),
        ((thisOi (predℤ (predℤ p))),
        zeroFunc (thisOi p) (thisOi (predℤ (predℤ p))) ))
        
          ≡⟨ ( let A = (LemmaTrans p) ; B = (LemmaTrans (predℤ (predℤ p))) ; Q : PathP _ _ _ ; Q = λ j →  zeroFunc (A j) (B j) in
          Σ≡ (A) λ j → (B j) , (Q j)) ⟩
          (let v = (transp (λ j → (sym (iPathℤ i)) j) p) in
        
        (thisO v),
        ((thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ (predℤ p)))),
        zeroFunc (thisO v) (thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ (predℤ p)))))

          ≡⟨  (let A = (LemmaPredTransp {i = i}) ; Q : PathP _ _ _ ; Q = λ j →  thisO (A {p = (predℤ p)} j) ; L : PathP _ _ _ ; L = λ j → thisO (predℤ (A {p = p} j)) in Σ≡ refl λ j → ( (trans Q L) j) , (zeroFunc (thisO v) ((trans Q L) j)))  ⟩


        (thisO v),
        (thisO (predℤ (predℤ v))),
        (zeroFunc (thisO v) (thisO (predℤ (predℤ v))))

          ≡⟨ Σ≡ refl (λ j → refl j , (sym (isChain0Post v)) j) ⟩

         (thisO v),
         (thisO (predℤ (predℤ v))),
         (thisA (predℤ v)) <<< (thisA v)

          ≡⟨⟩

         (thisO v),
         (thisO (predℤ (predℤ v))),
         ((zeroFunc (thisO (predℤ v)) (thisO (predℤ (predℤ v)))) <<< (zeroFunc (thisO v) (thisO (predℤ v))))

          ≡⟨ (let A = sym (LemmaTrans p) ;  B = sym (LemmaTrans (predℤ p)) ; C = sym (LemmaTrans (predℤ (predℤ p))) ; Q : PathP _ _ _ ; Q = λ j → (zeroFunc (B j) (C j)) <<< (zeroFunc (A j) (B j)) in Σ≡ refl {!!}) ⟩

{--

(let A = (LemmaPredTransp {i = i}) ; Q : PathP _ _ _ ; Q = λ j →  thisO (A {p = (predℤ p)} j) ; L : PathP _ _ _ ; L = λ j → thisO (predℤ (A {p = p} j)) in Σ≡ refl λ j → ((sym (trans Q L)) j) , zeroFunc (((sym Q) j)) (((sym (trans Q L)) j))  <<< zeroFunc (refl j) (((sym Q) j)))

--}

          (thisO v),
          thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ (predℤ p))),
          (zeroFunc (thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ p))) (thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ (predℤ p))) )) <<< (zeroFunc (thisO v) (thisO (transp (λ j → (sym (iPathℤ i)) j) (predℤ p))) )

          ≡⟨ (( (let A = sym (LemmaTrans p) ;  B = sym (LemmaTrans (predℤ p)) ; C = sym (LemmaTrans (predℤ (predℤ p))) ; Q : PathP _ _ _ ; Q = λ j → (zeroFunc (B j) (C j)) <<< (zeroFunc (A j) (B j)) in
          Σ≡ (A) (λ j → (C j) , (Q j))) )) ⟩

         (thisOi p),
         (thisOi (predℤ (predℤ p))),
         (zeroFunc (thisOi (predℤ p)) (thisOi (predℤ (predℤ p)))) <<< (zeroFunc (thisOi p) (thisOi (predℤ p)))

          ≡⟨⟩

        ((thisOi p), (thisOi (predℤ (predℤ p))),  (thisAi (predℤ p)) <<< (thisAi p))∎))


      LemmaProj1 : (p : ℤ) → cong-d fst (isChainG p) ≡ refl
      LemmaProj1 p = {!cong-d fst (isChainG p)!}

      LemmaProj2 : (p : ℤ) → cong-d (λ a → fst (snd a)) (isChainG p) ≡ refl
      LemmaProj2 p = {!!}      

      isChain : (p : ℤ) → (thisAi (predℤ p)) <<< (thisAi p) ≡ zeroFunc (thisOi p) (thisOi (predℤ (predℤ p)))
      isChain p =  let r = cong-d (λ a → snd (snd a)) (isChainG p) ; A = λ j → (Arrow (LemmaProj1 p j) (thisOi (predℤ (predℤ p)))) ; B = λ j → (Arrow (thisOi p) (LemmaProj2 p j)) in
        λ j → {! r!}

      -- Main theorem.
      
      baseChain : (ChainComplex ℓa ℓb {cat = cat})
      baseChain = record {thisA = thisAi; thisO = thisOi; isChain = isChain}
