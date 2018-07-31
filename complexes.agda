{-# OPTIONS --cubical #-}
module complexes where

  -- open import Cubical
  --open import Agda.Builtin.Nat
  open import Agda.Primitive --lsuc etc...
  open import Agda.Builtin.Equality renaming (_≡_ to _≡b_) renaming (refl to reflb)

  open import Data.Integer.Base renaming (suc to sucℤ) renaming (pred to predℤ) hiding (_⊔_)
  open import Data.Integer.Properties
  open import Data.Nat.Base hiding (_⊔_) hiding (_+_) hiding (_^_)
  open import Agda.Builtin.Int

  --open import Cubical.FromStdLib
  --open import Cubical.Examples.Int
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cat.Category
  open import Cat.Prelude --hiding (_×_) --using

  open import Numbers
  open import Utils

  --- We define what a chain complex is.
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

    module iChain (A : Object) (i : ℤ) where

      -- Here we create the i-chain based on the 0-chain.

      open zChain A

      path1 : (ℤ → Object) ≡ (ℤ → Object)
      path1 = cong (λ X → (X → Object)) (iPathℤ i)
 
      thisOi = transp (λ j → path1 j) thisO
  
      thisAi :  (p : ℤ) → Arrow (thisOi p) (thisOi (predℤ p))
      thisAi p = (zeroFunc (thisOi p) (thisOi (predℤ p)))

      LmCheck1 : (thisOi i) ≡ A
      LmCheck1 = begin
        thisOi i ≡⟨ ElimCompL 1 (thisO (primComp (λ j → iPathℤ i (~ j)) i0 (λ i₁ → empty) i)) ⟩
        (thisO (primComp (λ j → iPathℤ i (~ j)) i0 (λ i₁ → empty) i)) ≡⟨ sym (LmExchgPath _ _ _ (whoZero {i = i})) <| (λ e → thisO e) ⟩
        thisO (pos 0) ≡⟨⟩
        A ∎


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

          ≡⟨ (let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} ; C = cong (λ x → predℤ x) A ; Q : PathP _ _ _ ; Q = trans B C
              in Σ≡ refl λ j → ( thisO (Q (~ j))) , (zeroFunc (thisO (A (~ j))) (thisO (Q (~ j)))) <<< (zeroFunc (thisO v) (thisO (A (~ j))))) ⟩


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

      LemmaProj1' : (p : ℤ) → cong-d fst (isChainG p)
                            ≡ sym
                              (trans (LemmaTrans p)
                              (trans refl
                              (trans refl
                              (trans refl
                              (trans (sym (LemmaTrans p))
                                     refl)))))
      LemmaProj1' p = refl

      -- The proofs we did are based on the umbrella principle (Things like P M P^-1 in linear algebra); So of course the two first paths are equal to refl.
      LemmaProj1 : (p : ℤ) → cong-d fst (isChainG p) ≡ refl
      LemmaProj1 p = begin
        sym
                              (trans (LemmaTrans p)
                              (trans refl
                              (trans refl
                              (trans refl
                              (trans (sym (LemmaTrans p))
                                     refl))))) ≡⟨ LemmaIt 3 (λ x → trans refl x) (trans-id-l (trans (sym (LemmaTrans p)) refl)) <| (λ e → sym(trans (LemmaTrans p) e) ) ⟩
        sym(trans (LemmaTrans p) (trans (sym (LemmaTrans p)) refl)) ≡⟨ trans-id (sym(LemmaTrans p)) <| (λ x → sym(trans (LemmaTrans p) x)) ⟩
        sym(trans (LemmaTrans p) (sym (LemmaTrans p))) ≡⟨ LmTransSym _ (LemmaTrans p) <| (λ x → sym x) ⟩
        refl ∎


      LemmaProj2' : (p : ℤ) → cong-d (\ x → x .snd .fst) (isChainG p)
                            ≡ sym (trans (LemmaTrans (predℤ (predℤ p)))
                                  (trans (let A = LemmaPredTransp {i = i} {p = p}
                                              B = LemmaPredTransp {i = i} {p = predℤ p}
                                          in -- not definitionally the same as "cong thisO (trans B (cong predℤ A))"
                                             trans (cong thisO B) (cong (\ i → thisO (predℤ i)) A)
                                          )
                                  (trans refl
                                  (trans (let A = LemmaPredTransp {i = i} {p = p}
                                              B = LemmaPredTransp {i = i} {p = predℤ p}
                                           in sym (cong thisO (trans B (cong predℤ A))))
                                  (trans (sym (LemmaTrans (predℤ (predℤ p))))
                                    refl)))))
      LemmaProj2' p = refl

      --LemmaCongTrans : {A B : Set} {x : A} (f : A → B) (y : A) (a : x ≡ y) (z : A) (b : y ≡ z) → cong f (trans a b) ≡ trans (cong f a) (cong f b)
      --LemmaCongTrans f = pathJ _ (pathJ _ (begin
        --{!!}))

      LemmaInLine' : (p : ℤ) → let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} in (sym (cong thisO (trans B (cong predℤ A)))) ≡ (trans (sym (cong (\ i → thisO (predℤ i)) A)) (sym (cong thisO B)) )

      LemmaInLine' p = begin
        let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} ; cb = (cong thisO B) ; ca = (cong (\ i → thisO (predℤ i)) A) in
        
        (sym (cong thisO (trans B (cong predℤ A)))) ≡⟨⟩
        sym (cong thisO (trans B (cong predℤ A))) ≡⟨ sym (trans-cong thisO B _ (cong predℤ A)) <| (λ x → sym x) ⟩
        sym (trans cb (cong thisO (cong predℤ A))) ≡⟨ (LmCongCong thisO predℤ _ A) <| (λ x → sym(trans (cong thisO B) x) ) ⟩
        sym (trans cb ca) ≡⟨ (symOnTransL _ cb _ ca) ⟩
        (trans (sym ca) (sym cb))∎


      LemmaInLine : (p : ℤ) → let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} in trans (trans (cong thisO B) (cong (\ i → thisO (predℤ i)) A)) (sym (cong thisO (trans B (cong predℤ A)))) ≡ refl


      --Proof worked and then agda couldn't parse it anymore...
      LemmaInLine p = begin
        let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} ; cb = (cong thisO B) ; ca = (cong (\ i → thisO (predℤ i)) A) in
        trans (trans cb ca) (sym (cong thisO (trans B (cong predℤ A)))) ≡⟨ LemmaInLine' p <| (λ X → trans (trans cb ca) X)  ⟩
        trans (trans cb ca) (trans (sym ca) (sym cb)) ≡⟨  trans-assoc {p = (trans cb ca)} {q = (sym ca)} {r = (sym cb)} ⟩
        trans (trans (trans cb ca) (sym ca)) (sym cb) ≡⟨  sym( trans-assoc {p = cb} {q = ca} {r = (sym ca)}) <| (λ x → trans x (sym cb))  ⟩
        trans (trans cb (trans ca (sym ca))) (sym cb) ≡⟨ LmTransSym _ ca <| (λ x → trans (trans cb x) (sym cb)) ⟩
        trans (trans cb refl) (sym cb) ≡⟨ trans-id cb <| (λ x → trans x (sym cb)) ⟩
        trans cb (sym cb) ≡⟨ LmTransSym _ cb ⟩
        refl ∎
        
      LemmaProj2 : (p : ℤ) → cong-d (λ a → fst (snd a)) (isChainG p) ≡ refl
      LemmaProj2 p = begin
        (let A = LemmaPredTransp {i = i} {p = p} ; B = LemmaPredTransp {i = i} {p = predℤ p} in
        let c1 = λ X → sym (trans (LemmaTrans (predℤ (predℤ p)))
                                  (trans (trans (cong thisO B) (cong (\ i → thisO (predℤ i)) A))
                                  X)) ; e1 =
                                  (trans (sym (cong thisO (trans B (cong predℤ A))))
                                  (trans (sym (LemmaTrans (predℤ (predℤ p))))
                                    refl)) in c1 (trans refl e1) ≡⟨ (trans-id-l e1) <| c1 ⟩
                                    
        let e2 = λ (X : thisO (transp (λ j → sym (iPathℤ i) j) (predℤ (predℤ p))) ≡ thisOi (predℤ (predℤ p))) → (trans (sym (cong thisO (trans B (cong predℤ A)))) X) in
        c1 (e2 (trans (sym (LemmaTrans (predℤ (predℤ p))))
                                    refl)) ≡⟨ trans-id (sym (LemmaTrans (predℤ (predℤ p)))) <| (λ X → c1 (e2 X)) ⟩ 
                                    
       let a = (trans (cong thisO B) (cong (\ i → thisO (predℤ i)) A)) ; b = (sym (cong thisO (trans B (cong predℤ A)))) ; c = (sym (LemmaTrans (predℤ (predℤ p)))) in
       sym (trans (LemmaTrans (predℤ (predℤ p))) (trans a (trans b c)) ) ≡⟨ trans-assoc {p = a} {q = b} {r = c} <| (λ X → sym (trans (LemmaTrans (predℤ (predℤ p))) X) ) ⟩
                                          
        sym (trans (LemmaTrans (predℤ (predℤ p)))
                                  (trans (trans (trans (cong thisO B) (cong (\ i → thisO (predℤ i)) A))
                                         (sym (cong thisO (trans B (cong predℤ A)))))
                                          (sym (LemmaTrans (predℤ (predℤ p)))) )) ≡⟨ (LemmaInLine p) <| (λ X → sym (trans (LemmaTrans (predℤ (predℤ p))) (trans X (sym (LemmaTrans (predℤ (predℤ p)))) )))  ⟩
                                          
        sym (trans (LemmaTrans (predℤ (predℤ p)))
                   (trans refl (sym (LemmaTrans (predℤ (predℤ p)))) )) ≡⟨ trans-id-l (sym (LemmaTrans (predℤ (predℤ p)))) <| (λ x → sym (trans (LemmaTrans (predℤ (predℤ p))) x)) ⟩
                   
        sym ( trans (LemmaTrans (predℤ (predℤ p))) (sym (LemmaTrans (predℤ (predℤ p)))) ) ≡⟨  LmTransSym _ (LemmaTrans (predℤ(predℤ p))) <| (λ x → sym x) ⟩
        refl ∎)

      isChain : (p : ℤ) → (thisAi (predℤ p)) <<< (thisAi p) ≡ zeroFunc (thisOi p) (thisOi (predℤ (predℤ p)))
      isChain p = transp (\ j → PathP (\ i → Arrow (LemmaProj1 p j i) (LemmaProj2 p j i)) lhs rhs) (cong-d (λ a → snd (snd a)) (isChainG p))
         where
           lhs = (thisAi (predℤ p)) <<< (thisAi p)
           rhs = zeroFunc (thisOi p) (thisOi (predℤ (predℤ p)))
           
      -- Main theorem.
      
      baseChain : (ChainComplex ℓa ℓb {cat = cat})
      baseChain = record {thisA = thisAi; thisO = thisOi; isChain = isChain}
