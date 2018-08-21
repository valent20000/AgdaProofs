{-# OPTIONS --cubical #-}
module complexes2 where

  open import Cubical.FromStdLib hiding (_×_) hiding (_+_)
  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  
  open import Cat.Category
  open import Cat.Prelude

  open import Cat.Category.ZeroCategory

  open import Numbers2
  
  open import Cubical.FromStdLib renaming (_+_ to _+ℕ_)
  open import Data.Integer.Base renaming (_+_ to _+d_) hiding (_⊔_) renaming (suc to sucℤ) renaming (pred to predℤ) renaming (+_ to pos) renaming (-[1+_] to negsuc)
  
  open import Utils

  --- We define what a chain complex is.
  {--
    Convention:
      thisO is the object in position i.
      thisA is the arrow in position i.
    The arrows are like that: ... <- . <- . <- . <- ...
    They go from i to (i - 1)
  --}

  module _ (ℓa ℓb : Level) {cat : ZeroCategory ℓa ℓb} where
    
    record ChainComplex  : Set (ℓa ⊔ ℓb) where

      open ZeroCategory cat
      
      field
        thisO : ℤ → Object
        thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))

        -- zeroFunc gives the zero arrow between two given object.
        isChain : (i : ℤ) → (thisA (predℤ i)) <<< (thisA i) ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i)))

    {--
      
      Now we are going to define a certain type of chain complexes;
      .. ← 0 ← .. ← 0 ← A ← 0 ← .. ← 0 ← ..
      With A in the i ∈ ℤ position.
  
    --}


  -- We now assume we have an ambient ZeroCategory
  
  module _ (ℓa ℓb : Level) (cat : ZeroCategory ℓa ℓb) where

    open ZeroCategory cat

    {-- We first start with the zero chain.
        We can do all the proofs by pattern matching since ℕ is defined as 0 and suc, and ℤ as ℕ + ℕ; zero holds a special place.
    --}
    
    module zChain (A : Object)  where

      thisO : ℤ → Object
      thisO (pos 0) = A
      thisO n = cZero

      {-- Expanded definition of thisA :

        thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
        thisA (pos 0) = (zeroFunc A cZero)
        thisA (pos 1) = (zeroFunc cZero A)
        thisA (pos (suc (suc n))) = (zeroFunc cZero cZero)
        thisA (negsuc n) = (zeroFunc cZero cZero)

      --}

      thisA : (i : ℤ) → Arrow (thisO i) (thisO (predℤ i))
      thisA i = (zeroFunc (thisO i) (thisO (predℤ i)))
      
      -- We want to proove now that the zero chain is indeed a chain.

      {-- Those proofs are really trivial. We just say that both members of the equality are equal to a 'canonical' element of their type.
          We just have to look at every case. But it's simple because here we are at 0 who as a special place in ℤ
          We don't have to consider j = i, j = i + 2, j < i etc... Wich would make things extremely complicated. 
      --}
      
      --First we prove the result for 0 → 0
      -- That is, every two arrows between 0 and 0 are equal (because it's a zero element)
      -- Note that using proofTerm or proofInit (stating that 0 is terminal/initial) both works...
      
      ProofZ : (A : Arrow cZero cZero) → A ≡ zeroFunc cZero cZero
      ProofZ A = begin
        A ≡⟨ sym (proofTerm A) ⟩
        fst (snd (snd hasZero)) ≡⟨ proofTerm (zeroFunc cZero cZero) ⟩
        zeroFunc cZero cZero ∎

      {-- The fundamental idea is that because of the unicty given by the initiality / terminality (there exist a unique element such that ...); we can equate
          everything to a 'canonical' element (the one given by the existence). Thus the proof is really easy.

          We just have to consider the cases where A is involed separatly.
      --}
       
      isChain0 : (i : ℤ) → (thisA (predℤ i)) <<< (thisA i) ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i)))
      
      isChain0 (pos 0) = begin
        thisA (negsuc 0) <<< thisA (pos 0) ≡⟨ sym (proofTerm ((thisA (predℤ (pos 0))) <<< (thisA (pos 0)))) ⟩
        fst (snd (snd hasZero))            ≡⟨  proofTerm (zeroFunc A cZero)  ⟩
        zeroFunc A cZero ∎
        
      isChain0 (pos 2) = begin
         thisA (pos 1) <<< thisA (pos 2) ≡⟨ sym (proofInit (thisA (pos 1) <<< thisA (pos 2))) ⟩
         fst (fst (snd hasZero))         ≡⟨ proofInit (zeroFunc cZero A) ⟩
         zeroFunc cZero A ∎

      -- Chains between zeros.      
      isChain0 (pos 1) = ProofZ (thisA (pos 0) <<< thisA (pos 1))
      isChain0 (pos (suc (suc (suc n)))) = ProofZ (thisA (pos (suc (suc n))) <<< thisA (pos (suc (suc (suc n)))))
      isChain0 (negsuc n) = ProofZ (thisA (negsuc (suc n)) <<< thisA (negsuc n))


      -- THEOREM : The zeroChain is a Chain Complex.

      zeroChain : (ChainComplex ℓa ℓb {cat = cat})
      zeroChain = record {thisA = thisA; thisO = thisO; isChain = isChain0}

    module iChain (A : Object) (i : ℤ) where

      -- Here we create the i-chain based on the 0-chain.

      open zChain A

      +i : ℤ → ℤ
      +i = λ x → transp (λ j → iPathℤ i j) x

      -i : ℤ → ℤ
      -i = λ x → transp (λ j → iPathℤ i (~ j)) x

      path1 : (ℤ → Object) ≡ (ℤ → Object)
      path1 = cong (λ X → (X → Object)) (iPathℤ i)

      CComplex : Σ Set (\ Z → Z → Z) → Set _
      CComplex (Z , predZ) = (Σ (Z → Object) (\ thisO →
         Σ (∀ i → Arrow (thisO i) (thisO (predZ i))) (\ thisA →
           (i : Z) → (thisA (predZ i)) <<< (thisA i)
                   ≡ zeroFunc (thisO i) (thisO (predZ (predZ i))))))


      pathComplex : ChainComplex ℓa ℓb {cat = cat} ≡ ChainComplex ℓa ℓb {cat = cat}
      pathComplex = begin
      
        let T = (Σ (ℤ → Object) (\ thisO →
                  Σ (∀ i → Arrow (thisO i) (thisO (predℤ i))) (\ thisA →
                 (i : ℤ) → (thisA (predℤ i)) <<< (thisA i)
                         ≡ zeroFunc (thisO i) (thisO (predℤ (predℤ i))))))

        in
        let chainToSig : ChainComplex ℓa ℓb {cat = cat} → T
            chainToSig = λ cc → (cc .ChainComplex.thisO) , ((cc .ChainComplex.thisA) , cc .ChainComplex.isChain)

            sigToChain : T → ChainComplex ℓa ℓb {cat = cat}
            sigToChain = λ sig → record { thisO = fst sig ; thisA = fst (snd sig) ; isChain = snd (snd sig) }

            chainToChain : ∀ e → sigToChain (chainToSig ( e )) ≡ e
            chainToChain = λ e → refl
            
            sigTosig : ∀ e → chainToSig( sigToChain( e ) ) ≡ e
            sigTosig = λ e → refl

            recSig :  Σ _ (isEquiv (ChainComplex ℓa ℓb {cat = cat}) T)

            recSig =
              chainToSig ,
              gradLemma chainToSig sigToChain sigTosig chainToChain

        in
        ChainComplex ℓa ℓb {cat = cat}
          ≡⟨ equivToPath recSig ⟩
         T
           ≡⟨ cong CComplex eq ⟩
         T
           ≡⟨ sym (equivToPath recSig) ⟩
         ChainComplex ℓa ℓb {cat = cat} ∎ 
       where
         
         eq : PathP (\ _ → Σ Set (\ Z → Z → Z)) (ℤ , predℤ) (ℤ , predℤ)
         eq = Σ≡ (iPathℤ i) (toPathP (funExt \ x → begin
           transp (\ j → iPathℤ i j) (predℤ (transp (\ j → iPathℤ i (~ j)) x)) ≡⟨ (sym(LemmaPredTransp i x) <| \ e → transp (\ j → iPathℤ i j) e) ⟩
           transp (\ j → iPathℤ i j) (transp (\ j → iPathℤ i (~ j)) (predℤ x)) ≡⟨ transp-iso (\ j → (iPathℤ i) (~ j)) (predℤ x) ⟩
           predℤ x ∎ ))


      -- THEOREM : the i-chain is a Chain Complex.
      baseChain' : ChainComplex ℓa ℓb
      baseChain' = transp (\ i → pathComplex i) zeroChain


      -- We can extract the objects and arrows.
      thisOi : (x : ℤ) → Object
      thisOi = \ x → (baseChain' .ChainComplex.thisO x)

      thisAi : (x : ℤ) → Arrow (ChainComplex.thisO baseChain' x) (ChainComplex.thisO baseChain' (predℤ x))
      thisAi = \ x → (baseChain' .ChainComplex.thisA x)

      -- Verifications; We can check that it gave us what we expected it to be.

      simpl : ∀ x → (thisOi x) ≡ (thisO (-i x))
      simpl x = begin
        baseChain' .ChainComplex.thisO x ≡⟨ ElimCompL 17 (thisO ((empCmp ^ 6) (-i ((empCmp ^ 10) x)))) ⟩
        (thisO ((empCmp ^ 6) (-i ((empCmp ^ 10) x)))) ≡⟨ (ElimCompL 6 ((-i ((empCmp ^ 10) x))) <| \ e → thisO e) ⟩
        thisO (-i ((empCmp ^ 10) x)) ≡⟨ (ElimCompL 10 x <| \ e → thisO ( -i e )) ⟩
        (thisO (-i x)) ∎

      correction :  ∀ z → (thisOi (z + i)) ≡ (thisO z)
      correction z = begin
        thisOi (z + i) ≡⟨ (sym (LemmaIP i z) <| \ e → thisOi e) ⟩
        thisOi (+i z) ≡⟨ simpl (+i z) ⟩
        thisO (-i (+i z)) ≡⟨ (transp-iso (\ j → iPathℤ i j) z <| \ e → thisO e) ⟩ 
        thisO z ∎
        
      correction1 : (thisOi i) ≡ A
      correction1 = begin
        thisOi i ≡⟨ (sym( +-0 i ) <| \ e → thisOi e) ⟩
        thisOi (pos 0 + i) ≡⟨ correction (pos 0) ⟩
        thisO (pos 0) ≡⟨⟩
         A ∎

      correction2 : ∀ n → (thisOi ((pos (suc n)) + i)) ≡ cZero
      correction2 n = begin
        thisOi ((pos (suc n)) + i) ≡⟨ correction (pos (suc n)) ⟩
        thisO (pos (suc n)) ≡⟨⟩
        cZero ∎

      correction3 : ∀ n → (thisOi ((negsuc n) + i)) ≡ cZero
      correction3 n = begin
        thisOi ((negsuc n) + i) ≡⟨ correction (negsuc n) ⟩
        thisO (negsuc n) ≡⟨⟩
        cZero ∎

      {-- This would be really interesting to prove:
          simpl2 : ∀ x → (thisAi x) ≡ (zeroFunc (thisOi x) (thisOi (predℤ x)))

          Unfortunately; we are reaching here one of the limitation of Ctt. (Note that still, the naive proof works though)
          If you check the normal form, it's so huge (unexpectedly for such a little proof!) that it's a good example of things that we cannot work with in practice (or at least with a lot of difficulties).

          Hopefully, people are working on that.
      --}
