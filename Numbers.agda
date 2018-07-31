{-# OPTIONS --cubical #-}
module Numbers where

  open import Agda.Primitive --lsuc etc...
  open import Agda.Builtin.Equality renaming (_≡_ to _≡b_) renaming (refl to reflb)

  open import Data.Integer.Base renaming (suc to sucℤ) renaming (pred to predℤ) hiding (_⊔_)
  open import Data.Integer.Properties
  open import Data.Nat.Base hiding (_⊔_) hiding (_+_)
  open import Agda.Builtin.Int

  open import Cubical.PathPrelude
  open import Cubical.Lemmas

  open import Cat.Prelude --hiding (_×_) --using

  open import Utils

  ------- We first prove (ℤ, 0) ≡ (ℤ, i) for every i ∈ ℤ
  {--

  To do that, we first create the simplest equality between ℤ and ℤ : the +1 path.

  To create an equality between two types, we first have to show that they are isomorphic.
  We can then use univalence to get the desired equality.

  It's obvious that (ℤ, 0) ≃ (ℤ, 1), using the isomorphisms +1 and -1, that is successor and predecessor.
  The proof that they are an isomorphism is also trivial, due to the definition of suc and pred.

  --}

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

  {--

  Here, sucPathℤ will be our +1 path.
  We use equivToPath, that is 'Univalence', that creates a path from the equivalence suc-equiv that we give it.
  
  suc-equiv is an equivalence, that means it's a pair, of a function (the isomorphism) and the proof that this isomorphism is indeed an isomorphism between the two indicated types.

  We thus give sucℤ (+1 isomorphism) as a first parameter.
  To create a proof that it's an isomorphism, we use gradLemma, giving +1, it's reciprocal function, and the proof that they act like an isomorphism.

  --}

  sucPathℤ : ℤ ≡ ℤ
  sucPathℤ = equivToPath suc-equiv
    where
    suc-equiv : Σ _ (isEquiv ℤ ℤ)
    suc-equiv .fst = sucℤ
    suc-equiv .snd = gradLemma sucℤ predℤ sucPred predSuc


  {--
  
  We are now going to define the +i (for i : ℤ) path. They are multiple ways to do this. I chose what I think is the simplest one :
  
  - We first define by induction the +n path by concatenating the +1 path n times.
  - The +i path is the +|i| (in ℕ) path, in a direction depending of the sign of i.

  (An alternative would have been defining a -n path by concatening the symetric of +1 (ie -1); Here we chose to take the symetric of +n directly).

  Note that we won't have to use Univalence anymore; it's done. Now we are working with paths; not isomorphism.

  --}

  -- For natural numbers, the +n path
  
  nPathℤ : (i : ℕ) → (ℤ ≡ ℤ)
  nPathℤ 0 = refl
  nPathℤ (suc n) = trans sucPathℤ (nPathℤ n)

  -- General case; the +i path
  
  iPathℤ : (i : ℤ) → ℤ ≡ ℤ --Path from ℤ to ℤ using +i.
  iPathℤ (pos n) = (nPathℤ n)
  iPathℤ (negsuc n) = sym (nPathℤ (suc n))

  {--

  Here is a special lemma. The computational properties of univalence makes that sometimes, 'parasites' primComp on a trivial path appears in your terms.
  LemmaT is a lemma that simply shows that taking primComp of an integer 3 times over a trivial path gives back that integer.

  To show it, we use transp-refl wich states that concatenating with refl (trivial path) doesn't change anything.

  Note that because this is the naive way, we show it directly. In the non naive way we'll have a more general theorem to get rid of those more easily.

  --}

  LemmaT : (n : ℕ) → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡ n
  LemmaT n = begin
  
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n)) ≡⟨ (transp-refl n)  <| (λ x → primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) x)) ⟩
         
      primComp (λ i → ℕ) i0 (λ i → empty) (primComp (λ i → ℕ) i0 (λ i → empty) n) ≡⟨ (transp-refl n) <| (λ x → (primComp (λ i → ℕ) i0 (λ i → empty) x))⟩
        
      primComp (λ i → ℕ) i0 (λ i → empty) n ≡⟨ (transp-refl n) ⟩
      n ∎


  {--

    Here is a really crucial lemma; It states that the (1 + n) path is the same as the (n + 1) path.
    It's really obvious; the proof is a simple induction

    You can see here that it's postulated; (the proof is commented below). This is because, even if trivial, this theorem can take quite a lot of time to typecheck. Postulating it makes Agda admit it instead of typechecking. This way, when we modify the file and re-typecheck; he won't be typechecked and everything will go faster. Of course, once the proof is done, it's important not to postulate it anymore.

  --}

  postulate LemmaCommN : {n : ℕ} → trans sucPathℤ (nPathℤ n) ≡ trans (nPathℤ n) sucPathℤ
  --LemmaCommN {0} = trans ((trans-id sucPathℤ)) ((sym (trans-id-l sucPathℤ)))
  --LemmaCommN {(suc n)} = begin
    --trans sucPathℤ (trans sucPathℤ (nPathℤ n)) ≡⟨ cong {! λ x → trans sucPathℤ x!} LemmaCommN ⟩
    --{!trans sucPathℤ (trans (nPathℤ n) sucPathℤ)!} ≡⟨ trans-assoc ⟩
    --{!(trans (trans sucPathℤ (nPathℤ n)) sucPathℤ) ∎!}

  whoZeroN : {i : ℕ} → transp (λ j → (nPathℤ i)j) (pos 0) ≡ (pos i)
  whoZeroN {0} = λ j → (pos 0) -- 
  whoZeroN {suc n} = begin
    transp (λ j → trans sucPathℤ (nPathℤ n) j) (pos 0)              ≡⟨ (LemmaCommN {n = n}) <| (λ x → transp (λ j → x j) (pos 0)) ⟩
    transp (λ j → trans (nPathℤ n) sucPathℤ j) (pos 0)              ≡⟨ transpOfTrans ℤ (nPathℤ n) ℤ (sucPathℤ) ⟩
    transp (λ j → sucPathℤ j) (transp (λ j → (nPathℤ n) j) (pos 0)) ≡⟨ (whoZeroN {n}) <| (λ x → transp (λ j → sucPathℤ j) x) ⟩
    transp (λ j → sucPathℤ j) (pos n)                               ≡⟨ (LemmaT n) <| (λ x → pos (suc x)) ⟩
    pos (suc n)∎

  LemmaNeg : {n : ℕ} → (transp (λ j → (nPathℤ (suc n)) (~ j)) (pos 0)) ≡ (negsuc n)
  LemmaNeg {0} = refl
  LemmaNeg {suc n} = begin
    transp (λ j → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ j)) (pos 0)  ≡⟨⟩
    transp (λ j → (sym (trans sucPathℤ (trans sucPathℤ (nPathℤ n)))) j) (pos 0) ≡⟨ (symOnTrans ℤ sucPathℤ ℤ ((trans sucPathℤ (nPathℤ n)))) <| (λ x → transp (λ j → x j) (pos 0)) ⟩
      
    transp (λ j → (trans (sym (trans sucPathℤ (nPathℤ n))) (sym sucPathℤ)) j) (pos 0) ≡⟨ (symOnTrans ℤ sucPathℤ ℤ ((nPathℤ n))) <| ( λ x → transp (λ j → (trans x (sym sucPathℤ)) j) (pos 0)) ⟩
      
    transp (λ j → trans (trans (sym (nPathℤ n)) (sym sucPathℤ)) (sym sucPathℤ) j) (pos 0) ≡⟨
      transpOfTrans {ℤ} {(pos 0)} ℤ (trans (sym (nPathℤ n)) (sym sucPathℤ)) ℤ (sym sucPathℤ) ⟩
      
    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (trans (sym (nPathℤ n)) (sym sucPathℤ)) j) (pos 0)) ≡⟨
      (sym (symOnTrans ℤ sucPathℤ ℤ (nPathℤ n))) <| (λ x → transp (λ j → (sym sucPathℤ) j) (transp (λ j → x j) (pos 0))) ⟩

    transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (trans sucPathℤ (nPathℤ n))) j) (pos 0)) ≡⟨⟩
    transp (λ j → sucPathℤ (~ j)) (transp (λ j → trans sucPathℤ (nPathℤ n) (~ j)) (pos 0)) ≡⟨
     (LemmaNeg {n = n}) <| (λ x → transp (λ j → sucPathℤ (~ j)) x) ⟩
    transp (λ j → sucPathℤ (~ j)) (negsuc n) ≡⟨ (LemmaT n) <| (λ x → negsuc (suc x)) ⟩
    negsuc (suc n)∎
      

  whoZero : {i : ℤ} → transp (λ j → (iPathℤ i)j) (pos 0) ≡ i
  whoZero {pos n} = whoZeroN
  whoZero {(negsuc n)} = LemmaNeg



  {--

  Here would be an elegant way to prove LemmaPredTransp.
  Problem being, whoIsWho requires to prove a lemma similar (for suc though)
  
  But with an idea kinda similar, we'll be able to simplify the proof in the non naive version.
 
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




  --
  -- LemmaT2 is simply the ℤ version of LemmaT; nothing to see here. 
  --
  LemmaT2 : (p : ℤ)  → primComp (λ i → ℤ) i0 (λ i → empty) (primComp (λ _ → ℤ) i0 (λ i → empty) (primComp (λ i → ℤ) i0 (λ i → empty) p)) ≡ p
  LemmaT2 p = begin
    primComp (λ i → ℤ) i0 (λ i → empty)
      (primComp (λ _ → ℤ) i0 (λ i → empty)
       (primComp (λ i → ℤ) i0 (λ i → empty) p)) ≡⟨  transp-refl p <| (λ x → primComp (λ i → ℤ) i0 (λ i → empty) (primComp (λ _ → ℤ) i0 (λ i → empty) x)) ⟩
    primComp (λ i → ℤ) i0 (λ i → empty)
      (primComp (λ _ → ℤ) i0 (λ i → empty) p) ≡⟨ transp-refl p <| (λ x → primComp (λ i → ℤ) i0 (λ i → empty) x) ⟩
    primComp (λ i → ℤ) i0 (λ i → empty) p ≡⟨ transp-refl p ⟩
    p ∎





  LemmaPredSucP : (p : ℤ) → transp (λ j → sucPathℤ j) (predℤ p) ≡ predℤ (transp (λ j → sucPathℤ j) p) -- ≡ p
  LemmaPredSucP p = begin
    transp (λ j → sucPathℤ j) (predℤ p) ≡⟨ LemmaT2 (pos 1 + (negsuc 0 + p)) ⟩
    pos 1 + (negsuc 0 + p) ≡⟨ sym (eqTr (+-assoc (pos 1) (negsuc 0) p)) ⟩
    pos 1 + negsuc 0 + p ≡⟨⟩
    negsuc 0 + pos 1 + p ≡⟨ eqTr (+-assoc (negsuc 0) (pos 1) p) ⟩
    negsuc 0 + (pos 1 + p) ≡⟨ (sym ((LemmaT2 (pos 1 + p)) <| (λ x → negsuc 0 + x))) ⟩
    predℤ (transp (λ j → sucPathℤ j) p)∎

  abstract
      LemmaPredTransp : {i p : ℤ} → (transp (λ j → (sym (iPathℤ i)) j) (predℤ p)) ≡ (predℤ (transp (λ j → (sym (iPathℤ i)) j) p))
     
      LemmaPredTransp {pos 0} {p} = begin
        transp (λ j → sym (λ _ → ℤ) j) (predℤ p) ≡⟨ transp-refl (predℤ p) ⟩
        predℤ p                                  ≡⟨ sym (transp-refl p) <| (λ x → predℤ x) ⟩
        predℤ (transp (λ j → sym (λ _ → ℤ) j) p) ∎

      LemmaPredTransp {negsuc 0} {p} = begin
        transp (λ j → sym (λ i → trans sucPathℤ (λ _ → ℤ) (~ i)) j) (predℤ p)     ≡⟨⟩
        transp (λ j → trans sucPathℤ (λ _ → ℤ) j) (predℤ p)                       ≡⟨ transpOfTrans {a = (predℤ p)} ℤ sucPathℤ ℤ refl ⟩ --transpoftrans
        transp (λ j → ℤ)  (transp (λ j → sucPathℤ j) (predℤ p))                   ≡⟨  transp-refl (transp (λ j → sucPathℤ j) (predℤ p))  ⟩
        transp (λ j → sucPathℤ j) (predℤ p)                                       ≡⟨ (LemmaPredSucP p) ⟩ --Normal form + lemma of 3 primComp
        predℤ (transp (λ j →  sucPathℤ j) p)                                      ≡⟨ (sym ((transp-refl (transp (λ j →  sucPathℤ j) p)) <| (λ x → predℤ x))) ⟩
        predℤ (transp (λ j → ℤ) (transp (λ j →  sucPathℤ j) p))                   ≡⟨ (sym (transpOfTrans {a = p} ℤ sucPathℤ ℤ refl <| (λ x → predℤ x))) ⟩
        predℤ (transp (λ j →  trans sucPathℤ (λ _ → ℤ) j) p)                      ≡⟨⟩
        predℤ (transp (λ j → sym (λ i → trans sucPathℤ (λ _ → ℤ) (~ i)) j) p) ∎
        

      LemmaPredTransp {pos (suc n)} {p} = begin
        transp (λ j → sym (trans sucPathℤ (nPathℤ n)) j) (predℤ p) ≡⟨ symOnTrans ℤ sucPathℤ ℤ (nPathℤ n) <| (λ x → transp (λ j → x j) (predℤ p)) ⟩
        transp (λ j →  (trans (sym (nPathℤ n)) (sym sucPathℤ)) j) (predℤ p) ≡⟨ transpOfTrans {a = (predℤ p)} ℤ (sym (nPathℤ n)) ℤ  (sym sucPathℤ) ⟩
        transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) (predℤ p)) ≡⟨⟩
        transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) (predℤ p)) ≡⟨ (LemmaPredTransp {i = pos n} {p = p}) <| (λ x → transp (λ j → (sym sucPathℤ) j) x) ⟩
        transp (λ j → (sym sucPathℤ) j) (predℤ (transp (λ j → (sym (nPathℤ n)) j) p)) ≡⟨ (LemmaTranspRev {a = (transp (λ j → (sym (nPathℤ n)) j) p)} predℤ sucPathℤ LemmaPredSucP) ⟩
        predℤ (transp (λ j → (sym sucPathℤ) j) (transp (λ j → (sym (nPathℤ n)) j) p)) ≡⟨ sym (transpOfTrans {a = p} ℤ (sym (nPathℤ n)) ℤ  (sym sucPathℤ)) <| (λ x → predℤ x) ⟩
        predℤ (transp (λ j → trans (sym (nPathℤ n)) (sym sucPathℤ) j) p) ≡⟨ (sym (symOnTrans ℤ sucPathℤ ℤ (nPathℤ n))) <| (λ x → predℤ (transp (λ j → x j) p))  ⟩
        predℤ (transp (λ j → sym (trans sucPathℤ (nPathℤ n)) j) p)∎


      LemmaPredTransp {negsuc (suc n) } {p} = begin
        transp (λ j → sym (λ i → trans sucPathℤ (trans sucPathℤ (nPathℤ n)) (~ i)) j) (predℤ p) ≡⟨⟩
        transp (λ j →  trans sucPathℤ (trans sucPathℤ (nPathℤ n)) j) (predℤ p) ≡⟨  LemmaCommN {n = n} <| (λ x →  transp (λ j →  trans sucPathℤ x j) (predℤ p)) ⟩
        transp (λ j →  trans sucPathℤ (trans (nPathℤ n) sucPathℤ) j) (predℤ p) ≡⟨  trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ} <| (λ x → transp (λ j → x j) (predℤ p)) ⟩
        transp (λ j →  trans (trans sucPathℤ (nPathℤ n)) sucPathℤ j) (predℤ p) ≡⟨  transpOfTrans {a = predℤ p} ℤ (trans sucPathℤ (nPathℤ n)) ℤ sucPathℤ ⟩
        transp (λ j → sucPathℤ j) (transp (λ j → (trans sucPathℤ (nPathℤ n)) j) (predℤ p)) ≡⟨⟩
        transp (λ j → sucPathℤ j) (transp (λ j → sym (λ i → (trans sucPathℤ (nPathℤ n)) (~ i)) j) (predℤ p)) ≡⟨ (LemmaPredTransp {i = negsuc n} {p = p}) <| (λ x → transp (λ j → sucPathℤ j) x) ⟩
        transp (λ j → sucPathℤ j) (predℤ (transp (λ j → sym (λ i → trans sucPathℤ (nPathℤ n) (~ i)) j) p)) ≡⟨⟩
        transp (λ j → sucPathℤ j) (predℤ (transp (λ j → trans sucPathℤ (nPathℤ n) j) p)) ≡⟨ LemmaPredSucP  (transp (λ j → trans sucPathℤ (nPathℤ n) j) p) ⟩
        predℤ (transp (λ j → sucPathℤ j) (transp (λ j → trans sucPathℤ (nPathℤ n) j) p)) ≡⟨  sym (transpOfTrans {a = p} ℤ (trans sucPathℤ (nPathℤ n)) ℤ sucPathℤ) <| (λ x → predℤ x) ⟩
        predℤ (transp (λ j → trans (trans sucPathℤ (nPathℤ n)) sucPathℤ j) p) ≡⟨ sym (trans-assoc {p = sucPathℤ} {q = (nPathℤ n)} {r = sucPathℤ}) <| (λ x → predℤ (transp (λ j → x j) p) )  ⟩
        predℤ (transp (λ j → trans sucPathℤ (trans (nPathℤ n) sucPathℤ) j) p) ≡⟨ sym (LemmaCommN {n = n} <| (λ x →  transp (λ j →  trans sucPathℤ x j) p)) <| (λ x → predℤ x) ⟩
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
