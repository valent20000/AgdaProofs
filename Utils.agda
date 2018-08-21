{-# OPTIONS --cubical #-}
module Utils where

  open import Cubical.PathPrelude
  open import Cubical.Lemmas
  open import Cubical.FromStdLib
  open import Cubical.GradLemma

  open import Agda.Primitive
  open import Agda.Builtin.Equality renaming (_≡_ to _≡b_) renaming (refl to reflb)

  open import Data.Nat.Base hiding (_⊔_ ; _^_)
  open import Data.Nat.Properties 

  open import Cat.Category


  {--
    First some really useful lemma : transforms equality from the standard library to Cubical equalities.
    Indeed, the stdlib was proven in Hott (with only refl).
    This eqTr lemma associate the refl in Hott to the refl (path) from Cubical.
    Simply stated : everything that was proven in Hott is of course true in Ctt.
  --}

  eqTr : {A : Set} {a b : A} (p : a ≡b b) → a ≡ b
  eqTr reflb = refl
  

  -- For the inspect idiom
  -- Used in the 'Bonus part'; skip it.
  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x
    
  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl




  -- This is just a convenient notation to avoid using a lot of trans sometimes.
  
  infix 3 _∙_
  _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  a ∙ b = trans a b


  -- Here are some notations i came up with to make things easier to read.
  
  module _ {ℓ} {ℓ'} where
    
    {-- This operator is just cong, but it makes proof easier to read.
        Instead of writing cong X Y, one can now write Y <| X
        That can be read as 'Y, under the context X'
        When reading a proof, people won't care about the context, and because we read left to right, this allows to put the important part first, on top of clearly separating the context from the rest and avoid re-writing cong everytime.
    --}
    infix 4 _<|_

    _<|_ : {A : Set ℓ} {B : Set ℓ'} {x y : A} (a : x ≡ y) (cont : A → B) → cont x ≡ cont y  
    a <| cont = ((cong cont) a)

    {-- This is just function application, sometimes it's convenient.
        If you want to put the interesting property on the left of your proof.
        sym p with p your proof become p >| sym (A mathematician won't care about the sym part when reading the proof; what is important is p). 
    --}
    infix 4 _>|_
    _>|_ : {A : Set ℓ} {B : Set ℓ'} (x : A) (f : A → B) → B
    _>|_ x f = f x
    
  {--
    The coming lemmas are trivial but useful lemmas proven by path inductions.
    To see why they are obviously true, replace every path by 'not moving' (Rouglhy speaking that's what a path induction does)
  --}


  symOnTrans : {A : Set} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (sym (trans p q)) ≡ trans (sym q) (sym p)

  symOnTrans = pathJ _ (pathJ _ --Induction on q and then p.
    refl)

  module _ {ℓ} where

    symOnTransL : {A : Set ℓ} {a : A} (b : A) (p : a ≡ b) (c : A) (q : b ≡ c) → (sym (trans p q)) ≡ trans (sym q) (sym p)

    symOnTransL = pathJ _ (pathJ _ --Induction on q and then p.
      refl)

  module _ {ℓ} {ℓ'} {ℓ''} where

    {-- Simply stating that context adds up.
        A context inside a context gives you a big context.
    --}
    
    LmCongCong : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {x : A} (g : B → C) (f : A → B) (y : A) (p : x ≡ y) → cong g (cong f p) ≡ cong (λ x → g (f x)) p
    LmCongCong g f = pathJ _ (refl)



  module _ {ℓ} where

    {-- Going back and forth a path is the same as not moving --}
    
    LmTransSym : {A : Set ℓ} {a : A} (b : A) (q : a ≡ b) → trans q (sym q) ≡ refl
    LmTransSym {A} = pathJ _ (trans-id refl)

    {-- Here is defined the power operator of a function; it's used in different ways throughout the project --}

    infix 95 _^_
         
    _^_ : {A :  Set ℓ} (f : A → A) (n : ℕ) → A → A
    f ^ 0 = λ x → x
    f ^ (suc n) = λ a → f ((f ^ n) a)

    
    ^-+ : {A :  Set ℓ} (f : A → A) (n1 n2 : ℕ) → (f ^ (n1 + n2)) ≡ (λ x → (f ^ n1) ((f ^ n2) x))
    ^-+ f zero n2 = begin
      f ^ (zero + n2) ≡⟨⟩
      (λ x →  (f ^ n2) x) ∎
      
    ^-+ f (suc n) n2 = begin
      (λ a → f ((f ^ (n + n2)) a)) ≡⟨ ( ^-+ f n n2 <| \ x → (λ a → f (x a))) ⟩
      (λ x → f ((f ^ n) ((f ^ n2) x))) ∎

    -- Iterating n time an 'identity' function over x gives back x
    LemmaIt : {A :  Set ℓ} {x : A} (n : ℕ) (f : A → A) (p : f x ≡ x) → ((f ^ n) x) ≡ x
    LemmaIt {A} {x} (0) f p = refl
    LemmaIt {A} {x} (suc n) f p = begin
      f ((f ^ n) x) ≡⟨ (LemmaIt n f p) <| (λ x → f x) ⟩
      f x ≡⟨ p ⟩
      x ∎

    {-- (arbitrary level version) 
      Elimintates n primComp along a trivial path of x for x given.
      To understand why it's needed see Numbers.agda
    --}
    ElimCompL : {A : Set ℓ} (n : ℕ) (e : A) → PathP _ _ _
    ElimCompL {A} n e = LemmaIt n (λ x → (primComp (λ _ → A) i0 (λ i → empty) x)) (transp-refl e)
    

-- You can change a transport over a composition of path in two successive transports;
  transpOfTrans : {A : Set} {a : A} (B : Set) (p : A ≡ B) (C : Set) (q : B ≡ C) → (transp (λ j → (trans p q) j) a) ≡ (transp (λ j → q j) (transp (λ j → p j) a))
  transpOfTrans {A} {a} = pathJ _ (pathJ _  (begin --By induction on p and q.
  
      transp (λ j → trans (λ i → A) (λ i → A) j) a                     ≡⟨ (trans-id refl) <|  (λ x → transp (λ j → x j) a) ⟩
      transp (λ j → A) a                                               ≡⟨ (transp-refl a) ⟩ 
      a                                                                ≡⟨ sym (transp-refl a) ⟩
      (transp (λ j → refl j) a)                                        ≡⟨ sym (transp-refl (transp (λ j → refl j) a)) ⟩
      (transp (λ j → refl j) (transp (λ j → refl {x = A} j) a)) ∎))

  {-- Lemma to reverse the path:
      If a path conserv f a given function, then so does the symmetrical path.
      (To optimize our proof here we might've shown a more powerful lemma; stating that if two function 'cancel' each others; then we can obtain what we want. I'm not sure it would've worked) 
  --}
   
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


    {-- (standard version) 
      Elimintates n primComp along a trivial path of x for x given.
      To understand why it's needed see Numbers.agda
    --}
 
  ElimComp : {A : Set} (n : ℕ) (e : A) → PathP _ _ _
  ElimComp {A} n e = LemmaIt n (λ x → (primComp (λ _ → A) i0 (λ i → empty) x)) (transp-refl e)

  empCmp : {A : Set} (e : A) → A
  empCmp {A} = (λ e → primComp (λ _ → A) i0 (λ i → empty) e)

  -- Could also be proven by transp-iso
  LmExchgPath : {A : Set} {a : A}  (B : Set) (p : A ≡ B) (b : B) (e : transp (λ i → p i) a ≡ b) → a ≡ transp (λ i → (sym p) i) b
  LmExchgPath {A} {a} = pathJ _ λ b e → begin
    a ≡⟨ trans (sym (transp-refl a)) e ⟩
    b ≡⟨ sym (transp-refl b) ⟩
    transp (λ i → sym (λ i₁ → A) i) b ∎

  module _ {ℓ} where

    -- Proof that equivalence is transitive. Using univalence, it's trivial.
    transEq : {A B C : Set ℓ} → A ≃ B → B ≃ C → A ≃ C
    transEq eq eq' = pathToEquiv (trans (equivToPath eq) (equivToPath eq'))
    

  module _ {ℓa ℓb} (c : RawCategory ℓa ℓb) where

    open RawCategory c


    -- A lemma on transport on arrows in a category; used in the bonus part.
    
    lemmaX : {A B C : Object} (D : Object) (pa : A ≡ D) (E : Object) (pb : B ≡ E) (F : Object) (pc : C ≡ F) (f : Arrow A B) (g : Arrow B C) →
      transp (λ j → Arrow (pb j) (pc j)) g <<< transp (λ j → Arrow (pa j) (pb j)) f ≡ transp (λ j → Arrow (pa j) (pc j)) (g <<< f)
      
    lemmaX {A} {B} {C} = pathJ _ (pathJ _ (pathJ _ λ f g → begin
      transp (λ j → Arrow B C) g <<< transp (λ j → Arrow A B) f ≡⟨ (let
                                                                       X = transp-refl g
                                                                       Y = transp-refl f
                                                                       in λ j → (X j) <<< (Y j)) ⟩
      (g <<< f) ≡⟨ sym (transp-refl (g <<< f)) ⟩
      transp (λ j → Arrow A C) (g <<< f) ∎))
