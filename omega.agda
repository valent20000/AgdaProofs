{-# OPTIONS --cubical #-}
module omega where

  open import Cubical
  open import Agda.Builtin.Nat
  open import Cubical.PathPrelude
  open import Cubical.Lemmas

  open import Agda.Primitive

  {--

    This is used as an introduction to my internship, and to the use of Cubical Agda in practice.
    You'll learn here how to do basic proofs in CA.
    This was done during the first week of my internship as a 'warmup'.

  --}

  -- We'll use this syntax a lot : ? ≡⟨ ? ⟩ ? 
  -- Deep down, it's just defined as transitivity of paths, but it's really useful to make things clear.
  -- When you want to prove a ≡ b, you can put a ≡⟨ p ⟩ b with p a proof of a ≡ b. The idea is to used that syntax to make intermediate steps.

  -- Also, if you have Agda Mode installed on emacs; here are the really useful shortcuts you'll use :
  
  -- \ + <char>; for greek letters : \G + <char> (ex : λ); for elementary types \b + <char> (ex : ℕ)
  
  -- ctrl c; ctrl s in a goal; Agda will try to infer the result if he can

  -- ctrl c; ctrl d gives the type of the selected thing (for example what you typed in your goal)

  -- ctrl c; ctrl , gives the goal and the context.


  -- This is a proof that composition in the second loop space commutes. (See : Hott; Theorem 2.1.6 pages 68-69)
  -- It's not necessary to have a deep understanding of the proof to understand what we will do here; the point here being presenting Cubical Agda, not the proof.
  -- But quickly looking at it could help.


  -- The definition of Ω used here.
  {--
    These things are the loop spaces (1 and 2).
 
      a ≡ a (in type A); the type of proofs that a is equal to a (an element would be refl for example)

      refl a ≡ refl a (in type a ≡ a); the type of proofs that refl a is equal to refl a (an element would be refl (refl a) for example)
  --}

  Ω : (A : Set) → (a : A) → Set
  Ω A a = (a ≡ a)

  Ω² : (A : Set) → (a : A) → Set
  Ω² A a = Ω (a ≡ a) (refl {x = a}) -- (refl {x = a}) ≡ (refl {x = a})


  -- Here we will define the loop spaces in a more general way.
  -- We can learn two things from this :
  -- Inductions in Agda are done by pattern matching.
  -- To do mutual inductions, one should pay attention to the order of definition, refln should be define before the body of Ωn.
  
  Ωn : (A : Set) (a : A) (n : Nat) → Set
  refln : (A : Set) (a : A) (n : Nat) →  Ωn A a n

  Ωn A a 0 = A
  Ωn A a (suc n) = Ω (Ωn A a n) (refln A a n)

  refln A a zero = a
  refln A a (suc n) = refl {x = refln A a n} -- The syntax {var = ?} is used to give optional parameters. These are parameters that Agda will try to infer.
  
  {--
    First we will show a lemma about trans. Transitivity of 3 paths :
      
         p     q     r 
      a --> b --> c --> d

    Is the same as taking q :

       p     q     r
     a<~~ b --> c ~~>d

    And transporting it's two endpoints; c along the path r; and b along the path p (in reverse).

  --}

  -- To understand why these two lemmas are here, i would advise looking at the proof of transp-trans2 below.

  
  lemmaA : {A : Set} {a : A} → transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a) ≡ refl {x = a}
  lemmaA {A} {a} = begin
    transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a) ≡⟨⟩ -- there is a ⟨⟩ so we gave no proof; that means that the two things are definitionally equal (htey reduce to the same normal form) 
    transp (λ i → refl i ≡ a) (λ i → a)           ≡⟨⟩ -- Indeed; sym of a constant path gives back that path; refl at any point is a.
    transp (λ i → a ≡ a) (λ i → a) ≡⟨ trans-id refl ⟩ -- And transporting along a constant path (here a ≡ a doesn't depend on i) gives bkac what you gave.
    (refl ∎)

  lemmaB : {A : Set} {a : A} → trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡ refl
  lemmaB {A} {a} = begin
  
    --trans-id p gives that concatenating p with refl gives back p.
    -- Here we use cong; wich is really important; it takes 2 arguments; a 'context' and an equality; it gives back an equality under the context.
    trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡⟨ cong (λ x → trans (λ i → a) x) ((trans-id refl)) ⟩
    trans (λ i → a) (λ i → a)                   ≡⟨ trans-id refl ⟩
    refl

  
  transp-trans2 : ∀ {A : Set} {a : A} (b : A) (p : a ≡ b) (c : A) (q : b ≡ c) (d : A) (r : c ≡ d) → trans p (trans q r) ≡ transp (\ i → sym p i ≡ r i) q

  {-- To prove this; we use path induction three times.
      In Cubical Agda, path induction is NOT primitive; we cannot do this induction by pattern matching; instead we use pathJ.
      pathJ takes 4 parameters; but there is a way to avoid that.
      If you state your theorem by putting the paths like that : (x : A) (p : y ≡ x); preferably at the end, then using pathJ, Agda will be able to infer the first parameter; and you only have to give the second; the other 2 are 'still' parameters; see that :

      To define a function f = λ a → a you can either do :
        f a = a
        f = refl
      It's the same principle here (the = refl one) ; by not pattern matching on the arguments;
  --}

  transp-trans2 {A} {a} = pathJ _ (pathJ _ (pathJ _  --Induction on r, q, p
  
      -- Every path is now refl a; ie (λ i → a); the 'not moving' path
      
    ( begin trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡⟨ lemmaB ⟩ -- Obviously doing refl 3 times is the same as doing refl once. That's proven in lemmaB
      refl                                              ≡⟨ sym lemmaA ⟩ -- We use sym here because lemmaA proves that what is below is equal to refl; so we take the path in the other direction to get refl ≡ ...)
      transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a)∎))) --Transporting refl along this path gives refl; see lemmaA


  -- transp-trans was actually proven first by fabian here https://github.com/bafain/cubical-demo/blob/wip-image/src/Cubical/Lemmas.agda#L60
  -- The proof that i gave above doesn't require anything.
  
  transp-trans : ∀ {A : Set} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → trans p (trans q r) ≡ transp (\ i → sym p i ≡ r i) q
  transp-trans {A} {a} {b} {c} {d} p q r = transp-trans2 {A} {a} b p c q d r


  -- -- We now define the whiskering operator like in Hott
  infix 9 _·ᵣ_
  infix 9 _·ₗ_
  

  -- The sym part is to stay consistent with Hott's notations
  ru : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans p refl
  ru p = sym (trans-id p)

  --Those 2 are used for the path induction.
  rBaseCase : {A : Set} → {a b : A} → {p q : (a ≡ b)} → {α : (p ≡ q)} → (trans p refl) ≡ (trans q refl)
  rBaseCase {A} {a} {b} {p} {q} {α} = (trans (sym (ru p)) (trans α (ru q)))

  rPType : {A : Set} {a b : A} (p q : (a ≡ b)) (c : A) (r : b ≡ c) → Set
  rPType p q c r = (trans p r) ≡ (trans q r)


  
  _·ᵣ_ : {A : Set} {a b : A} {p q : (a ≡ b)} {c : A} (α : (p ≡ q)) (r : (b ≡ c)) → (trans p r) ≡ (trans q r)

  {--
    As stated before; one can use pathJ with the four parameters. These are then
      . The type family
      . The base case (where the path is refl)
      . The element where the path below will go to.
      . The path the induction is on.
  
  --}
  
  _·ᵣ_ {A} {a} {b} {p} {q} {c} α r = pathJ --Defined by induction on r
    (rPType p q)
    (rBaseCase {α = α})
    c
    r

  {-- We have defined our operator as stated in Hott.
      But remember we're not in Hott!
      Now equalities obtained by path inductions aren't definitional anymore. We must thus create a lemma.
  --}

  -- pathJprop states that we get the base case when we give refl to something that was proven by path induction.
  
  rInit : {A : Set} {a b : A} {p q : (a ≡ b)} (α : (p ≡ q)) → (α ·ᵣ refl) ≡ (rBaseCase {α = α})
  rInit {A} {a} {b} {p} {q} α = λ i → pathJprop ((rPType p q)) (rBaseCase {α = α}) i


  -- /!\ You can skip this part, we just do the exact same thing but for ·ₗ (that part was 'left out' in Hott); it can be a good exercise to try to prove.
  
  lu : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans refl p
  lu p = sym (trans-id-l p)

  lBaseCase : {A : Set} {b c : A} {r s : (b ≡ c)} {β : (r ≡ s)} → (trans refl r) ≡ (trans refl s)
  lBaseCase {A} {b} {c} {r} {s} {β} = ((trans (sym (lu r)) (trans β (lu s))))

  lPType :  {A : Set} {b c : A} (r s : (b ≡ c)) (a : A) (q : b ≡ a) → Set
  lPType r s = (λ a₁ q₁ → (trans (sym q₁) r) ≡ (trans (sym q₁) s))

  _·ₗ_ : {A : Set} → {a b c : A} → {r s : (b ≡ c)} → (q : (a ≡ b)) → (β : (r ≡ s)) → (trans q r) ≡ (trans q s)

  -- We do the induction on (sym q) and not q because the induction is based! (one of the endpoints doesn't move) So the sides do not play a symmetrical role.
  _·ₗ_ {A} {a} {b} {c} {r} {s} q β = pathJ
    (lPType r s)
    (lBaseCase {β = β})
    a
    (sym q)

  lInit : {A : Set} {b c : A} {r s : (b ≡ c)} (β : (r ≡ s)) → (refl ·ₗ β) ≡ (lBaseCase {β = β})

  lInit {A} {b} {c} {r} {s} β = λ i → pathJprop (lPType r s) (lBaseCase {β = β}) i


  {-- Now let's define an operator, that is a generalized version of the one in Hott.
      The point is to be able to prove things by path inductions, indeed in the loopspace both endpoints of paths are tied and one cannot use path induction.
      (For example, in the circle, there are paths connecting a to a that are NOT refl (the 'not moving path').

      At some point Hott states : 'now suppose a ≡ b ≡ c' (and everything is refl).
      The rigorous way of doing that is what is done here, by first creating a general operator and then making it coincide with a less general one.
      ⋆ is only in Ω, wich makes it's endpoints tied. And so proving lemmas on it is 'impossible'.
  --}

  infix 8 _⋆g_
  infix 8 _⋆'g_

  _⋆g_ : {A : Set} {a : A} {b : A} {c : A} {p q : (a ≡ b)} {r s : (b ≡ c)} (α : (p ≡ q)) (β : (r ≡ s)) → (trans p r) ≡ (trans q s)

  _⋆g_ {A} {a} {b} {c} {p} {q} {r} {s} α β = trans (α ·ᵣ r) (q ·ₗ β)

  -- We also define the ' generalized.
  
  _⋆'g_ : {A : Set} {a : A} {b : A} {c : A} {p q : (a ≡ b)} {r s : (b ≡ c)} (α : (p ≡ q)) (β : (r ≡ s)) → (trans p r) ≡ (trans q s)

  _⋆'g_ {A} {a} {b} {c} {p} {q} {r} {s} α β = trans (p ·ₗ β) (α ·ᵣ s)


  -- First we show that the two stars are actually equals using 4 inductions.

  agreementG : {A : Set} {a : A} (b : A) (p : (a ≡ b)) (c : A) (r : (b ≡ c)) (q : (a ≡ b)) (α : (p ≡ q)) (s : (b ≡ c)) (β : (r ≡ s)) → (α ⋆g β) ≡ (α ⋆'g β)
 
  agreementG {A} {a} =
   (pathJ _ --Induction on p
   (pathJ _ --Induction on r
   (pathJ _ --Induction on α
   (pathJ _ --Induction on β
   -- We now have to prove that the equality holds when everything is refl.
   -- Luckily; it's true definitionally. So refl works.
   refl
   ))))

  -- We're going to need these lemmas to have homogeneous types. See the explanation below.

  lemma1 : {A : Set} (a : A) → trans (λ _ → a) (λ _ → a) ≡ (λ _ → a)
  lemma1 a = trans-id-l refl

  -- We now show equality on the two desired types.
  familRefl :  {A : Set} (x : A) → Set
  familRefl = λ x → (x ≡ x)

  lemma2 : {A : Set} (a : A) → (trans (λ _ → a) (λ _ → a) ≡ trans (λ _ → a) (λ _ → a)) ≡ ( (λ _ → a) ≡ (λ _ → a) )
  lemma2 a = cong familRefl (lemma1 a)


  {-- In Hott, the proof is simple, just unfold and simplify everything.
      The problem here is that we're not in Hott. Here we have :
        - α ⋆ β : (trans (λ _ → a) (λ _ → a) ≡ trans (λ _ → a) (λ _ → a))
        - α ∙ β : ( (λ _ → a) ≡ (λ _ → a) )

      Because the types are not the same, α ⋆ β and α · β doesn't live in the same world. They cannot be equal!
      But we want to say that they are equal; and indeed, they are in a sense, because their types are equal!
 
      So we have to transport one along a certain path (here lemma2) in the other world somehow to somewhat achieve an equality.

      This is often done in CTT by using PathP
      PathP is the 'same' as using transport:
 
      e : A, e' : A', p: A ≡ A'
      transport p e ≡ e' <-> PathP [λi. A'] (transport p e) e'

      The problem is we want to use the syntax .≡⟨.⟩. for proofs. So we're going to have to stay with transport.
  
  --}

  --starOnLoop : {A : Set} → {a : A} → (α β : (Ω² A a)) → PathP (λ i → (lemma2 a i)) (α ⋆ β) (trans α β)


  -- Given a, (p a) is the path that we will use everywhere to make things live in the same world.

  p : {A : Set} (a : A) → I → Set
  p = λ a → (λ i → lemma2 a i)

  -- We now plunge ourselves in the loop world; where a ≡ b ≡ c etc ...
  
  module _ {A : Set} {a : A} (α β : (Ω² A a)) where -- We define the stars on Ω
    infix 8 _⋆_


    -- It's important to see how those operators are defined.
    -- They are defined as our more general operators once transported in the world of the loopspace. (Along a certain path p given by lemma2)
    -- By defining those this way, we'll be able to use the properties proven for the general operators.
    
    _⋆_ : (Ω² A a)
    _⋆_ = transp (p a) (α ⋆g β)

    _⋆'_ : (Ω² A a)
    _⋆'_ = transp (p a) (α ⋆'g β)

     
  module _ (A : Set) (a : A) (α β : (Ω² A a)) where


    -- Just a notation to replace trans and make things simpler.
    -- g stands for generalized.
    
    infix 3 _∙g_
    _∙g_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    a ∙g b = trans a b

    infix 3 _∙_
    _∙_ : ∀ {A : Set} {x : A} → x ≡ x → x ≡ x → x ≡ x
    a ∙ b = trans a b





    {--
      Our first interesting lemma. It's a consequence of the umbrella principle :
        → f ∙ g ∙ h ~ transporting both endpoint of g along f and h. As stated in trans-transp.

        → So transport of (a ∙ b) along (sym p) and p is like p-1 ∙ (a ∙ b) ∙ p and so = (p-1 ∙ a ∙ p) ∙ (p-1 ∙ b ∙ p) 
    --}
    transp-∙ : ∀ {A : Set} {x : A} → (q r : x ≡ x) → ∀ y → (p : x ≡ y)  → transp (\ i → p i ≡ p i) (q ∙ r) ≡ (transp (\ i → p i ≡ p i) q ∙ transp (\ i → p i ≡ p i) r)
    transp-∙ {x = x} q r = pathJ _ (begin

             -- By path induction on p
             --fromPathP creates an equality between a transp of X and X given a a path. Here we could have used transp-refl : it's type being PathP A x y → transp A x ≡ y, by giving refl of type PathP we get what we want.
             transp (\ i → x ≡ x) (q ∙ r) ≡⟨ fromPathP {A = (\ i → x ≡ x) } refl ⟩ 
             q ∙ r                        ≡⟨ (let Q = fromPathP {A = (\ i → x ≡ x) } refl; R = fromPathP {A = (\ i → x ≡ x) } refl
                                              in \ i → Q (~ i) ∙ R (~ i)) ⟩
             -- Here we do two steps at the same time; Q/R changes q/r to what we want. The 'in' part gives us the ability to create a path (\ i → .) using Q and R. 
             (transp (\ i → x ≡ x) q ∙ transp (\ i → x ≡ x) r) ∎)


    -- Here we show, like in Hott, that the star operator is actually transitivity in the loop type.
    -- You can learn from here that _ is used to tell Agda 'infer it yourself'. In Agda mode, it will be higlighted in Yellow if he's unable to.
    
    starOnLoop : (α ⋆ β) ≡ (α ∙ β)
    starOnLoop = begin
      (α ⋆ β)                                   ≡⟨⟩ --By definition.
      transp (p a) (α ⋆g β)                     ≡⟨⟩ -- We extend little by little the definitions.
      
      transp (p a) ((α ·ᵣ refl) ∙g (refl ·ₗ β)) ≡⟨ (let A = rInit α; B = lInit β in \ i → transp (p a) (A i ∙g B i)) ⟩

      -- Remember the definition of ·ᵣ, by path induction; we know that when applied to refl they give back the base case.
      -- (We do two steps at once).

      transp (p a) ((sym (ru refl) ∙g (α ∙g (ru refl))) ∙g (sym (lu refl) ∙g (β ∙g (lu refl)))) ≡⟨ ((let
        A = transp-trans (sym (ru refl)) α (ru refl)
        B = transp-trans (sym (lu refl)) β (lu refl) in \ i → transp (p a) (A i ∙g B i))) ⟩

      -- We change our p ∙ q ∙ r in transports. 
        
      transp (p a) (transp (\ i → p a (~ i)) α ∙ transp (\ i → p a (~ i)) β)                    ≡⟨  transp-∙
        (transp (\ i → p a (~ i)) α)
        (transp (\ i → p a (~ i)) β)
        _ _ ⟩

      -- We know that transporting the whole thing along (p a) is the same as transporting the 2 along (p a) and then concatenating.
      
      transp (p a) (transp (\ i → p a (~ i)) α) ∙ transp (p a) (transp (\ i → p a (~ i)) β)

      -- Last step is easy : transporting along a path back and forth gives back what you gave in the first place. That's transp-iso.

        ≡⟨ (let A = transp-iso (\ i → p a (~ i)) α; B = transp-iso (\ i → p a (~ i)) β in \ i → A i ∙ B i ) ⟩

      (α ∙ β) ∎



    -- You can skip this part, same proof as above.
    star'OnLoop : (α ⋆' β) ≡ (β ∙ α) -- A parallel proof.
    star'OnLoop = begin
      (α ⋆' β) ≡⟨⟩
      transp (p a) (α ⋆'g β) ≡⟨⟩
      transp (p a) ((refl ·ₗ β) ∙g (α ·ᵣ refl))  ≡⟨ (let A = (rInit α); B = (lInit β) in \ i → transp (p a) (B i ∙g A i)) ⟩
      transp (p a) ((sym (lu refl) ∙g (β ∙g (lu refl))) ∙g (sym (ru refl) ∙g (α ∙g (ru refl)))) ≡⟨ ((let
        A = transp-trans (sym (ru refl)) α (ru refl)
        B = transp-trans (sym (lu refl)) β (lu refl) in \ i → transp (p a) (B i ∙g A i))) ⟩
      transp (p a) ((transp (\ i → p a (~ i)) β) ∙ (transp (\ i → p a (~ i)) α)) ≡⟨ transp-∙
      ((transp (\ i → p a (~ i)) β) )
      ((transp (\ i → p a (~ i)) α))
      _ _ ⟩
          
      transp (p a) (transp (\ i → p a (~ i)) β) ∙ transp (p a) (transp (\ i → p a (~ i)) α) ≡⟨ ((let A = transp-iso (\ i → p a (~ i)) α; B = transp-iso (\ i → p a (~ i)) β in \ i → B i ∙ A i )) ⟩
      (β ∙ α) ∎



    -- We use our more general proof of agreement
    -- Here we know that the general operators agree, and by definition, our operators are these ones under the context transp (p a).
    -- We can thus simply transport the proof!
    agreement : (α ⋆ β) ≡ (α ⋆' β)
    agreement = cong (transp (p a)) ((agreementG a refl a refl refl α refl β))
   

    -- Here is our Theorem. The commutativity of ∙ in 2nd loop space.   
    comm : (α ∙ β) ≡ (β ∙ α)
    comm = begin
      α ∙ β ≡⟨ sym starOnLoop ⟩
      α ⋆ β  ≡⟨ agreement ⟩
      α ⋆' β ≡⟨ star'OnLoop ⟩
     (β ∙ α) ∎


-- END
--------------------------------------------------------------------
--------------------------------------------------------------------



{-- Unused lemmas will be put here.
  lemmam : {A : Set} {x y : A} (x ≡ y) → (x ≡ x) ≡ (y ≡ y)
  lemmam {A} {x} {y} p = pathJ
    (λ y₁ p₁ → (x ≡ x) ≡ (y₁ ≡ y₁))
    ( refl { x = (x ≡ x) } )
    y
    p
--}

{--
  Tryin prove and undeerstand pathJProp ?
  rInit : {A : Set} → {a b : A} → {p q : (a ≡ b)} → (α : (p ≡ q)) → (α ·ᵣ refl) ≡ (rBaseCase {α = α})
  rInit  {A} {a} {b} {p} {q} α =
    pathJ
    (λ q₁ α₁ → {!(α₁ ·ᵣ refl) ≡ (rBaseCase {α = α₁})!})
    refl
    q
    α
--}
