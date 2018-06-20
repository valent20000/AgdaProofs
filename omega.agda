{-# OPTIONS --cubical #-}
module omega where

  open import Cubical
  open import Agda.Builtin.Nat
  open import Cubical.PathPrelude
  open import Cubical.Lemmas

  -- We'll use this syntax a lot : ? ≡⟨ ? ⟩ ?

  -- The definition of Ω used here.

  Ω : (A : Set) → (a : A) → Set
  Ω A a = (a ≡ a)

  Ω² : (A : Set) → (a : A) → Set
  Ω² A a = Ω (a ≡ a) (refl {x = a}) -- (refl {x = a}) ≡ (refl {x = a})

  ---- Lemma: Transp-trans. This shows that concatenating path is the same a transporting.

  lemmaA : {A : Set} {a : A} → transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a) ≡ refl {x = a}
  lemmaA {A} {a} = begin
    transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a) ≡⟨ cong (λ x → transp (λ i → sym x i ≡ a) _) refl ⟩
    transp (λ i → refl i ≡ a) (λ i → a) ≡⟨⟩
    transp (λ i → a ≡ a) (λ i → a) ≡⟨ trans-id refl ⟩
    (refl ∎)

  lemmaB : {A : Set} {a : A} → trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡ refl
  lemmaB {A} {a} = begin
    trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡⟨ cong (λ x → trans _ x) ((trans-id refl)) ⟩
    trans (λ i → a) (λ i → a) ≡⟨ trans-id refl ⟩
    refl

  transp-trans2 : ∀ {A : Set} {a : A} (b : A) (p : a ≡ b) (c : A) (q : b ≡ c) (d : A) (r : c ≡ d) → trans p (trans q r) ≡ transp (\ i → sym p i ≡ r i) q

  transp-trans2 {A} {a} = pathJ _ (pathJ _ (pathJ _  --Induction on r, q, p
    ( begin trans (λ i → a) (trans (λ i → a) (λ i → a)) ≡⟨ lemmaB ⟩
      refl ≡⟨ sym lemmaA ⟩
      transp (λ i → sym (λ i₁ → a) i ≡ a) (λ i → a)∎)))


  --proven first by fabian at https://github.com/bafain/cubical-demo/blob/wip-image/src/Cubical/Lemmas.agda#L60
  -- You can see my own proof above, wich doesn't require anything.
  transp-trans : ∀ {A : Set} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → trans p (trans q r) ≡ transp (\ i → sym p i ≡ r i) q
  transp-trans {A} {a} {b} {c} {d} p q r = transp-trans2 {A} {a} b p c q d r


  -- We now define the whiskering operator like in Hott
  infix 9 _·ᵣ_
  infix 9 _·ₗ_

  -- The sym part is to stay consistent with Hott's notations
  ru : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans p refl
  ru p = sym (trans-id p)

  rBaseCase : {A : Set} → {a b : A} → {p q : (a ≡ b)} → {α : (p ≡ q)} → (trans p refl) ≡ (trans q refl)
  rBaseCase {A} {a} {b} {p} {q} {α} = (trans (sym (ru p)) (trans α (ru q)))

  rPType : {A : Set} {a b : A} (p q : (a ≡ b)) (c : A) (r : b ≡ c) → Set
  rPType p q c r = (trans p r) ≡ (trans q r)


  _·ᵣ_ : {A : Set} {a b : A} {p q : (a ≡ b)} {c : A} (α : (p ≡ q)) (r : (b ≡ c)) → (trans p r) ≡ (trans q r)

  _·ᵣ_ {A} {a} {b} {p} {q} {c} α r = pathJ --Defined by induction on r
    (rPType p q)
    (rBaseCase {α = α})
    c
    r

  -- But remember we're not in Hott!
  -- Now equalities obtained by path inductions aren't definitional anymore. We must thus create a lemma.

  rInit : {A : Set} {a b : A} {p q : (a ≡ b)} (α : (p ≡ q)) → (α ·ᵣ refl) ≡ (rBaseCase {α = α})

  rInit {A} {a} {b} {p} {q} α = λ i → pathJprop ((rPType p q)) (rBaseCase {α = α}) i


  -- We do the same for ·ₗ

  lu : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans refl p
  lu p = sym (trans-id-l p)

  lBaseCase : {A : Set} {b c : A} {r s : (b ≡ c)} {β : (r ≡ s)} → (trans refl r) ≡ (trans refl s)
  lBaseCase {A} {b} {c} {r} {s} {β} = ((trans (sym (lu r)) (trans β (lu s))))

  lPType :  {A : Set} {b c : A} (r s : (b ≡ c)) (a : A) (q : b ≡ a) → Set
  lPType r s = (λ a₁ q₁ → (trans (sym q₁) r) ≡ (trans (sym q₁) s))

  _·ₗ_ : {A : Set} → {a b c : A} → {r s : (b ≡ c)} → (q : (a ≡ b)) → (β : (r ≡ s)) → (trans q r) ≡ (trans q s)

  -- We do the induction on (sym q) and not q because the induction is based! So the sides do not play a symmetrical role.
  _·ₗ_ {A} {a} {b} {c} {r} {s} q β = pathJ
    (lPType r s)
    (lBaseCase {β = β})
    a
    (sym q)

  lInit : {A : Set} {b c : A} {r s : (b ≡ c)} (β : (r ≡ s)) → (refl ·ₗ β) ≡ (lBaseCase {β = β})

  lInit {A} {b} {c} {r} {s} β = λ i → pathJprop (lPType r s) (lBaseCase {β = β}) i


  -- ⋆g is a more general operator, not ⋆ wich is only in Ω.

  infix 8 _⋆g_
  infix 8 _⋆'g_

  _⋆g_ : {A : Set} {a : A} {b : A} {c : A} {p q : (a ≡ b)} {r s : (b ≡ c)} (α : (p ≡ q)) (β : (r ≡ s)) → (trans p r) ≡ (trans q s)

  _⋆g_ {A} {a} {b} {c} {p} {q} {r} {s} α β = trans (α ·ᵣ r) (q ·ₗ β)

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

      Now α ⋆ β and α · β doesn't live in the same world. They cannot be equal!
      But we want to say that they are equal; and indeed, they are in a sense, because their types are equivalent (consider it as isomorphic if you don't know Hott). 
      So we have to transport one along a certain path (here lemma2) in the other world somehow to somewhat achieve an equality.
      This is done in CTT by using PathP
      PathP is the 'same' as using transport:
 
      e : A, e' : A', p: A ≡ A'
      transport p e ≡ e' <-> PathP [λi. A'] (transport p e) e'
  
  --}

  --starOnLoop : {A : Set} → {a : A} → (α β : (Ω² A a)) → PathP (λ i → (lemma2 a i)) (α ⋆ β) (trans α β)
  -- The problem is we want to use a simpler syntax .≡⟨.⟩. for proofs, that works only for homogeneous path. So we're going t have to stay with transport.


  -- Given a, (p a) is the path that we will use everywhere to make things live in the same world.

  p : {A : Set} (a : A) → I → Set
  p = λ a → (λ i → lemma2 a i)

  module _ {A : Set} {a : A} (α β : (Ω² A a)) where -- We define the stars on Ω
    infix 8 _⋆_

    _⋆_ : (Ω² A a)
    _⋆_ = transp (p a) (α ⋆g β)

    _⋆'_ : (Ω² A a)
    _⋆'_ = transp (p a) (α ⋆'g β)



     
  module _ (A : Set) (a : A) (α β : (Ω² A a)) where




    -- Just a notation to make things simpler.
    
    infix 3 _∙g_
    _∙g_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    a ∙g b = trans a b

    infix 3 _∙_
    _∙_ : ∀ {A : Set} {x : A} → x ≡ x → x ≡ x → x ≡ x
    a ∙ b = trans a b





    {--
      Our first interesting lemma. It's a consequence of the umbrella principle :
        → f ∙ g ∙ h ~ transporting both endpoint of g along f and h.
        → So transport of (a ∙ b) is like p-1 ∙ (a ∙ b) ∙ p and so = (p-1 ∙ a ∙ p) ∙ (p-1 ∙ b ∙ p) 
    --}
    transp-∙ : ∀ {A : Set} {x : A} → (q r : x ≡ x) → ∀ y → (p : x ≡ y)  → transp (\ i → p i ≡ p i) (q ∙ r) ≡ (transp (\ i → p i ≡ p i) q ∙ transp (\ i → p i ≡ p i) r)
    transp-∙ {x = x} q r = pathJ _ (begin
             transp (\ i → x ≡ x) (q ∙ r) ≡⟨ fromPathP {A = (\ i → x ≡ x) } refl ⟩
             q ∙ r                        ≡⟨ (let Q = fromPathP {A = (\ i → x ≡ x) } refl; R = fromPathP {A = (\ i → x ≡ x) } refl
                                              in \ i → Q (~ i) ∙ R (~ i)) ⟩
             (transp (\ i → x ≡ x) q ∙ transp (\ i → x ≡ x) r) ∎)


    
    starOnLoop : (α ⋆ β) ≡ (α ∙ β)
    starOnLoop = begin
      (α ⋆ β) ≡⟨⟩
      transp (p a) (α ⋆g β) ≡⟨⟩
      transp (p a) ((α ·ᵣ refl) ∙g (refl ·ₗ β)) ≡⟨ (let A = rInit α; B = lInit β in \ i → transp (p a) (A i ∙g B i)) ⟩

      transp (p a) ((sym (ru refl) ∙g (α ∙g (ru refl))) ∙g (sym (lu refl) ∙g (β ∙g (lu refl)))) ≡⟨ ((let
        A = transp-trans (sym (ru refl)) α (ru refl)
        B = transp-trans (sym (lu refl)) β (lu refl) in \ i → transp (p a) (A i ∙g B i))) ⟩
      transp (p a) (transp (\ i → p a (~ i)) α ∙ transp (\ i → p a (~ i)) β)                    ≡⟨  transp-∙
        (transp (\ i → p a (~ i)) α)
        (transp (\ i → p a (~ i)) β)
        _ _ ⟩  -- Constraint solving for the rest :
    
      transp (p a) (transp (\ i → p a (~ i)) α) ∙ transp (p a) (transp (\ i → p a (~ i)) β)
        ≡⟨ (let A = transp-iso (\ i → p a (~ i)) α; B = transp-iso (\ i → p a (~ i)) β in \ i → A i ∙ B i ) ⟩
      (α ∙ β) ∎




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



    -- We use our more general proof of agreement.
    agreement : (α ⋆ β) ≡ (α ⋆' β)
    agreement = cong (transp (p a)) ((agreementG a refl a refl refl α refl β))
   

    -- Here is our Theorem. The commutativity of ∙ in 2nd loop space.   
    comm : (α ∙ β) ≡ (β ∙ α)
    comm = begin
      α ∙ β ≡⟨ sym starOnLoop ⟩
      α ⋆ β  ≡⟨ agreement ⟩
      α ⋆' β ≡⟨ star'OnLoop ⟩
      (β ∙ α) ∎



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
