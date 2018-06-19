{-# OPTIONS --cubical #-}
module omega where

  open import Cubical
  open import Agda.Builtin.Nat
  open import Cubical.PathPrelude
  open import Cubical.Lemmas

  Ω : (A : Set) → (a : A) → Set
  Ω A a = (a ≡ a)

  Ω² : (A : Set) → (a : A) → Set
  Ω² A a = Ω (a ≡ a) (refl {x = a}) -- (refl {x = a}) ≡ (refl {x = a})

  -- Proof of α · β = β · α where · is trans.

  infix 9 _·ᵣ_
  infix 9 _·ₗ_

  -- The sym part is to stay consistent with Hott's notations
  ru : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans p (\ i → y)
  ru p = sym (trans-id p)
  
  _·ᵣ_ : {A : Set} → {a b : A} → {p q : (a ≡ b)} → {c : A} → (α : (p ≡ q)) → (r : (b ≡ c)) → (trans p r) ≡ (trans q r)

  rBaseCase : {A : Set} → {a b : A} → {p q : (a ≡ b)} → {α : (p ≡ q)} → (trans p refl) ≡ (trans q refl)
  rBaseCase {A} {a} {b} {p} {q} {α} = (trans (sym (ru p)) (trans α (ru q)))

  _·ᵣ_ {A} {a} {b} {p} {q} {c} α r = pathJ 
    (λ c₁ r₁ → (trans p r₁) ≡ (trans q r₁))
    rBaseCase
    c
    r

  -- Now equalities obtanied by paht induction aren't definitional anymore. We must thus create a lemma.
  rInit : {A : Set} → {a b : A} → {p q : (a ≡ b)} → (α : (p ≡ q)) → (α ·ᵣ refl) ≡ rBaseCase
  rInit  {A} {a} {b} {p} {q} α =
    pathJ
    (λ q₁ α₁ → {!(α₁ ·ᵣ refl) ≡ (rBaseCase {α = α₁} {q = q₁})!})
    refl
    q
    α


  lu : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ trans (\ i → x) p
  lu p = sym (trans-id-l p)

  _·ₗ_ : {A : Set} → {a b c : A} → {r s : (b ≡ c)} → (q : (a ≡ b)) → (β : (r ≡ s)) → (trans q r) ≡ (trans q s)

  _·ₗ_ {A} {a} {b} {c} {r} {s} q β = pathJ
    (λ a₁ q₁ → (trans (sym q₁) r) ≡ (trans (sym q₁) s))
    ((trans (sym (lu r)) (trans β (lu s))))
    a
    (sym q)

  infix 8 _⋆_
  _⋆_ : {A : Set} → {a : A} → {b : A} → {c : A} → {p q : (a ≡ b)} → {r s : (b ≡ c)}  → (α : (p ≡ q)) → (β : (r ≡ s)) → (trans p r) ≡ (trans q s)

  _⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β = trans (α ·ᵣ r) (q ·ₗ β)

  lemma1 : {A : Set} → (a : A) → trans (λ _ → a) (λ _ → a) ≡ (λ _ → a)
  lemma1 a = trans-id-l refl

  lemmam : {A : Set} → {x y : A} → (x ≡ y) → (x ≡ x) ≡ (y ≡ y)
  lemmam {A} {x} {y} p = pathJ
    (λ y₁ p₁ → (x ≡ x) ≡ (y₁ ≡ y₁))
    ( refl { x = (x ≡ x) } )
    y
    p

  -- We now show equality on the two desired types.
  familRefl :  {A : Set} → (x : A) → Set
  familRefl = λ x → (x ≡ x)

  lemma2 : {A : Set} → (a : A) → (trans (λ _ → a) (λ _ → a) ≡ trans (λ _ → a) (λ _ → a) ) ≡ ( (λ _ → a) ≡ (λ _ → a) )
  
  lemma2 a = cong familRefl ((lemma1 a))


  -- Now α ⋆ β and α · β doesn't live in the same world. So we have to transport one in the other somehow to somewhat achieve an equality.
  -- This is done by using PathP
  -- PathP is the 'same' as using transport:
  {-- e : A, e' : A', p: A ≡ A'
    transport p e ≡ e' <-> PathP [λi. A'] (transport p e) e'
  --}
  
  --starOnLoop : {A : Set} → {a : A} → (α β : (Ω² A a)) → PathP (λ i → (lemma2 a i)) (α ⋆ β) (trans α β)

  -- The problem is we want to use a simpler syntax for proof, that works only for homogeneous path. So we're going t have to stay with transport.

  module _ (A : Set) (a : A) (α β : (Ω² A a)) where

    -- We thus define obj wich is what we want to study
    obj : (λ _ → a) ≡ (λ _ → a)
    obj = (transp (λ i → lemma2 a i) (α ⋆ β))

    -- ? ≡⟨ ? ⟩ ?
    starOnLoop :  obj ≡ (trans α β)
    starOnLoop  =
      begin {!(α ⋆ β)!}


  -- comm : {A : Set} → {a : A} → ( α β : (Ω² A a)) → (trans α β) ≡ (trans β α)
  -- comm = 
  
