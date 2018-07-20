{-# OPTIONS --cubical #-}
module test where

  open import Cubical.FromStdLib hiding (_×_) hiding (_+_)
  open import Cubical.Examples.Int
  open import Cubical.PathPrelude
  open import Cubical.Lemmas

  module _ {ℓ} {A : Set ℓ} {x y z : A} where
  
    lm : trans' {ℓ = ℓ} {A = A} {x = x} {y = y} {z = z }  ≡ trans {ℓ = ℓ} {A = A} {x = x} {y = y} {z = z}
    lm = funExt λ p → funExt λ q → ?
