/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Transporting additive characters along equivalences

Precomposing an additive character of `B` with an additive equivalence `e : A ≃+ B` yields an
additive character of `A`. Since `AddChar _ M` carries the pointwise multiplicative monoid
structure, this defines a multiplicative isomorphism `AddChar.congrLeft e : AddChar B M ≃*
AddChar A M`, built from Mathlib's `AddChar.toMonoidHomMulEquiv`,
`MulEquiv.monoidHomCongrLeft`, and `AddEquiv.toMultiplicative`.

## Main definitions

* `AddChar.congrLeft`: precomposition with `e : A ≃+ B` as a multiplicative equivalence
  `AddChar B M ≃* AddChar A M`.
-/

public section

namespace AddChar

variable {A B M : Type*} [AddMonoid A] [AddMonoid B] [CommMonoid M]

/-- Precomposition with an additive equivalence `e : A ≃+ B` induces a multiplicative
isomorphism `AddChar B M ≃* AddChar A M`. -/
def congrLeft (e : A ≃+ B) : AddChar B M ≃* AddChar A M :=
  toMonoidHomMulEquiv.trans
    ((MulEquiv.monoidHomCongrLeft (AddEquiv.toMultiplicative e.symm)).trans
      toMonoidHomMulEquiv.symm)

/-- Precomposing a character `ψ` along `e : A ≃+ B` evaluates at `a : A` as `ψ (e a)`. -/
@[simp]
theorem congrLeft_apply (e : A ≃+ B) (ψ : AddChar B M) (a : A) :
    congrLeft e ψ a = ψ (e a) := by
  simp [congrLeft, toMonoidHomMulEquiv]

/-- The inverse of `congrLeft e` is `congrLeft e.symm`. -/
@[simp]
theorem congrLeft_symm (e : A ≃+ B) :
    (congrLeft e : AddChar B M ≃* AddChar A M).symm = congrLeft e.symm := by
  ext ψ b
  simp [congrLeft, toMonoidHomMulEquiv]

end AddChar
