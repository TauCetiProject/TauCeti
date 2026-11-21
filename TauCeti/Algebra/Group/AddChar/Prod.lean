/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import TauCeti.Algebra.Group.Prod

/-!
# Additive characters of a product

An additive character of `A × B` is the same as a pair of additive characters of `A` and `B`: a
character `ψ` gives its restrictions `a ↦ ψ (a, 0)` and `b ↦ ψ (0, b)`, and a pair `(ψ₁, ψ₂)` gives
`(a, b) ↦ ψ₁ a * ψ₂ b`. Since Mathlib's `AddChar A M` is a commutative monoid, written
multiplicatively, this is a multiplicative equivalence. It is Tau Ceti's `MonoidHom.coprodEquiv`
transported along Mathlib's `AddChar.toMonoidHomMulEquiv`.

## Main definitions

* `AddChar.coprodEquiv`: the multiplicative equivalence
  `AddChar A M × AddChar B M ≃* AddChar (A × B) M`.
-/

public section

namespace AddChar

variable {A B M : Type*} [AddMonoid A] [AddMonoid B] [CommMonoid M]

/-- Additive characters of `A × B` are pairs of additive characters of `A` and `B`: the pair
`(ψ₁, ψ₂)` gives the character `(a, b) ↦ ψ₁ a * ψ₂ b`. -/
noncomputable def coprodEquiv : AddChar A M × AddChar B M ≃* AddChar (A × B) M :=
  ((toMonoidHomMulEquiv.prodCongr toMonoidHomMulEquiv).trans MonoidHom.coprodEquiv).trans
    ((MulEquiv.monoidHomCongrLeft (MulEquiv.prodMultiplicative (G := A) (H := B)).symm).trans
      toMonoidHomMulEquiv.symm)

/-- The character attached to a pair `(ψ₁, ψ₂)` sends `(a, b)` to `ψ₁ a * ψ₂ b`. -/
@[simp]
theorem coprodEquiv_apply (ψ : AddChar A M × AddChar B M) (x : A × B) :
    coprodEquiv ψ x = ψ.1 x.1 * ψ.2 x.2 := by
  simp [coprodEquiv, toMonoidHomMulEquiv]

/-- The first character attached to `ψ` is its restriction `a ↦ ψ (a, 0)`. -/
@[simp]
theorem coprodEquiv_symm_apply_fst (ψ : AddChar (A × B) M) (a : A) :
    (coprodEquiv.symm ψ).1 a = ψ (a, 0) := by
  simp [coprodEquiv, toMonoidHomMulEquiv]

/-- The second character attached to `ψ` is its restriction `b ↦ ψ (0, b)`. -/
@[simp]
theorem coprodEquiv_symm_apply_snd (ψ : AddChar (A × B) M) (b : B) :
    (coprodEquiv.symm ψ).2 b = ψ (0, b) := by
  simp [coprodEquiv, toMonoidHomMulEquiv]

end AddChar
