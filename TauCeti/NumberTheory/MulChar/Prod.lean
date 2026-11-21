/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.Algebra.Group.Prod

/-!
# Multiplicative characters of a product

A multiplicative character of `M × N` is the same as a pair of multiplicative characters of `M`
and `N`: a character `χ` gives its restrictions `m ↦ χ (m, 1)` and `n ↦ χ (1, n)`, and a pair
`(χ₁, χ₂)` gives `(m, n) ↦ χ₁ m * χ₂ n`. The restrictions are characters because `(m, 1)` is
a unit if and only if `m` is a unit, and `(1, n)` is a unit if and only if `n` is a unit. For
finite commutative rings `R₁` and `R₂`, this describes the characters of `R₁ × R₂`.

The equivalence is Tau Ceti's `MonoidHom.coprodEquiv` for the unit groups, transported along
Mathlib's `MulChar.mulEquivToUnitHom` and `MulEquiv.prodUnits`.

## Main definitions

* `MulChar.coprodEquiv`: the multiplicative equivalence
  `MulChar M R × MulChar N R ≃* MulChar (M × N) R`.
-/

public section

namespace MulChar

variable {M N R : Type*} [CommMonoid M] [CommMonoid N] [CommMonoidWithZero R]

/-- Multiplicative characters of `M × N` are pairs of multiplicative characters of `M` and `N`:
the pair `(χ₁, χ₂)` gives the character `(m, n) ↦ χ₁ m * χ₂ n`. -/
noncomputable def coprodEquiv : MulChar M R × MulChar N R ≃* MulChar (M × N) R :=
  ((mulEquivToUnitHom.prodCongr mulEquivToUnitHom).trans MonoidHom.coprodEquiv).trans
    ((MulEquiv.monoidHomCongrLeft MulEquiv.prodUnits.symm).trans mulEquivToUnitHom.symm)

/-- The character attached to a pair `(χ₁, χ₂)` sends `(m, n)` to `χ₁ m * χ₂ n`. -/
@[simp]
theorem coprodEquiv_apply (χ : MulChar M R × MulChar N R) (x : M × N) :
    coprodEquiv χ x = χ.1 x.1 * χ.2 x.2 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp [coprodEquiv, MulEquiv.prodUnits]
  · rw [map_nonunit _ hx]
    rcases not_and_or.1 (mt Prod.isUnit_iff.2 hx) with h | h
    · rw [map_nonunit _ h, zero_mul]
    · rw [map_nonunit _ h, mul_zero]

/-- The first character attached to `χ` is its restriction `m ↦ χ (m, 1)`. -/
@[simp]
theorem coprodEquiv_symm_apply_fst (χ : MulChar (M × N) R) (m : M) :
    (coprodEquiv.symm χ).1 m = χ (m, 1) := by
  have h := coprodEquiv_apply (coprodEquiv.symm χ) (m, 1)
  rw [MulEquiv.apply_symm_apply] at h
  simpa using h.symm

/-- The second character attached to `χ` is its restriction `n ↦ χ (1, n)`. -/
@[simp]
theorem coprodEquiv_symm_apply_snd (χ : MulChar (M × N) R) (n : N) :
    (coprodEquiv.symm χ).2 n = χ (1, n) := by
  have h := coprodEquiv_apply (coprodEquiv.symm χ) (1, n)
  rw [MulEquiv.apply_symm_apply] at h
  simpa only [MulChar.map_one, one_mul] using h.symm

end MulChar
