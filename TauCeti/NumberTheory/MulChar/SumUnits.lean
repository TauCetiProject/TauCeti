/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums twisted by a multiplicative character over the units

A multiplicative character vanishes off the units, so a sum `∑ₐ χ(a) f(a)` over a finite monoid
is the same sum over its units (`MulChar.sum_mul_eq_sum_units`). On the units, the restriction
`(χ : M →* R).comp (Units.coeHom M)` of `χ` is evaluated by `MulChar.coe_comp_coeHom_apply`.
-/

public section

namespace MulChar

variable {M : Type*} [CommMonoid M]

/-- The restriction of a multiplicative character to the units, as a monoid homomorphism, takes
the values of the character. -/
@[simp] theorem coe_comp_coeHom_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar M R)
    (u : Mˣ) :
    ((χ : M →* R).comp (Units.coeHom M)) u = χ u :=
  rfl

/-- A sum twisted by a multiplicative character only sees the units:
`∑ₐ χ(a) f(a) = ∑ᵤ χ(u) f(u)`. -/
theorem sum_mul_eq_sum_units {R : Type*} [CommSemiring R] [Fintype M] [Fintype Mˣ]
    (χ : MulChar M R) (f : M → R) :
    ∑ a, χ a * f a = ∑ u : Mˣ, χ u * f u := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨Units.val, Units.val_injective⟩))
    fun a _ ha ↦ ?_, Finset.sum_map]
  · rfl
  · have ha' : ¬ IsUnit a := fun ⟨u, hu⟩ ↦ ha (by simp [← hu])
    simp [χ.map_nonunit ha']

end MulChar
