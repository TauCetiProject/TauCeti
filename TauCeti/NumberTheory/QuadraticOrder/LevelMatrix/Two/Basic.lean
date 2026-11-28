/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix
import TauCeti.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Quadratic multiplication matrices at level two

The unit group of a quadratic algebra modulo `2` has order `1`, `2` or `3`, in the split,
ramified and inert cases respectively (`card_periodMatrixGroup_zmod_two`). These are the orders
of the corresponding multiplication matrix groups, before quotienting by the image of the integral
units. When the constant coefficient is `-1`, every residue unit lifts to an integral unit, for any
integral linear coefficient (`Int.units_map_zmod_two_neg_one_surjective`).
In particular, every residue unit in the Gaussian and Eisenstein integer algebras lifts to an
integral unit (`units_map_zmod_two_gaussian_surjective`,
`units_map_zmod_two_eisenstein_surjective`). Thus their unit images cannot be replaced by the
scalar signs, which both reduce to the identity at level two.

For the reduced global-unit subgroups `unitPeriodMatrixSubgroup a b 2`, see
`TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Two.Quotient`.

## References

* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §§2, 4.
-/

public section

namespace QuadraticAlgebra

/-- The order of the quadratic multiplication matrix group over `𝔽₂`: two in the ramified
case, one in the split case, and three in the inert case. -/
theorem card_periodMatrixGroup_zmod_two (a b : ZMod 2) :
    Nat.card (periodMatrixGroup a b) = if b = 0 then 2 else if a = 0 then 1 else 3 := by
  rw [card_periodMatrixGroup_eq_card_norm_units, Nat.card_eq_fintype_card]
  fin_cases a <;> fin_cases b <;> decide

/-- Every unit modulo `2` in an integral quadratic algebra with constant coefficient `-1`
lifts to an integral unit. The lifts are `1`, `omegaUnit b`, and `(omegaUnit b)²`. -/
theorem _root_.Int.units_map_zmod_two_neg_one_surjective (b : ℤ) :
    Function.Surjective (Units.map
      (mapRingHom (Int.castRingHom (ZMod 2)) (-1) b).toMonoidHom) := by
  intro u
  have hu := isUnit_iff_norm_isUnit.mp u.isUnit
  have key : ∀ c t s : ZMod 2, IsUnit (t ^ 2 + c * t * s + s ^ 2) →
      (t = 1 ∧ s = 0) ∨ (t = 0 ∧ s = 1) ∨ (c = 1 ∧ t = 1 ∧ s = 1) := by decide
  have hn : IsUnit (u.val.re ^ 2 + (b : ZMod 2) * u.val.re * u.val.im +
      u.val.im ^ 2) := by
    simpa [norm_def, sq, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using hu
  have hωval := mapRingHom_omega (Int.castRingHom (ZMod 2)) (-1) b
  rcases key _ _ _ hn with h | h | h
  · refine ⟨1, Units.ext ?_⟩
    ext <;> simp [h.1, h.2]
  · refine ⟨TauCeti.QuadraticAlgebra.omegaUnit b, Units.ext ?_⟩
    ext <;> simp [hωval, h.1, h.2]
  · refine ⟨TauCeti.QuadraticAlgebra.omegaUnit b ^ 2, Units.ext ?_⟩
    ext <;> simp [hωval, h.1, h.2.1, h.2.2, sq, ZMod.neg_eq_self_mod_two]

/-- Every unit modulo `2` in the Gaussian integer algebra lifts to an integral unit. -/
theorem units_map_zmod_two_gaussian_surjective :
    Function.Surjective (Units.map
      (mapRingHom (Int.castRingHom (ZMod 2)) (-1) 0).toMonoidHom) :=
  Int.units_map_zmod_two_neg_one_surjective 0

/-- Every unit modulo `2` in the Eisenstein integer algebra lifts to an integral unit. The
three residues are represented by `1`, `ω`, and `ω² = ω - 1`. -/
theorem units_map_zmod_two_eisenstein_surjective :
    Function.Surjective (Units.map
      (mapRingHom (Int.castRingHom (ZMod 2)) (-1) 1).toMonoidHom) :=
  Int.units_map_zmod_two_neg_one_surjective 1

end QuadraticAlgebra
