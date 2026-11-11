/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Scalar bounds for the continuous-functional-calculus square root

In a unital algebra with a continuous functional calculus for self-adjoint elements, the order
between a self-adjoint element `a` and a scalar `algebraMap ℝ A r` is read off the spectrum of `a`.
Since the real square root is monotone, the square root `CFC.sqrt a` then satisfies the same bound
with `√r` in place of `r`:

* `a ≤ r` gives `√a ≤ √r`,
* `r ≤ a` gives `√r ≤ √a`.

These are the two scalar cases of the operator monotonicity of the square root
(`CFC.monotone_sqrt`), which Mathlib proves only in C⋆-algebras. The scalar cases need no
C⋆-structure, so they apply, for instance, to real matrices with the Loewner order, which are not a
complex C⋆-algebra. They are the estimates that keep a map built from square roots of congruences
inside an order interval `[α, β]` of scalars.

## Main statements

* `CFC.sqrt_le_algebraMap`: if `a ≤ algebraMap ℝ A r`, then
  `CFC.sqrt a ≤ algebraMap ℝ A √r`.
* `CFC.algebraMap_le_sqrt`: if `algebraMap ℝ A r ≤ a`, then
  `algebraMap ℝ A √r ≤ CFC.sqrt a`.
-/

public section

namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [StarModule ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
  [IsSemitopologicalRing A] [T2Space A]

/-- An element bounded above by the scalar `r` has square root bounded above by the scalar `√r`.
No nonnegativity hypothesis is needed: the square root of an element that is not nonnegative is
`0`. -/
theorem sqrt_le_algebraMap {a : A} {r : ℝ} (h : a ≤ algebraMap ℝ A r) :
    sqrt a ≤ algebraMap ℝ A √r := by
  by_cases ha : 0 ≤ a
  · rw [sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
    exact cfc_le_algebraMap _ _ a fun x hx ↦
      Real.sqrt_le_sqrt ((le_algebraMap_iff_spectrum_le (ha := ha.isSelfAdjoint)).1 h x hx)
  · rw [sqrt_eq_cfc, cfc_apply_of_not_predicate a ha]
    exact algebraMap_nonneg A (Real.sqrt_nonneg r)

/-- An element bounded below by the scalar `r` has square root bounded below by the scalar `√r`.
No nonnegativity hypothesis is needed: `√r = 0` for `r ≤ 0`. -/
theorem algebraMap_le_sqrt {a : A} {r : ℝ} (h : algebraMap ℝ A r ≤ a) :
    algebraMap ℝ A √r ≤ sqrt a := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Real.sqrt_eq_zero'.2 hr]
  have ha : 0 ≤ a := (algebraMap_nonneg A hr.le).trans h
  rw [sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  exact algebraMap_le_cfc _ _ a fun x hx ↦
    Real.sqrt_le_sqrt ((algebraMap_le_iff_le_spectrum (ha := ha.isSelfAdjoint)).1 h x hx)

end CFC
