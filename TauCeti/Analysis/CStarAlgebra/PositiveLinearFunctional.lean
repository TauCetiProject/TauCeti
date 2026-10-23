/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional

/-!
# Positive functionals in the weak-* dual of a C⋆-algebra

For a functional `φ : WeakDual ℂ A` on a C⋆-algebra that is nonnegative on nonnegative elements,
this file records the norm facts about positive functionals in the form used on the weak-* dual.

* `WeakDual.monotone_toStrongDual_of_map_nonneg`: `φ` is monotone.
* `WeakDual.tendsto_approximateUnit_norm_of_map_nonneg`: along the approximate unit, `φ` tends
  to its norm.
* `WeakDual.norm_toStrongDual_eq_map_one_of_map_nonneg`: if `A` is unital, the norm of `φ` is
  `φ 1`.

These are Mathlib's `ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm` and
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`, restated for `WeakDual ℂ A`.
-/

public section

open Filter
open scoped ComplexOrder Topology

namespace WeakDual

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- A functional that is nonnegative on nonnegative elements is monotone. -/
theorem monotone_toStrongDual_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Monotone (toStrongDual φ) :=
  (monotone_iff_map_nonneg _).mpr fun a ha => (hφ a ha).trans_eq (toStrongDual_apply φ a).symm

/-- Along the approximate unit, a functional that is nonnegative on nonnegative elements tends
to its norm. -/
theorem tendsto_approximateUnit_norm_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Tendsto (fun e => φ e) (CStarAlgebra.approximateUnit A) (𝓝 (‖toStrongDual φ‖ : ℂ)) := by
  simpa using (ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm
    (CStarAlgebra.increasingApproximateUnit A)).mp (monotone_toStrongDual_of_map_nonneg hφ)

end NonUnital

/-- On a unital C⋆-algebra, the norm of a functional that is nonnegative on nonnegative elements
is its value at `1`. -/
theorem norm_toStrongDual_eq_map_one_of_map_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {φ : WeakDual ℂ A} (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (‖toStrongDual φ‖ : ℂ) = φ 1 := by
  simpa using ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp
    (monotone_toStrongDual_of_map_nonneg hφ)

end WeakDual
