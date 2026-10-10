/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.FieldTheory.IsRealClosed.Real
import Mathlib.Algebra.Order.Ring.Abs

/-! # Nonnegative square roots in real closed fields

Every nonnegative element of an ordered real closed field has a unique nonnegative square root.
`nonnegSqrt` chooses this root, and on `ℝ` it agrees with `Real.sqrt`.

## Main results

* `exists_nonneg_sq` proves the property for ordered real closed fields.
* `nonnegSqrt` chooses the root using real closedness; `nonnegSqrt_nonneg`,
  `sq_nonnegSqrt`, and `nonnegSqrt_unique` characterize it.
* `nonnegSqrt_real_eq_sqrt` identifies the chosen root on `ℝ` with `Real.sqrt`.
-/

public section

namespace TauCeti.RealClosure

section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Two nonnegative square roots of the same element are equal. -/
theorem nonnegSqrt_unique {a r s : R} (hr0 : 0 ≤ r) (hr : r ^ 2 = a)
    (hs0 : 0 ≤ s) (hs : s ^ 2 = a) : r = s := by
  apply (sq_eq_sq₀ hr0 hs0).mp
  rw [hr, hs]

end

section

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Every nonnegative element of an ordered real closed field has a nonnegative square root. -/
theorem exists_nonneg_sq [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, hr⟩ := IsRealClosed.exists_eq_pow_of_nonneg ha (n := 2) (by decide)
  exact ⟨|r|, abs_nonneg r, by simpa [sq_abs] using hr.symm⟩

/-- The nonnegative square root of a nonnegative element in a real closed field. -/
noncomputable def nonnegSqrt [IsRealClosed R] {a : R} (ha : 0 ≤ a) : R :=
  Classical.choose (exists_nonneg_sq ha)

/-- The selected square root is nonnegative. -/
@[simp]
theorem nonnegSqrt_nonneg
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    0 ≤ nonnegSqrt ha :=
  (Classical.choose_spec (exists_nonneg_sq ha)).1

/-- The selected square root squares to its input. -/
@[simp]
theorem sq_nonnegSqrt
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    (nonnegSqrt ha) ^ 2 = a :=
  (Classical.choose_spec (exists_nonneg_sq ha)).2

/-- The chosen nonnegative square root on `ℝ` agrees with `Real.sqrt`. -/
theorem nonnegSqrt_real_eq_sqrt
    {a : ℝ} (ha : 0 ≤ a) : nonnegSqrt ha = Real.sqrt a := by
  apply nonnegSqrt_unique
  · exact nonnegSqrt_nonneg ha
  · exact sq_nonnegSqrt ha
  · exact Real.sqrt_nonneg a
  · exact Real.sq_sqrt ha

end

end TauCeti.RealClosure
