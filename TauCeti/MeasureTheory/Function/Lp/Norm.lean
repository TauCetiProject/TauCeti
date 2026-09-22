/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Norm inequalities in `Lᵖ` spaces

This file contains norm estimates for `Lᵖ` functions derived from almost-everywhere pointwise
bounds.

## Main declaration

* `TauCeti.Lp.norm_le_add_of_ae_norm_le`: an `Lᵖ` norm bound from pointwise domination by a
  two-term linear combination.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- The norm of an `Lᵖ` function dominated pointwise by a two-term combination of two other
`Lᵖ` functions obeys the same bound in norm. -/
theorem Lp.norm_le_add_of_ae_norm_le {alpha F G H : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H] {m : Measure alpha}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp F q m} {g : Lp G q m} {h : Lp H q m} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hle : ∀ᵐ z ∂m, ‖f z‖ ≤ a * ‖g z‖ + b * ‖h z‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  obtain ⟨A, hAnorm, hAcoe⟩ : ∃ A : Lp ℝ q m, ‖A‖ = ‖g‖ ∧ ∀ᵐ z ∂m, A z = ‖g z‖ :=
    ⟨(Lp.memLp g).norm.toLp _, by rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def],
      (Lp.memLp g).norm.coeFn_toLp⟩
  obtain ⟨B, hBnorm, hBcoe⟩ : ∃ B : Lp ℝ q m, ‖B‖ = ‖h‖ ∧ ∀ᵐ z ∂m, B z = ‖h z‖ :=
    ⟨(Lp.memLp h).norm.toLp _, by rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def],
      (Lp.memLp h).norm.coeFn_toLp⟩
  calc ‖f‖ ≤ ‖a • A + b • B‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [hle, hAcoe, hBcoe, Lp.coeFn_add (a • A) (b • B), Lp.coeFn_smul a A,
          Lp.coeFn_smul b B] with z hz hA hB hadd hsA hsB
        rw [hadd, Pi.add_apply, hsA, hsB, Pi.smul_apply, Pi.smul_apply, hA, hB, smul_eq_mul,
          smul_eq_mul, Real.norm_of_nonneg (add_nonneg (mul_nonneg ha (norm_nonneg _))
            (mul_nonneg hb (norm_nonneg _)))]
        exact hz
    _ ≤ ‖a • A‖ + ‖b • B‖ := norm_add_le _ _
    _ = a * ‖g‖ + b * ‖h‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hAnorm, hBnorm]

end TauCeti
