/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Rectangle
public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Height-counting functions of completed L-functions

`AnalyticLFunctionData.zeroCountingFunction d T` counts zeros of the completed function
in `0 ≤ Re s ≤ 1`, `0 < Im s ≤ T`, with their positive divisor multiplicities.
`AnalyticLFunctionData.symmetricZeroCountingFunction d T` instead uses `-T ≤ Im s ≤ T`,
including real zeros when `0 ≤ T`. Poles do not contribute to either count. These are counts of the
completion, not of the uncompleted function's trivial zeros.

Both functions are monotone and locally constant from the right at every height, hence
right-continuous even at ordinates of zeros. The one-sided count is zero at nonpositive heights.
Splitting in height gives exact increments without double-counting the shared edge.
Compactness of the containing rectangles ensures finite divisor support at every height.

The definitions use Mathlib's divisor convention: a function not meromorphic on its stated
domain has divisor zero, as does an infinite-order germ. To interpret these as actual zero
counts, use the completed function of a record with meromorphic continuation and not
identically zero. No boundary nonvanishing or finite-growth assumption is needed here.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.2–9.4.
-/

public section

open Set Complex Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- Zeros of the completed function in the closed critical strip with
`0 < Im s ≤ T`, counted with positive divisor multiplicity. -/
noncomputable def zeroCountingFunction (d : AnalyticLFunctionData) (T : ℝ) : ℕ :=
  zeroCount d.completed univ (Icc 0 1 ×ℂ Ioc 0 T)

/-- Zeros of the completed function in the closed critical strip with
`-T ≤ Im s ≤ T`, counted with positive divisor multiplicity. Real zeros are included when
`0 ≤ T`. -/
noncomputable def symmetricZeroCountingFunction (d : AnalyticLFunctionData) (T : ℝ) : ℕ :=
  zeroCount d.completed univ (Icc 0 1 ×ℂ Icc (-T) T)

variable (d : AnalyticLFunctionData)

/-- The one-sided counting function is the zero count on a half-open rectangle. -/
theorem zeroCountingFunction_def (T : ℝ) :
    d.zeroCountingFunction T = zeroCount d.completed univ (Icc 0 1 ×ℂ Ioc 0 T) := (rfl)

/-- The symmetric counting function is the zero count on a closed rectangle. -/
theorem symmetricZeroCountingFunction_def (T : ℝ) :
    d.symmetricZeroCountingFunction T =
      zeroCount d.completed univ (Icc 0 1 ×ℂ Icc (-T) T) := (rfl)

/-- At nonpositive heights the one-sided counting region is empty. -/
@[simp] theorem zeroCountingFunction_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    d.zeroCountingFunction T = 0 := by
  simp only [zeroCountingFunction_def]
  rw [reProdIm_eq_empty.mpr (Or.inr (Ioc_eq_empty_of_le hT)), zeroCount_empty]

/-- At negative heights the symmetric counting region is empty. Unlike the one-sided
count, the symmetric count need not vanish at height zero. -/
@[simp] theorem symmetricZeroCountingFunction_of_neg {T : ℝ} (hT : T < 0) :
    d.symmetricZeroCountingFunction T = 0 := by
  simp only [symmetricZeroCountingFunction_def]
  rw [reProdIm_eq_empty.mpr (Or.inr (Icc_eq_empty_of_lt (by linarith))), zeroCount_empty]

/-- At height zero the symmetric count counts precisely the zeros on the real segment. -/
theorem symmetricZeroCountingFunction_zero :
    d.symmetricZeroCountingFunction 0 = zeroCount d.completed univ (Icc 0 1 ×ℂ {0}) := by
  simp [symmetricZeroCountingFunction_def]

/-- The one-sided count does not decrease as the height increases. At positive heights,
zeros on the top edge are counted. -/
theorem monotone_zeroCountingFunction : Monotone d.zeroCountingFunction := by
  intro S T hST
  simp only [zeroCountingFunction_def]
  exact zeroCount_reProdIm_Ioc_le hST (subset_univ _)

/-- The symmetric count does not decrease as the height increases, including at negative
heights. -/
theorem monotone_symmetricZeroCountingFunction : Monotone d.symmetricZeroCountingFunction := by
  intro S T hST
  simp only [symmetricZeroCountingFunction_def]
  exact zeroCount_reProdIm_Icc_le (neg_le_neg hST) hST (subset_univ _)

/-- Exact splitting at nonnegative heights `0 ≤ S ≤ T`. Zeros at height `S` belong to the
lower piece when `0 < S`, and are excluded from both pieces when `S = 0`. No nonvanishing
assumption is needed on the splitting edge. -/
theorem zeroCountingFunction_eq_add {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    d.zeroCountingFunction T = d.zeroCountingFunction S +
      zeroCount d.completed univ (Icc 0 1 ×ℂ Ioc S T) := by
  simp only [zeroCountingFunction_def]
  exact zeroCount_reProdIm_Ioc_eq_add hS hST (subset_univ _)

/-- The one-sided count stabilizes immediately to the right of every height, even when
that height itself carries a zero. -/
theorem eventuallyEq_zeroCountingFunction_nhdsGE (T : ℝ) :
    d.zeroCountingFunction =ᶠ[𝓝[≥] T] fun _ ↦ d.zeroCountingFunction T := by
  simpa only [Filter.EventuallyEq, zeroCountingFunction_def] using
    (eventuallyEq_zeroCount_reProdIm_Ioc_nhdsGE (f := d.completed) T (subset_univ _))

/-- The one-sided counting function is right-continuous at every real height. -/
theorem continuousWithinAt_zeroCountingFunction_Ici (T : ℝ) :
    ContinuousWithinAt d.zeroCountingFunction (Ici T) T := by
  rw [funext d.zeroCountingFunction_def]
  exact continuousWithinAt_zeroCount_reProdIm_Ioc_Ici T (subset_univ _)

/-- The one-sided count at height zero vanishes. -/
theorem zeroCountingFunction_zero : d.zeroCountingFunction 0 = 0 :=
  d.zeroCountingFunction_of_nonpos le_rfl

/-- The one-sided count vanishes exactly when the rectangle has no positive divisor
multiplicities. This characterization does not identify zeros with pointwise values. -/
theorem zeroCountingFunction_eq_zero_iff (T : ℝ) :
    d.zeroCountingFunction T = 0 ↔
      ∀ z ∈ Icc 0 1 ×ℂ Ioc 0 T, (MeromorphicOn.divisor d.completed univ z).toNat = 0 := by
  rw [zeroCountingFunction_def]
  exact zeroCount_eq_zero_iff (zeroCount_support_finite_of_subset_reProdIm_Icc (subset_univ _)
    (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩))

/-- The symmetric count vanishes exactly when its closed rectangle has no positive divisor
multiplicities. Real-axis multiplicities are included for nonnegative heights. -/
theorem symmetricZeroCountingFunction_eq_zero_iff (T : ℝ) :
    d.symmetricZeroCountingFunction T = 0 ↔
      ∀ z ∈ Icc 0 1 ×ℂ Icc (-T) T, (MeromorphicOn.divisor d.completed univ z).toNat = 0 := by
  rw [symmetricZeroCountingFunction_def]
  exact zeroCount_eq_zero_iff
    (zeroCount_support_finite_of_subset_reProdIm_Icc (subset_univ _) Subset.rfl)

/-- The symmetric count stabilizes immediately to the right of every height. -/
theorem eventuallyEq_symmetricZeroCountingFunction_nhdsGE (T : ℝ) :
    d.symmetricZeroCountingFunction =ᶠ[𝓝[≥] T] fun _ ↦ d.symmetricZeroCountingFunction T := by
  simpa only [Filter.EventuallyEq, symmetricZeroCountingFunction_def] using
    (eventuallyEq_zeroCount_reProdIm_Icc_neg_nhdsGE (f := d.completed) T (subset_univ _))

/-- The symmetric counting function is right-continuous at every real height. -/
theorem continuousWithinAt_symmetricZeroCountingFunction_Ici (T : ℝ) :
    ContinuousWithinAt d.symmetricZeroCountingFunction (Ici T) T := by
  rw [funext d.symmetricZeroCountingFunction_def]
  exact continuousWithinAt_zeroCount_reProdIm_Icc_neg_Ici T (subset_univ _)

end TauCeti.LFunctions.AnalyticLFunctionData
