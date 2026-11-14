/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Conj
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

The completed function of the dual card is the reflection `conj ∘ Λ ∘ conj`, so the one-sided
count of the dual card counts the zeros of `Λ` below the real axis. At a nonnegative height the
symmetric count is therefore the one-sided count of the card, plus that of its dual, plus the
zeros on the real segment `[0, 1]`. When the divisor of `Λ` is invariant under conjugation and
`Λ` has no zero on `[0, 1]`, this is `N±(T) = 2 N(T)`.

The definitions use Mathlib's divisor convention: a function not meromorphic on its stated
domain has divisor zero, as does an infinite-order germ. To interpret these as actual zero
counts, use the completed function of a record with meromorphic continuation and not
identically zero. No boundary nonvanishing or finite-growth assumption is needed here.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§9.2–9.4.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §16.
-/

public section

open Set Complex Filter Topology ComplexConjugate
open scoped Pointwise

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

/-! ### Reflection across the real axis and the symmetric count -/

/-- The completed function of the dual card has at `s` the divisor that the completed function
has at `conj s`. -/
theorem divisor_dual_completed (s : ℂ) :
    MeromorphicOn.divisor d.dual.completed univ s =
      MeromorphicOn.divisor d.completed univ (conj s) := by
  rw [dual_completed, ← divisor_conj_conj, preimage_univ]

/-- The zero count of the dual card over a region is the zero count of the card over the
reflected region. -/
theorem zeroCount_dual_completed (R : Set ℂ) :
    zeroCount d.dual.completed univ R = zeroCount d.completed univ (conj ⁻¹' R) := by
  rw [dual_completed, ← zeroCount_conj_conj, preimage_univ]

/-- **The dual card counts the zeros below the real axis.** The one-sided count of the dual card
at height `T` is the number of zeros of the completed function in `0 ≤ Re s ≤ 1`,
`-T ≤ Im s < 0`, counted with multiplicity. -/
theorem zeroCountingFunction_dual (T : ℝ) :
    d.dual.zeroCountingFunction T = zeroCount d.completed univ (Icc 0 1 ×ℂ Ico (-T) 0) := by
  rw [zeroCountingFunction_def, zeroCount_dual_completed, preimage_conj_reProdIm, neg_Ioc,
    neg_zero]

/-- The symmetric count of the dual card is the symmetric count of the card, since its region is
invariant under conjugation. -/
@[simp]
theorem symmetricZeroCountingFunction_dual (T : ℝ) :
    d.dual.symmetricZeroCountingFunction T = d.symmetricZeroCountingFunction T := by
  rw [symmetricZeroCountingFunction_def, symmetricZeroCountingFunction_def,
    zeroCount_dual_completed, preimage_conj_reProdIm, neg_Icc, neg_neg]

/-- **The symmetric count splits at the real axis.** At a nonnegative height `T`, the symmetric
count is the number of zeros with `0 < Im s ≤ T`, plus the number with `-T ≤ Im s < 0`, which is
the one-sided count of the dual card, plus the zeros on the real segment `[0, 1]`. -/
theorem symmetricZeroCountingFunction_eq_add {T : ℝ} (hT : 0 ≤ T) :
    d.symmetricZeroCountingFunction T = d.zeroCountingFunction T +
      d.dual.zeroCountingFunction T + d.symmetricZeroCountingFunction 0 := by
  -- Split the heights `[-T, T]` into `[-T, 0)`, `{0}` and `(0, T]`, and the count accordingly.
  have hfin {t : Set ℝ} (ht : t ⊆ Icc (-T) T) :=
    zeroCount_support_finite_of_subset_reProdIm_Icc (f := d.completed) (subset_univ _)
      (reProdIm_subset_iff.2 (prod_mono (le_refl (Icc (0 : ℝ) 1)) ht))
  have hunion (t₁ t₂ : Set ℝ) : Icc (0 : ℝ) 1 ×ℂ (t₁ ∪ t₂) = Icc 0 1 ×ℂ t₁ ∪ Icc 0 1 ×ℂ t₂ := by
    ext z
    simp only [mem_reProdIm, mem_union, and_or_left]
  have hlow : Ico (-T) 0 ⊆ Icc (-T) T := Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT)
  have hzero : Icc (0 : ℝ) 0 ⊆ Icc (-T) T := Icc_subset_Icc (neg_nonpos.2 hT) hT
  have hup : Ioc 0 T ⊆ Icc (-T) T := Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl)
  rw [symmetricZeroCountingFunction_def, symmetricZeroCountingFunction_def, neg_zero,
    zeroCountingFunction_def, zeroCountingFunction_dual,
    ← Ico_union_Icc_eq_Icc (neg_nonpos.2 hT) hT, ← Icc_union_Ioc_eq_Icc le_rfl hT, hunion,
    zeroCount_union _ (hfin hlow) (hfin (union_subset hzero hup)), hunion,
    zeroCount_union _ (hfin hzero) (hfin hup)]
  · omega
  · rw [disjoint_left]
    rintro z ⟨-, -, h₁⟩ ⟨-, h₂, -⟩
    linarith
  · rw [disjoint_left]
    rintro z ⟨-, -, h₁⟩ ⟨-, ⟨h₂, -⟩ | ⟨h₂, -⟩⟩ <;> linarith

/-- If the divisor of the completed function is invariant under conjugation, the dual card has
the same one-sided count. -/
theorem zeroCountingFunction_dual_eq_of_divisor_conj
    (hconj : ∀ s, MeromorphicOn.divisor d.completed univ (conj s) =
      MeromorphicOn.divisor d.completed univ s) (T : ℝ) :
    d.dual.zeroCountingFunction T = d.zeroCountingFunction T := by
  simp only [zeroCountingFunction_def, zeroCount_def, divisor_dual_completed, hconj]

/-- **`N±(T) = 2 N(T) + N±(0)` for a divisor invariant under conjugation.** At a nonnegative
height, the zeros below the real axis are the reflections of those above it, with the same
multiplicities. -/
theorem symmetricZeroCountingFunction_eq_two_mul_add
    (hconj : ∀ s, MeromorphicOn.divisor d.completed univ (conj s) =
      MeromorphicOn.divisor d.completed univ s) {T : ℝ} (hT : 0 ≤ T) :
    d.symmetricZeroCountingFunction T =
      2 * d.zeroCountingFunction T + d.symmetricZeroCountingFunction 0 := by
  rw [d.symmetricZeroCountingFunction_eq_add hT,
    d.zeroCountingFunction_dual_eq_of_divisor_conj hconj, two_mul]

/-- **`N±(T) = 2 N(T)`.** If the divisor of the completed function is invariant under
conjugation and the completed function has no zero on the real segment `[0, 1]`, the symmetric
count is twice the one-sided count at every height. -/
theorem symmetricZeroCountingFunction_eq_two_mul
    (hconj : ∀ s, MeromorphicOn.divisor d.completed univ (conj s) =
      MeromorphicOn.divisor d.completed univ s)
    (hreal : ∀ x ∈ Icc (0 : ℝ) 1, MeromorphicOn.divisor d.completed univ x ≤ 0) (T : ℝ) :
    d.symmetricZeroCountingFunction T = 2 * d.zeroCountingFunction T := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [hT, hT.le]
  have h0 : d.symmetricZeroCountingFunction 0 = 0 := by
    refine (d.symmetricZeroCountingFunction_eq_zero_iff 0).2 fun z hz ↦ Int.toNat_eq_zero.2 ?_
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz.2)
    rw [hz']
    exact hreal z.re hz.1
  rw [d.symmetricZeroCountingFunction_eq_two_mul_add hconj hT, h0, add_zero]

end TauCeti.LFunctions.AnalyticLFunctionData
