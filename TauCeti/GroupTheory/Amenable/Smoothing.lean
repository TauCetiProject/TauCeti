/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Linfty
public import TauCeti.GroupTheory.Amenable.Convolution

/-!
# Smoothed extensions of invariant means to Haar `L∞`

For a mean `m` on `UCB G` and an integrable kernel `h`, `m.smoothing h` is the continuous
functional `φ ↦ m (h ⋆ φ)` on Haar `L∞`. It is positive when `h` is nonnegative and normalized
when `h` has integral one. If `m` is left invariant, its value on the class of a `UCB` function
`f` is `(∫ h) * m f`. Thus every nonnegative integral-one kernel gives a norm-one positive
extension of `m` to `L∞`.

These are extensions as linear functionals: this file does not assert that they are invariant
on all of `L∞`, or that they are independent of the kernel. The restriction identity is the
starting point for comparing those smoothed functionals.

No σ-finiteness, countability, or separation hypothesis is imposed on the locally compact group.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, proof of
  Theorem G.3.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace TauCeti.Mean

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

/-- The continuous functional on Haar `L∞` obtained by smoothing with `h` and applying `m`.
For a nonnegative integral-one kernel and an invariant `m`, it is a positive normalized
extension of `m`; invariance on `L∞` is not part of this definition. -/
def smoothing (m : Mean G) (h : Lp ℝ 1 μ) : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  m.toContinuousLinearMap.comp (Lp.convolutionUCB h)

@[simp]
theorem smoothing_apply (m : Mean G) (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    m.smoothing h φ = m (Lp.convolutionUCB h φ) := by
  simp [smoothing]

/-- The norm of the smoothed functional is at most the `L¹` norm of the kernel. -/
theorem norm_smoothing_le (m : Mean G) (h : Lp ℝ 1 μ) : ‖m.smoothing h‖ ≤ ‖h‖ := by
  calc
    ‖m.smoothing h‖ ≤ ‖m.toContinuousLinearMap‖ * ‖Lp.convolutionUCB h‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖h‖ := by simpa using Lp.norm_convolutionUCB_le h

/-- The smoothed functional depends continuously on its kernel in the `L¹` norm. -/
theorem continuous_smoothing (m : Mean G) :
    Continuous (smoothing m : Lp ℝ 1 μ → Lp ℝ ∞ μ →L[ℝ] ℝ) := by
  exact ((ContinuousLinearMap.compL ℝ (Lp ℝ ∞ μ) (UCB G) ℝ)
    m.toContinuousLinearMap).continuous.comp Lp.continuous_convolutionUCB

/-- A nonnegative kernel gives a positive smoothed functional. -/
theorem smoothing_nonneg (m : Mean G) {h : Lp ℝ 1 μ} (hh : 0 ≤ h)
    {φ : Lp ℝ ∞ μ} (hφ : 0 ≤ φ) : 0 ≤ m.smoothing h φ := by
  simpa using m.toPositiveLinearMap.map_nonneg (Lp.convolutionUCB_nonneg hh hφ)

/-- The positive linear functional obtained by smoothing with a nonnegative kernel and
applying `m`. Normalization of the kernel is not required. -/
def smoothingPositive (m : Mean G) {h : Lp ℝ 1 μ} (hh : 0 ≤ h) :
    Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (m.smoothing h).toLinearMap (fun _ hφ => m.smoothing_nonneg hh hφ)

/-- The positive and continuous smoothed functionals have the same values. -/
@[simp]
theorem smoothingPositive_apply (m : Mean G) {h : Lp ℝ 1 μ} (hh : 0 ≤ h)
    (φ : Lp ℝ ∞ μ) : m.smoothingPositive hh φ = m.smoothing h φ := by
  rfl

/-- The value on the constant one is the integral of the kernel. -/
@[simp high]
theorem smoothing_linftyOne (m : Mean G) (h : Lp ℝ 1 μ) :
    m.smoothing h linftyOne = ∫ y, h y ∂μ := by
  simp [map_smul]

/-- An invariant mean applied after smoothing a `UCB` function gives its original value,
multiplied by the integral of the kernel. The kernel need not be nonnegative. -/
theorem IsLeftInvariant.smoothing_toLpTop {m : Mean G} (hm : m.IsLeftInvariant)
    (h : Lp ℝ 1 μ) (f : UCB G) :
    m.smoothing h (BoundedContinuousFunction.toLpTop μ ℝ (f : G →ᵇ ℝ)) =
      (∫ y, h y ∂μ) * m f := by
  simpa only [smoothing_apply] using hm.apply_convolutionUCB_toLpTop h f

/-- A nonnegative integral-one kernel gives a smoothed functional of norm one. -/
theorem norm_smoothing (m : Mean G) {h : Lp ℝ 1 μ} (hh : 0 ≤ h)
    (h₁ : ∫ y, h y ∂μ = 1) : ‖m.smoothing h‖ = 1 := by
  have hn : ‖h‖ = 1 := by
    rw [L1.norm_eq_integral_norm]
    exact (integral_congr_ae ((Lp.coeFn_nonneg h).2 hh |>.mono
      fun _ hy => Real.norm_of_nonneg hy)).trans h₁
  refine (norm_smoothing_le m h |>.trans_eq hn).antisymm ?_
  have hu : ‖(linftyOne : Lp ℝ ∞ μ)‖ ≤ 1 := by
    rw [← BoundedContinuousFunction.toLpTop_one μ]
    simpa using BoundedContinuousFunction.norm_toLpTop_le μ (𝕜 := ℝ) (1 : G →ᵇ ℝ)
  calc
    1 = ‖m.smoothing h linftyOne‖ := by rw [smoothing_linftyOne, h₁, norm_one]
    _ ≤ ‖m.smoothing h‖ * ‖(linftyOne : Lp ℝ ∞ μ)‖ := (m.smoothing h).le_opNorm _
    _ ≤ ‖m.smoothing h‖ := mul_le_of_le_one_right (norm_nonneg _) hu

/-- For an invariant mean, restriction of the normalized positive smoothed functional back to
`UCB` recovers the original mean. This is an extension statement, not an invariance statement
on all of `L∞`. -/
theorem IsLeftInvariant.ofLpTop_smoothing {m : Mean G} (hm : m.IsLeftInvariant)
    {h : Lp ℝ 1 μ} (hh : 0 ≤ h) (h₁ : ∫ y, h y ∂μ = 1) :
    Mean.ofLpTop (m.smoothingPositive hh)
      (by simpa only [smoothingPositive_apply] using (m.smoothing_linftyOne h).trans h₁) = m := by
  apply Mean.ext
  intro f
  rw [ofLpTop_apply, smoothingPositive_apply, hm.smoothing_toLpTop, h₁, one_mul]

end TauCeti.Mean
