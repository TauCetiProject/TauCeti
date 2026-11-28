/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
public import TauCeti.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Bounds through a compact domain embedding

Operators on a common domain `D` embedded into `H` by `ι : D →L[𝕜] H` are compared through `ι` via
estimates of the form `‖(A - B) x‖ ≤ c * ‖ι x‖`. This file collects the reusable bounds of this
kind for shifted differences, compact-interval extensions of continuous paths, reparametrizations,
`Set.IccExtend`, and `TauCeti.smoothSegmentPath`.

## Main declarations

* `TauCeti.WeakDerivStep.norm_sub_smul_sub_apply_le` and
  `TauCeti.WeakDerivStep.exists_norm_sub_smul_sub_apply_le`: shifted differences
  `(A₁ - c₁ • ι) - (A₂ - c₂ • ι)` are bounded through `ι`.
* `TauCeti.WeakDerivStep.exists_forall_mem_Icc_norm_sub_apply_le_of_ae`: almost everywhere bounds on
  bounded windows pass to every time of every compact interval for a continuous path.
* `TauCeti.WeakDerivStep.exists_ae_norm_comp_sub_apply_le`,
  `TauCeti.WeakDerivStep.exists_ae_norm_IccExtend_sub_apply_le`, and
  `TauCeti.WeakDerivStep.exists_norm_sub_apply_le`: bounds for continuous reparametrizations,
  `Set.IccExtend`, and single times.
* `TauCeti.WeakDerivStep.norm_smoothSegmentPath_sub_apply_le` and
  `TauCeti.WeakDerivStep.exists_ae_norm_smoothSegmentPath_sub_apply_le`: bounds for the smooth
  segment path `TauCeti.smoothSegmentPath`.
-/

public section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory Set
open scoped Topology

section ShiftedDifference

variable {𝕜 D H : Type*} [NormedField 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- If `A₁ - B` and `A₂ - B` are bounded through `ι`, then `(A₁ - c₁ • ι) - (A₂ - c₂ • ι)` is
bounded through `ι` with constant `C₁ + C₂ + ‖c₂ - c₁‖`. -/
theorem norm_sub_smul_sub_apply_le {ι A₁ A₂ B : D →L[𝕜] H} {C₁ C₂ : ℝ}
    (h₁ : ∀ x, ‖(A₁ - B) x‖ ≤ C₁ * ‖ι x‖) (h₂ : ∀ x, ‖(A₂ - B) x‖ ≤ C₂ * ‖ι x‖)
    (c₁ c₂ : 𝕜) (x : D) :
    ‖((A₁ - c₁ • ι) - (A₂ - c₂ • ι)) x‖ ≤ (C₁ + C₂ + ‖c₂ - c₁‖) * ‖ι x‖ := by
  have heq : ((A₁ - c₁ • ι) - (A₂ - c₂ • ι)) x =
      (A₁ - B) x - (A₂ - B) x + (c₂ - c₁) • ι x := by
    simp only [sub_apply, smul_apply]
    module
  rw [heq, add_mul, add_mul, ← norm_smul]
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (h₁ x) (h₂ x)))
    le_rfl)

/-- Existential form of `TauCeti.WeakDerivStep.norm_sub_smul_sub_apply_le`. -/
theorem exists_norm_sub_smul_sub_apply_le {ι A₁ A₂ B : D →L[𝕜] H}
    (h₁ : ∃ C₁, ∀ x, ‖(A₁ - B) x‖ ≤ C₁ * ‖ι x‖)
    (h₂ : ∃ C₂, ∀ x, ‖(A₂ - B) x‖ ≤ C₂ * ‖ι x‖) (c₁ c₂ : 𝕜) :
    ∃ C, ∀ x, ‖((A₁ - c₁ • ι) - (A₂ - c₂ • ι)) x‖ ≤ C * ‖ι x‖ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂ + ‖c₂ - c₁‖, norm_sub_smul_sub_apply_le hC₁ hC₂ c₁ c₂⟩

end ShiftedDifference

section CompactWindows

variable {𝕜 D H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {ι : D →L[𝕜] H} {A : ℝ → D →L[𝕜] H}

/-- For a continuous path, an almost everywhere bound of `A s - B` through `ι` on bounded windows
holds at every time of every compact interval. -/
theorem exists_forall_mem_Icc_norm_sub_apply_le_of_ae {μ : Measure ℝ} [μ.IsOpenPosMeasure]
    {B : D →L[𝕜] H} (hA : Continuous A)
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂μ, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) (R : ℝ) :
    ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - B) x‖ ≤ c * ‖ι x‖ := by
  obtain ⟨c, hc⟩ := hc (R + 1)
  refine ⟨c, fun r hr ↦ ?_⟩
  have hP : IsClosed {s | ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_le
      (((hA.sub continuous_const).clm_apply continuous_const).norm) continuous_const
  have hr' : r ∈ Ioo (-(R + 1)) (R + 1) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  exact hP.closure_subset (isOpen_Ioo.subset_closure_of_ae_le (t := {s | ∀ x, _}) hc hr')

/-- If `A r - B` is bounded through `ι` for `r` in compact intervals, then so is `A (φ s) - B'` for
`s` in bounded windows, for a continuous reparametrization `φ` and any `B'` with `B' - B`
bounded through `ι`. -/
theorem exists_ae_norm_comp_sub_apply_le {μ : Measure ℝ} {B B' : D →L[𝕜] H}
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - B) x‖ ≤ c * ‖ι x‖)
    (hB' : ∃ c, ∀ x, ‖(B' - B) x‖ ≤ c * ‖ι x‖) {φ : ℝ → ℝ} (hφ : Continuous φ) (T : ℝ) :
    ∃ c, ∀ᵐ s ∂μ, s ∈ Ioo (-T) T → ∀ x, ‖(A (φ s) - B') x‖ ≤ c * ‖ι x‖ := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
    ((isCompact_Icc (a := -T) (b := T)).image hφ).isBounded
  obtain ⟨c, hc⟩ := hb R
  obtain ⟨c', hc'⟩ := hB'
  refine ⟨c + c', Eventually.of_forall fun s hs x ↦ ?_⟩
  have hφs : φ s ∈ Icc (-R) R := by
    simpa [Real.norm_eq_abs, abs_le] using hR _ (mem_image_of_mem φ (Ioo_subset_Icc_self hs))
  rw [show (A (φ s) - B') x = (A (φ s) - B) x - (B' - B) x by simp, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hc _ hφs x) (hc' x))

/-- If `A r - B` is bounded through `ι` for `r` in compact intervals, then `Set.IccExtend` of `A`
on `[a, b]` satisfies the bounded-window bound through `ι` against any `B'` with `B' - B`
bounded through `ι`. -/
theorem exists_ae_norm_IccExtend_sub_apply_le {μ : Measure ℝ} {B B' : D →L[𝕜] H}
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - B) x‖ ≤ c * ‖ι x‖)
    (hB' : ∃ c, ∀ x, ‖(B' - B) x‖ ≤ c * ‖ι x‖) {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    ∃ c, ∀ᵐ s ∂μ, s ∈ Ioo (-T) T →
      ∀ x, ‖(IccExtend hab ((Icc a b).domRestrict A) s - B') x‖ ≤ c * ‖ι x‖ := by
  simpa only [IccExtend_apply, domRestrict_apply] using
    exists_ae_norm_comp_sub_apply_le hb hB' (by fun_prop : Continuous fun s : ℝ ↦ max a (min b s)) T

/-- A bound through `ι` of `A r - B` on compact intervals gives one at each single time. -/
theorem exists_norm_sub_apply_le {B : D →L[𝕜] H}
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - B) x‖ ≤ c * ‖ι x‖) (r : ℝ) :
    ∃ c, ∀ x, ‖(A r - B) x‖ ≤ c * ‖ι x‖ :=
  (hb |r|).imp fun _ hc ↦ hc r ⟨neg_abs_le r, le_abs_self r⟩

end CompactWindows

section SmoothSegment

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- If `B - B₀` is bounded through `ι`, then so is `smoothSegmentPath B₀ B s - B`, uniformly in
`s`. -/
theorem norm_smoothSegmentPath_sub_apply_le {ι B₀ B : D →L[ℝ] H} {c : ℝ}
    (hc : ∀ x, ‖(B - B₀) x‖ ≤ c * ‖ι x‖) (s : ℝ) (x : D) :
    ‖(smoothSegmentPath B₀ B s - B) x‖ ≤ c * ‖ι x‖ := by
  have heq : (smoothSegmentPath B₀ B s - B) x =
      (1 - Real.smoothTransition s) • -((B - B₀) x) := by
    simp only [smoothSegmentPath_def, sub_apply, add_apply, smul_apply]
    module
  rw [heq, norm_smul, norm_neg, Real.norm_of_nonneg
    (sub_nonneg.2 (Real.smoothTransition.le_one s))]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (sub_le_self _ (Real.smoothTransition.nonneg s)) |>.trans (hc x)

/-- If `B - B₀` is bounded through `ι`, then `smoothSegmentPath B₀ B s - B` satisfies the
bounded-window bound through `ι`. -/
theorem exists_ae_norm_smoothSegmentPath_sub_apply_le {μ : Measure ℝ} {ι B₀ B : D →L[ℝ] H}
    (hbdd : ∃ c, ∀ x, ‖(B - B₀) x‖ ≤ c * ‖ι x‖) (T : ℝ) :
    ∃ c, ∀ᵐ s ∂μ, s ∈ Ioo (-T) T → ∀ x, ‖(smoothSegmentPath B₀ B s - B) x‖ ≤ c * ‖ι x‖ :=
  hbdd.imp fun _ hc ↦ ae_of_all _ fun s _ x ↦ norm_smoothSegmentPath_sub_apply_le hc s x

end SmoothSegment

end TauCeti.WeakDerivStep
