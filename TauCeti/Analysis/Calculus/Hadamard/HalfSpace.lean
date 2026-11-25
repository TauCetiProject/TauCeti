/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.Analysis.Calculus.ParametricIntegral.Segment
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Hadamard division on a half-space

Let `ℓ` be a continuous linear functional on a real normed space `E` and `v` a vector with
`ℓ v = 1`, so that `{ℓ ≥ 0}` is a closed half-space with boundary hyperplane `{ℓ = 0}`; it has
unique derivatives (`ContinuousLinearMap.uniqueDiffOn_halfSpace`). A function `f` that is `C^(k+1)`
on `{ℓ ≥ 0}` near a point `q` of the hyperplane and vanishes on the hyperplane there is divisible by
`ℓ`: near `q`, `f = ℓ • g` on the half-space for a function `g` that is `C^k` on the half-space
(`TauCeti.exists_contDiffOn_eq_smul_of_eq_zero`). The quotient is the average
`g y = ∫₀¹ ∂_v f(y - (1 - τ) ℓ(y) v) dτ` of the derivative of `f` in the direction `v` along the
segment from the foot `y - ℓ(y) v` on the hyperplane to `y`. These segments stay in the half-space,
so only the derivative of `f` within the half-space enters, and no smooth extension of `f` across
the hyperplane is needed. This is Hadamard's lemma (`ContDiff.sub_eq_hadamardFactor_apply`) in a
form that applies in the half-space charts of a manifold with boundary.
-/

public section

noncomputable section

open Set Metric Filter MeasureTheory AffineMap
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

namespace TauCeti

/-- Radii for Hadamard division: for `w ∈ ball q δ` and `0 ≤ a < ε`, the foot `w - ℓ(w) v` of `w`
moved by `a v` lies in `{ℓ ≥ 0} ∩ ball q r`, and `ℓ < ε` on `ball q δ`. -/
private theorem exists_radii_mapsTo {ℓ : E →L[ℝ] ℝ} {v : E} (hv : ℓ v = 1) {q : E}
    (hq : ℓ q = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∃ ε > 0, (∀ y ∈ ball q δ, ℓ y < ε) ∧
      MapsTo (fun p : ℝ × E ↦ (p.2 - ℓ p.2 • v) + p.1 • v) (Ico 0 ε ×ˢ ball q δ)
        ({y | 0 ≤ ℓ y} ∩ ball q r) := by
  set C : ℝ := 1 + (2 * ‖ℓ‖ + 1) * ‖v‖
  set δ : ℝ := r / (C + 1)
  have hδ : 0 < δ := by positivity
  have hδC : δ * C < r := by
    have h1 : δ * C < δ * (C + 1) := by nlinarith
    rwa [div_mul_cancel₀ _ (by positivity)] at h1
  set ε : ℝ := (‖ℓ‖ + 1) * δ
  have hℓ (y : E) : ℓ y ≤ ‖ℓ‖ * ‖y - q‖ := by
    have := ℓ.le_opNorm (y - q)
    rw [map_sub, hq, sub_zero] at this
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)
  refine ⟨δ, hδ, ε, by positivity, fun y hy ↦ ?_, ?_⟩
  · have h2 : ‖y - q‖ < δ := mem_ball_iff_norm.1 hy
    nlinarith [hℓ y, norm_nonneg ℓ]
  rintro ⟨a, w⟩ ⟨⟨ha0, haε⟩, hw⟩
  refine ⟨by simpa [hv] using ha0, ?_⟩
  rw [mem_ball, dist_eq_norm] at hw ⊢
  have hfoot : (w - ℓ w • v) + a • v - q = ((w - q) - ℓ (w - q) • v) + a • v := by
    simp only [map_sub, hq, sub_zero]
    abel
  rw [hfoot]
  have h1 : ‖(w - q) - ℓ (w - q) • v‖ ≤ (1 + ‖ℓ‖ * ‖v‖) * ‖w - q‖ :=
    calc ‖(w - q) - ℓ (w - q) • v‖ ≤ ‖w - q‖ + ‖ℓ (w - q)‖ * ‖v‖ := by
          rw [← norm_smul]; exact norm_sub_le _ _
      _ ≤ ‖w - q‖ + ‖ℓ‖ * ‖w - q‖ * ‖v‖ := by gcongr; exact ℓ.le_opNorm (w - q)
      _ = (1 + ‖ℓ‖ * ‖v‖) * ‖w - q‖ := by ring
  have h2 : ‖a • v‖ ≤ ε * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_right haε.le (norm_nonneg v)
  have h3 : (1 + ‖ℓ‖ * ‖v‖) * ‖w - q‖ < (1 + ‖ℓ‖ * ‖v‖) * δ :=
    mul_lt_mul_of_pos_left hw (by positivity)
  calc ‖(w - q) - ℓ (w - q) • v + a • v‖ ≤ ‖(w - q) - ℓ (w - q) • v‖ + ‖a • v‖ :=
        norm_add_le _ _
    _ < (1 + ‖ℓ‖ * ‖v‖) * δ + ε * ‖v‖ := by linarith
    _ = δ * C := by ring
    _ < r := hδC

/-- **Hadamard's lemma along the segment from the foot.** If `f` is `C¹` on a convex set `S` with
unique derivatives containing `y` and its foot `y - ℓ(y) v`, and `f` vanishes at the foot, then
`f y = ℓ(y) • ∫₀¹ ∂_v f(y - ℓ(y) v + τ ℓ(y) v) dτ`, with the derivative taken within `S`. -/
private theorem eq_smul_intervalIntegral_fderivWithin {ℓ : E →L[ℝ] ℝ} {v : E} {S : Set E}
    (hSc : Convex ℝ S) (hSu : UniqueDiffOn ℝ S) {f : E → F} (hf : ContDiffOn ℝ 1 f S) {y : E}
    (hy : y ∈ S) (hc : y - ℓ y • v ∈ S) (h0 : f (y - ℓ y • v) = 0) :
    f y = ℓ y • ∫ τ in (0 : ℝ)..1, fderivWithin ℝ f S (y - ℓ y • v + (τ * ℓ y) • v) v := by
  have hderiv (z : E) (hz : z ∈ S) : HasFDerivWithinAt f (fderivWithin ℝ f S z) S z :=
    (hf.differentiableOn_one z hz).hasFDerivWithinAt
  have hFTC := (hSc.starConvex hc).sub_eq_intervalIntegral_lineMap_apply
    (hf.fderivWithin hSu (m := 0) le_rfl).continuousOn hderiv hy
  have hyc : y - (y - ℓ y • v) = ℓ y • v := by simp
  rw [h0, sub_zero, hyc] at hFTC
  rw [hFTC, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun τ _ ↦ ?_
  simp only [map_smul]
  simp [lineMap_apply, hyc, smul_smul, add_comm]

/-- Hadamard division on a half-space, at a point `q` of the boundary hyperplane, given a vector
`v` with `ℓ v = 1`. -/
private theorem exists_contDiffOn_eq_smul_of_apply_eq_zero {k : ℕ∞} {ℓ : E →L[ℝ] ℝ} {v : E}
    (hv : ℓ v = 1) {q : E} (hq : ℓ q = 0) {s : Set E} (hs : s ∈ 𝓝 q) {f : E → F}
    (hf : ContDiffOn ℝ (k + 1) f ({y | 0 ≤ ℓ y} ∩ s)) (h0 : ∀ y ∈ s, ℓ y = 0 → f y = 0) :
    ∃ g : E → F, ∃ t, IsOpen t ∧ q ∈ t ∧ ContDiffOn ℝ k g ({y | 0 ≤ ℓ y} ∩ t) ∧
      ∀ y ∈ {y | 0 ≤ ℓ y} ∩ t, f y = ℓ y • g y := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  set H : Set E := {y | 0 ≤ ℓ y}
  set S : Set E := H ∩ ball q r
  have hHc : Convex ℝ H := (convex_Ici 0).linear_preimage ℓ.toLinearMap
  have hHu : UniqueDiffOn ℝ H := ℓ.uniqueDiffOn_halfSpace 0
  have hSc : Convex ℝ S := hHc.inter (convex_ball q r)
  have hSu : UniqueDiffOn ℝ S := hHu.inter isOpen_ball
  have hfS : ContDiffOn ℝ (k + 1) f S := hf.mono (inter_subset_inter_right _ hrs)
  obtain ⟨δ, hδ, ε, hε, hℓε, hΦD⟩ := exists_radii_mapsTo hv hq hr
  set Φ : ℝ × E → E := fun p ↦ (p.2 - ℓ p.2 • v) + p.1 • v
  set D : Set (ℝ × E) := Ico 0 ε ×ˢ ball q δ
  -- The derivative of `f` in the direction `v`, at the points `Φ (a, w)`.
  let φ : ℝ × E → F := fun p ↦ fderivWithin ℝ f S (Φ p) v
  have hφ : ContDiffOn ℝ k φ D :=
    ((hfS.fderivWithin hSu le_rfl).comp (by fun_prop) hΦD).clm_apply contDiffOn_const
  set t : Set E := ball q δ
  have hmemD {y : E} (hy : y ∈ H ∩ t) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : (τ * ℓ y, y) ∈ D :=
    ⟨⟨mul_nonneg hτ.1 hy.1, lt_of_le_of_lt (mul_le_of_le_one_left hy.1 hτ.2) (hℓε y hy.2)⟩, hy.2⟩
  refine ⟨fun y ↦ ∫ τ in (0 : ℝ)..1, φ (τ * ℓ y, y), t, isOpen_ball, mem_ball_self hδ, ?_, ?_⟩
  · -- Smoothness of the average, by differentiation under the integral sign.
    have hF : ContDiffOn ℝ k (fun p : E × ℝ ↦ φ (p.2 * ℓ p.1, p.1))
        ((H ∩ t) ×ˢ Icc (0 : ℝ) 1) :=
      hφ.comp (by fun_prop) fun p hp ↦ hmemD hp.1 hp.2
    exact (Convex.contDiffOn_parametric_primitive (hHc.inter (convex_ball q δ)) (convex_Icc 0 1)
      (hHu.inter isOpen_ball) (left_mem_Icc.2 zero_le_one) hF).comp
      (contDiffOn_id.prodMk (contDiffOn_const (c := (1 : ℝ))))
      fun y hy ↦ ⟨hy, right_mem_Icc.2 zero_le_one⟩
  · -- The fundamental theorem of calculus along the segment from the foot of `y` to `y`.
    intro y hy
    have hc : y - ℓ y • v ∈ S := by
      have hΦc : Φ (0, y) = y - ℓ y • v := by simp [Φ]
      exact hΦc ▸ hΦD (show ((0 : ℝ), y) ∈ D from ⟨⟨le_rfl, hε⟩, hy.2⟩)
    have hyS : y ∈ S := by
      have hΦy : Φ (1 * ℓ y, y) = y := by simp [Φ]
      exact hΦy ▸ hΦD (hmemD hy (right_mem_Icc.2 zero_le_one))
    exact eq_smul_intervalIntegral_fderivWithin hSc hSu (hfS.of_le le_add_self) hyS hc
      (h0 _ (hrs hc.2) (by simp [hv]))

/-- **Hadamard division on a half-space.** If `f` is `C^(k+1)` on the half-space `{ℓ ≥ 0}` near
`q` and vanishes on the hyperplane `{ℓ = 0}` near `q`, then on the half-space near `q`,
`f = ℓ • g` for a function `g` that is `C^k` on the half-space. -/
theorem exists_contDiffOn_eq_smul_of_eq_zero {k : ℕ∞} {ℓ : E →L[ℝ] ℝ} {q : E} {s : Set E}
    (hs : s ∈ 𝓝 q) {f : E → F} (hf : ContDiffOn ℝ (k + 1) f ({y | 0 ≤ ℓ y} ∩ s))
    (h0 : ∀ y ∈ s, ℓ y = 0 → f y = 0) :
    ∃ g : E → F, ∃ t, IsOpen t ∧ q ∈ t ∧ ContDiffOn ℝ k g ({y | 0 ≤ ℓ y} ∩ t) ∧
      ∀ y ∈ {y | 0 ≤ ℓ y} ∩ t, f y = ℓ y • g y := by
  have hqs : q ∈ interior s := mem_interior_iff_mem_nhds.2 hs
  rcases lt_trichotomy (ℓ q) 0 with hq | hq | hq
  · -- Below the hyperplane the half-space misses a neighbourhood of `q`.
    have hempty : {y | 0 ≤ ℓ y} ∩ {y | ℓ y < 0} = ∅ :=
      eq_empty_of_forall_notMem fun y (hy : 0 ≤ ℓ y ∧ ℓ y < 0) ↦ not_le.2 hy.2 hy.1
    refine ⟨0, {y | ℓ y < 0}, isOpen_lt ℓ.continuous continuous_const, hq, ?_, ?_⟩
    · rw [hempty]
      exact contDiffOn_empty
    · rw [hempty]
      exact fun y hy ↦ hy.elim
  · by_cases hℓ : ℓ = 0
    · refine ⟨0, interior s, isOpen_interior, hqs, contDiffOn_const, fun y hy ↦ ?_⟩
      simp [h0 y (interior_subset hy.2) (by simp [hℓ]), hℓ]
    · obtain ⟨w, hw⟩ := ContinuousLinearMap.exists_ne_zero hℓ
      exact exists_contDiffOn_eq_smul_of_apply_eq_zero (v := (ℓ w)⁻¹ • w)
        (by simp [inv_mul_cancel₀ hw]) hq hs hf h0
  · -- Above the hyperplane, divide by `ℓ`.
    refine ⟨fun y ↦ (ℓ y)⁻¹ • f y, interior s ∩ {y | 0 < ℓ y},
      isOpen_interior.inter (isOpen_lt continuous_const ℓ.continuous), ⟨hqs, hq⟩, ?_,
      fun y hy ↦ (smul_inv_smul₀ hy.2.2.ne' _).symm⟩
    exact (ℓ.contDiff.contDiffOn.inv fun y (hy : y ∈ {y | 0 ≤ ℓ y} ∩ (interior s ∩ {y | 0 < ℓ y})) ↦
      hy.2.2.ne').smul
      (hf.of_succ.mono fun y hy ↦ ⟨hy.1, interior_subset hy.2.1⟩)

end TauCeti
