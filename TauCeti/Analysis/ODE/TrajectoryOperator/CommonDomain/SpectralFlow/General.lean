/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Neg
public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.RegularCrossings
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SpectralFlow.ShiftPath
import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Homotopy
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Perturbation
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Bounds
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.InvertiblePath
import TauCeti.MeasureTheory.Function.Lp.SmoothSegmentPath
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.LocallyConstant.Preconnected
import TauCeti.Topology.Order.ProjIcc

/-!
# The general Robbin–Salamon index theorem over a compactly embedded domain

Let `ι : D →L[ℝ] H` be a compact operator from a Banach space into a real Hilbert space, and let
`A : ℝ → D →L[ℝ] H` be a continuous path of `ι`-symmetric operators
(`⟪A s x, ι y⟫ = ⟪ι x, A s y⟫`), converging to invertible operators `Bbot` and `Btop` at `-∞` and
`∞`, and differing from `Btop` on every bounded interval by operators bounded through `ι`. Then the
trajectory operator `D_A u = (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`
(`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`) is Fredholm
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`).

This file proves the general **Robbin–Salamon spectral flow index theorem**:

* `ind(∂ₛ + A) = SF(A; a, b)` for every interval `[a, b]` outside which `A` is invertible
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_domainSpectralFlow`), and hence
  for all `a` far enough to the left and all `b` far enough to the right
  (`TauCeti.WeakDerivStep.eventually_index_familyDomainTrajectoryOperator_eq_domainSpectralFlow`).
* In the convention `∂ₛ - A` with coefficient `-A`, `ind(∂ₛ - A) = -SF(A; a, b)`
  (`index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow` and
  `eventually_index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow` in
  `TauCeti.WeakDerivStep`).
* When every crossing `t` (where `ker A t ≠ ⊥`) is regular, the index equals the sum of the
  crossing-form signatures
  (`index_familyDomainTrajectoryOperator_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm` in
  `TauCeti.WeakDerivStep`).

**Proof (staircase homotopy).** By localization
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend`) and limit
invariance (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`), the index of `D_A`
equals `modelIndex ι (A a) (A b)`, the index along the smooth segment `TauCeti.smoothSegmentPath`
from `A a` to `A b`. For any `t ∈ [a, b]` and any admissible shift `c` with `(A t - c • ι)`
invertible, consider the staircase defect

`Ψ t c = modelIndex ι (A a) (A t - c • ι) - SF(A; a, t) - SF(σ ↦ A t - (σ * c) • ι; 0, 1)`.

1. Along a fixed time `t`, `Ψ t c₁ = Ψ t c₂` for any two admissible shifts `c₁, c₂`: catenation of
   `modelIndex` isolates `modelIndex ι (A t - c₁ • ι) (A t - c₂ • ι)`, which equals
   `SF(σ ↦ A t - ((1 - σ) * c₁ + σ * c₂) • ι; 0, 1)` by the shift-path index formula
   (`eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow` in
   `TauCeti.WeakDerivStep`), and homotopy invariance around `[0, 1] × [0, 1]` relates the three
   shift segments.
2. Along a short subinterval `[u, v]` carrying a single admissible shift `c` for `A t - c • ι`,
   `Ψ u c = Ψ v c`: the segment `A u - c • ι ⇝ A v - c • ι` has index zero by
   `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_path`, while homotopy
   invariance on `[0, 1] × [u, v]` for `G σ t = A t - (σ * c) • ι` matches the jump in `SF(A; u, v)`
   to the difference of the vertical shift-segment spectral flows.

Choosing an admissible shift at each `t ∈ [a, b]` makes `t ↦ Ψ t (c t)` locally constant on `[a, b]`
by a Lebesgue-number radius (`TauCeti.apply_eq_of_forall_sub_lt`). Evaluating at `t = a, b` with
`c = 0` yields `modelIndex ι (A a) (A b) = SF(A; a, b)`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

section Helpers

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : D →L[ℝ] H}

/-! ### Model indices -/

variable [CompleteSpace D] [CompleteSpace H]

/-- The index of the trajectory operator along `TauCeti.smoothSegmentPath B₀ B`. -/
private def modelIndex (ι B₀ B : D →L[ℝ] H) : ℤ :=
  (familyDomainTrajectoryOperator (p := 2) ι (smoothSegmentPathL (μ := μ₀) B₀ B)).index

private theorem modelIndex_eq_add (hι : IsCompactOperator ι) {B₁ B₂ B₃ : D →L[ℝ] H}
    (hSymm₁ : ∀ x y, ⟪B₁ x, ι y⟫_ℝ = ⟪ι x, B₁ y⟫_ℝ) (hB₁ : B₁.IsInvertible)
    (hSymm₂ : ∀ x y, ⟪B₂ x, ι y⟫_ℝ = ⟪ι x, B₂ y⟫_ℝ) (hB₂ : B₂.IsInvertible)
    (hSymm₃ : ∀ x y, ⟪B₃ x, ι y⟫_ℝ = ⟪ι x, B₃ y⟫_ℝ) (hB₃ : B₃.IsInvertible)
    (h₁₂ : ∃ c, ∀ x, ‖(B₂ - B₁) x‖ ≤ c * ‖ι x‖)
    (h₂₃ : ∃ c, ∀ x, ‖(B₃ - B₂) x‖ ≤ c * ‖ι x‖) :
    modelIndex ι B₁ B₃ = modelIndex ι B₁ B₂ + modelIndex ι B₂ B₃ := by
  obtain ⟨c₁₂, hc₁₂⟩ := h₁₂
  obtain ⟨c₂₃, hc₂₃⟩ := h₂₃
  have h₁₃ : ∃ c, ∀ x, ‖(B₃ - B₁) x‖ ≤ c * ‖ι x‖ := ⟨c₁₂ + c₂₃, fun x ↦ by
    have hsplit : (B₃ - B₁) x = (B₃ - B₂) x + (B₂ - B₁) x := by simp
    rw [hsplit, add_comm c₁₂ c₂₃, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hc₂₃ x) (hc₁₂ x))⟩
  have h₂₃' : ∃ c, ∀ x, ‖(B₂ - B₃) x‖ ≤ c * ‖ι x‖ :=
    ⟨c₂₃, fun x ↦ by simpa only [sub_apply, norm_sub_rev] using hc₂₃ x⟩
  exact index_familyDomainTrajectoryOperator_eq_add hι hSymm₁ hB₁ hSymm₂ hB₂ hSymm₃ hB₃ h₂₃'
    (smoothSegmentPathL_ae B₁ B₂) (eventuallyEq_smoothSegmentPath_atBot B₁ B₂).tendsto
    (eventuallyEq_smoothSegmentPath_atTop B₁ B₂).tendsto
    (exists_ae_norm_smoothSegmentPath_sub_apply_le ⟨c₁₂, hc₁₂⟩)
    (smoothSegmentPathL_ae B₂ B₃) (eventuallyEq_smoothSegmentPath_atBot B₂ B₃).tendsto
    (eventuallyEq_smoothSegmentPath_atTop B₂ B₃).tendsto
    (exists_ae_norm_smoothSegmentPath_sub_apply_le ⟨c₂₃, hc₂₃⟩)
    (smoothSegmentPathL_ae B₁ B₃) (eventuallyEq_smoothSegmentPath_atBot B₁ B₃).tendsto
    (eventuallyEq_smoothSegmentPath_atTop B₁ B₃).tendsto
    (exists_ae_norm_smoothSegmentPath_sub_apply_le h₁₃)

private theorem modelIndex_sub_smul_eq_zero (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {u v c : ℝ}
    (huv : u ≤ v) (hinv : ∀ t ∈ Icc u v, (A t - c • ι).IsInvertible)
    (hbdd : ∀ t ∈ Icc u v, ∃ C, ∀ x, ‖(A t - A u) x‖ ≤ C * ‖ι x‖) :
    modelIndex ι (A u - c • ι) (A v - c • ι) = 0 := by
  have hmem (t : unitInterval) : Path.segment u v t ∈ Icc u v := by
    rw [← segment_eq_Icc huv, ← Path.range_segment]
    exact mem_range_self t
  let γ : Path (A u - c • ι) (A v - c • ι) := (Path.segment u v).map (hA.sub continuous_const)
  have hγbdd (t : unitInterval) : ∃ C, ∀ x, ‖(γ t - (A u - c • ι)) x‖ ≤ C * ‖ι x‖ := by
    obtain ⟨C, hC⟩ := hbdd (Path.segment u v t) (hmem t)
    exact ⟨C, fun x ↦ by simpa [γ] using hC x⟩
  have hvu : ∃ C, ∀ x, ‖((A v - c • ι) - (A u - c • ι)) x‖ ≤ C * ‖ι x‖ := by
    obtain ⟨C, hC⟩ := hbdd v (right_mem_Icc.2 huv)
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  exact index_familyDomainTrajectoryOperator_eq_zero_of_path hι γ
    (fun t x y ↦
      ContinuousLinearMap.inner_sub_ofReal_smul_apply_eq_inner_sub_ofReal_smul_apply
        (hSymm (Path.segment u v t) x y) c)
    (fun t ↦ hinv (Path.segment u v t) (hmem t)) hγbdd
    (smoothSegmentPathL_ae _ _) (eventuallyEq_smoothSegmentPath_atBot _ _).tendsto
    (eventuallyEq_smoothSegmentPath_atTop _ _).tendsto
    (exists_ae_norm_smoothSegmentPath_sub_apply_le hvu)

private theorem modelIndex_sub_smul (hι : IsCompactOperator ι) {B : D →L[ℝ] H}
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c₁ c₂ : ℝ}
    (hc₁ : (B - c₁ • ι).IsInvertible) (hc₂ : (B - c₂ • ι).IsInvertible) :
    modelIndex ι (B - c₁ • ι) (B - c₂ • ι) =
      domainSpectralFlow ι (fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι) 0 1 := by
  have hseg : smoothSegmentPath (B - c₁ • ι) (B - c₂ • ι) =
      fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι := by
    ext s x
    simp only [smoothSegmentPath_def, add_apply, smul_apply, sub_apply, smul_eq_mul]
    module
  have hall : ∀ᶠ ab in atBot ×ˢ atTop, modelIndex ι (B - c₁ • ι) (B - c₂ • ι) =
      domainSpectralFlow ι (fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι) ab.1 ab.2 := by
    refine eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow hι hSymm
      (contDiff_smoothSegmentPath (x := c₁) (y := c₂) (n := 0)).continuous
      (eventuallyEq_smoothSegmentPath_atBot c₁ c₂).tendsto
      (eventuallyEq_smoothSegmentPath_atTop c₁ c₂).tendsto hc₁ hc₂ _ ?_
    simpa only [← hseg] using smoothSegmentPathL_ae (B - c₁ • ι) (B - c₂ • ι)
  obtain ⟨⟨a, b⟩, hab, ha, hb⟩ :=
    (hall.and ((eventually_le_atBot 0).prod_mk (eventually_ge_atTop 1))).exists
  rw [hab]
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using
    domainSpectralFlow_sub_smul_smoothSegmentPath hι hSymm hc₁ hc₂ ha hb

/-! ### Staircase homotopy -/

private def staircaseDefect (ι : D →L[ℝ] H) (A : ℝ → D →L[ℝ] H) (a t c : ℝ) : ℤ :=
  modelIndex ι (A a) (A t - c • ι) - domainSpectralFlow ι A a t -
    domainSpectralFlow ι (fun σ ↦ A t - (σ * c) • ι) 0 1

private theorem staircaseDefect_zero (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (h₀ : ∀ t, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) (a t : ℝ) :
    staircaseDefect ι A a t 0 = modelIndex ι (A a) (A t) - domainSpectralFlow ι A a t := by
  have hsf0 : domainSpectralFlow ι (fun σ ↦ A t - (σ * 0) • ι) 0 1 = 0 :=
    domainSpectralFlow_eq_zero_of_forall_eq hι zero_le_one
      (by simpa using hSymm t) (by simpa using h₀ t) fun _ _ ↦ by simp
  rw [staircaseDefect, hsf0]
  simp only [zero_smul, sub_zero]

private theorem staircaseDefect_eq_of_isInvertible (hι : IsCompactOperator ι)
    {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H} (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖) {a t c₁ c₂ : ℝ}
    (ha : (A a).IsInvertible) (hc₁ : (A t - c₁ • ι).IsInvertible)
    (hc₂ : (A t - c₂ • ι).IsInvertible) :
    staircaseDefect ι A a t c₁ = staircaseDefect ι A a t c₂ := by
  have hpt := exists_norm_sub_apply_le hb
  have hm := modelIndex_eq_add hι (B₁ := A a) (B₂ := A t - c₁ • ι) (B₃ := A t - c₂ • ι)
    (hSymm a) ha
    (fun x y ↦
      ContinuousLinearMap.inner_sub_ofReal_smul_apply_eq_inner_sub_ofReal_smul_apply
        (hSymm t x y) c₁)
    hc₁
    (fun x y ↦
      ContinuousLinearMap.inner_sub_ofReal_smul_apply_eq_inner_sub_ofReal_smul_apply
        (hSymm t x y) c₂)
    hc₂
    (by simpa using exists_norm_sub_smul_sub_apply_le (hpt t) (hpt a) c₁ 0)
    (exists_norm_sub_smul_sub_apply_le (hpt t) (hpt t) c₂ c₁)
  have hseg := modelIndex_sub_smul hι (hSymm t) hc₁ hc₂
  have htri := domainSpectralFlow_sub_smul_add_domainSpectralFlow_sub_smul_eq hι (hSymm t)
    (c₂ := c₂) hc₁
  simp only [RCLike.ofReal_real_eq_id, id_eq] at htri
  simp only [staircaseDefect]
  linarith

private theorem staircaseDefect_eq_of_forall_isInvertible (hι : IsCompactOperator ι)
    {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H} (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖)
    (h₀ : ∀ t, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) {a u v c : ℝ} (hau : a ≤ u) (huv : u ≤ v)
    (ha : (A a).IsInvertible) (hinv : ∀ t ∈ Icc u v, (A t - c • ι).IsInvertible) :
    staircaseDefect ι A a u c = staircaseDefect ι A a v c := by
  have hpt := exists_norm_sub_apply_le hb
  have hu : u ∈ Icc u v := left_mem_Icc.2 huv
  have hv : v ∈ Icc u v := right_mem_Icc.2 huv
  have hm := modelIndex_eq_add hι (B₁ := A a) (B₂ := A u - c • ι) (B₃ := A v - c • ι)
    (hSymm a) ha
    (fun x y ↦
      ContinuousLinearMap.inner_sub_ofReal_smul_apply_eq_inner_sub_ofReal_smul_apply
        (hSymm u x y) c)
    (hinv u hu)
    (fun x y ↦
      ContinuousLinearMap.inner_sub_ofReal_smul_apply_eq_inner_sub_ofReal_smul_apply
        (hSymm v x y) c)
    (hinv v hv)
    (by simpa using exists_norm_sub_smul_sub_apply_le (hpt u) (hpt a) c 0)
    (exists_norm_sub_smul_sub_apply_le (hpt v) (hpt u) c c)
  have hm0 := modelIndex_sub_smul_eq_zero hι hA hSymm huv hinv fun t _ ↦ by
    simpa using exists_norm_sub_smul_sub_apply_le (hpt t) (hpt u) 0 0
  have hadd := domainSpectralFlow_add_adjacent_intervals hι hau huv hA.continuousOn
    (fun t _ ↦ hSymm t) fun t _ ↦ h₀ t
  have hsq := domainSpectralFlow_add_domainSpectralFlow_sub_smul_eq hι huv hA.continuousOn
    (fun t _ ↦ hSymm t) hinv
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  simp only [staircaseDefect]
  linarith

private theorem modelIndex_eq_domainSpectralFlow (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    {Btop : D →L[ℝ] H} (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBtop : Btop.IsInvertible)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖)
    {a b : ℝ} (hab : a ≤ b) (ha : (A a).IsInvertible) (hbInv : (A b).IsInvertible) :
    modelIndex ι (A a) (A b) = domainSpectralFlow ι A a b := by
  classical
  have h₀ (t : ℝ) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible := by
    obtain ⟨C, hC⟩ := exists_norm_sub_apply_le hb t
    simpa using ι.exists_isInvertible_ofReal_smul_sub_of_isInvertible_of_norm_sub_apply_le hι
      hBtop (hSymm t) hC
  obtain ⟨δ, hδ, hloc⟩ := ι.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub hι
    isCompact_Icc hA.continuousOn (fun t _ ↦ h₀ t) zero_lt_one
  let ψ (t : ℝ) : ℤ :=
    if h : ∃ c : ℝ, (A t - c • ι).IsInvertible then staircaseDefect ι A a t h.choose else 0
  have hconst := apply_eq_of_forall_sub_lt (f := ψ) hab hδ fun p q hap hpq hqb hlt ↦ by
    obtain ⟨c, -, hinv⟩ := hloc p ⟨hap, hpq.trans hqb⟩
    have hinv' (u : ℝ) (hu : u ∈ Icc p q) : (A u - c • ι).IsInvertible := by
      rw [ContinuousLinearMap.isInvertible_sub_comm]
      exact hinv u (Icc_subset_Icc hap hqb hu)
        (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]; linarith [hu.2])
    have hp : ∃ c' : ℝ, (A p - c' • ι).IsInvertible := ⟨c, hinv' p (left_mem_Icc.2 hpq)⟩
    have hq : ∃ c' : ℝ, (A q - c' • ι).IsInvertible := ⟨c, hinv' q (right_mem_Icc.2 hpq)⟩
    simp only [ψ, hp, hq, ↓reduceDIte]
    rw [staircaseDefect_eq_of_isInvertible hι hSymm hb ha hp.choose_spec
        (hinv' p (left_mem_Icc.2 hpq)),
      staircaseDefect_eq_of_forall_isInvertible hι hA hSymm hb h₀ hap hpq ha hinv',
      ← staircaseDefect_eq_of_isInvertible hι hSymm hb ha hq.choose_spec
        (hinv' q (right_mem_Icc.2 hpq))]
  have ha0 : ∃ c : ℝ, (A a - c • ι).IsInvertible := ⟨0, by simpa using ha⟩
  have hb0 : ∃ c : ℝ, (A b - c • ι).IsInvertible := ⟨0, by simpa using hbInv⟩
  have hψa : ψ a = 0 := by
    simp only [ψ, ha0, ↓reduceDIte]
    rw [staircaseDefect_eq_of_isInvertible (c₂ := 0) hι hSymm hb ha ha0.choose_spec
        (by simpa using ha),
      staircaseDefect_zero hι hSymm h₀ a a]
    have hm0 : modelIndex ι (A a) (A a) = 0 := by
      rw [modelIndex]
      exact index_familyDomainTrajectoryOperator_eq_zero hι (hSymm a) ha (smoothSegmentPathL_ae _ _)
        (eventuallyEq_smoothSegmentPath_atBot _ _).tendsto
        (eventuallyEq_smoothSegmentPath_atTop _ _).tendsto
        (exists_ae_norm_smoothSegmentPath_sub_apply_le ⟨0, fun _ ↦ by simp⟩)
    rw [hm0, domainSpectralFlow_self, sub_zero]
  have hψb : ψ b = modelIndex ι (A a) (A b) - domainSpectralFlow ι A a b := by
    simp only [ψ, hb0, ↓reduceDIte]
    rw [staircaseDefect_eq_of_isInvertible (c₂ := 0) hι hSymm hb ha hb0.choose_spec
        (by simpa using hbInv),
      staircaseDefect_zero hι hSymm h₀ a b]
  linarith [hconst, hψa, hψb]

end Helpers

/-! ### The index theorem -/

section Main

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}
  {A : ℝ → D →L[ℝ] H} {Bbot Btop : D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀}

/-- Reduction from a localized path to the smooth segment model between `A a` and `A b`. -/
private theorem index_familyDomainTrajectoryOperator_eq_modelIndex (hι : IsCompactOperator ι)
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {a b : ℝ}
    (hab : a ≤ b) (hInv : ∀ s ∉ Ioo a b, (A s).IsInvertible) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = modelIndex ι (A a) (A b) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_tendsto hA hbot htop
  have hb := exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc
  have hm : MemLp (IccExtend hab ((Icc a b).domRestrict A)) ∞ μ₀ :=
    memLp_top_of_bound hA.continuousOn.domRestrict.Icc_extend'.aestronglyMeasurable C
      (.of_forall fun s ↦ hC _)
  have hloc := index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend hι hA hSymm hab hInv
    hBbot hBtop hAL hbot htop hc hm.coeFn_toLp
  have hba : ∃ c, ∀ x, ‖(A b - A a) x‖ ≤ c * ‖ι x‖ := by
    simpa using exists_norm_sub_smul_sub_apply_le (exists_norm_sub_apply_le hb b)
      (exists_norm_sub_apply_le hb a) 0 0
  rw [hloc]
  exact index_familyDomainTrajectoryOperator_eq hι (hSymm a) (hInv a left_notMem_Ioo)
    (hSymm b) (hInv b right_notMem_Ioo) hm.coeFn_toLp
    (TauCeti.tendsto_IccExtend_atBot hab _) (TauCeti.tendsto_IccExtend_atTop hab _)
    (exists_ae_norm_IccExtend_sub_apply_le hb (exists_norm_sub_apply_le hb b) hab)
    (smoothSegmentPathL_ae (A a) (A b)) (eventuallyEq_smoothSegmentPath_atBot _ _).tendsto
    (eventuallyEq_smoothSegmentPath_atTop _ _).tendsto
    (exists_ae_norm_smoothSegmentPath_sub_apply_le hba)

/-- **The Robbin–Salamon index formula over a compactly embedded domain.** Let `ι : D →L[ℝ] H` be a
compact operator from a Banach space into a real Hilbert space, and let `A : ℝ → D →L[ℝ] H` be a
continuous path of `ι`-symmetric operators converging to invertible operators `Bbot` and `Btop` at
`-∞` and `∞`, differing from `Btop` on every bounded interval by operators bounded through `ι`. If
`A s` is invertible for every `s` outside `(a, b)`, with `a ≤ b`, then the Fredholm index of
`u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` equals the spectral flow
`TauCeti.domainSpectralFlow ι A a b`. -/
theorem index_familyDomainTrajectoryOperator_eq_domainSpectralFlow (hι : IsCompactOperator ι)
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {a b : ℝ}
    (hab : a ≤ b) (hInv : ∀ s ∉ Ioo a b, (A s).IsInvertible) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = domainSpectralFlow ι A a b := by
  rw [index_familyDomainTrajectoryOperator_eq_modelIndex hι hA hSymm hab hInv hBbot hBtop hAL hbot
      htop hc,
    modelIndex_eq_domainSpectralFlow hι hA hSymm hBtop
      (exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc) hab
      (hInv a left_notMem_Ioo) (hInv b right_notMem_Ioo)]

/-- **The Robbin–Salamon index formula for large intervals.** Under the hypotheses of
`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_domainSpectralFlow`, for every `a`
far enough to the left and every `b` far enough to the right, the index of `u ↦ (ι ∘ u)' + A u` is
`TauCeti.domainSpectralFlow ι A a b`. -/
theorem eventually_index_familyDomainTrajectoryOperator_eq_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        domainSpectralFlow ι A ab.1 ab.2 := by
  filter_upwards [ContinuousLinearMap.eventually_le_and_forall_notMem_Ioo_isInvertible
      hBbot hBtop hbot htop] with ⟨a, b⟩ ⟨hab, hinv⟩
  exact index_familyDomainTrajectoryOperator_eq_domainSpectralFlow hι hA hSymm hab hinv hBbot hBtop
    hAL hbot htop hc

/-- **The index of `∂ₛ - A` is minus the spectral flow of `A`.** Let `ι : D →L[ℝ] H` be compact,
and let `A` be a continuous path of `ι`-symmetric operators with invertible limits `Bbot` and `Btop`
at `±∞`, differing from `Btop` on bounded windows by operators bounded through `ι`, and invertible
outside `(a, b)` for `a ≤ b`. Then the index of `u ↦ (ι ∘ u)' - A u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`, whose coefficient is `-A`, is
`-TauCeti.domainSpectralFlow ι A a b`. -/
theorem index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {a b : ℝ} (hab : a ≤ b)
    (hInv : ∀ s ∉ Ioo a b, (A s).IsInvertible) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] fun s ↦ -A s)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = -domainSpectralFlow ι A a b := by
  have hb := exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc
  have h₀ (t : ℝ) (_ : t ∈ Icc a b) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible := by
    obtain ⟨C, hC⟩ := exists_norm_sub_apply_le hb t
    simpa using ι.exists_isInvertible_ofReal_smul_sub_of_isInvertible_of_norm_sub_apply_le hι
      hBtop (hSymm t) hC
  have hind := index_familyDomainTrajectoryOperator_eq_domainSpectralFlow (A := fun s ↦ -A s)
    hι hA.neg (fun s x y ↦ by simp [hSymm s x y]) hab
    (fun s hs ↦ ContinuousLinearMap.isInvertible_neg_iff.2 (hInv s hs))
    (ContinuousLinearMap.isInvertible_neg_iff.2 hBbot)
    (ContinuousLinearMap.isInvertible_neg_iff.2 hBtop) hAL hbot.neg htop.neg fun T ↦ by
      obtain ⟨c, hcT⟩ := hc T
      exact ⟨c, hcT.mono fun s hs hsT x ↦ by
        simpa only [sub_apply, neg_apply, neg_sub_neg, norm_sub_rev] using hs hsT x⟩
  rw [hind, domainSpectralFlow_neg_of_ker_eq_bot hι hab hA.continuousOn (fun t _ ↦ hSymm t) h₀
    (LinearMap.ker_eq_bot.2 (hInv a left_notMem_Ioo).injective)
    (LinearMap.ker_eq_bot.2 (hInv b right_notMem_Ioo).injective)]

/-- **The index of `∂ₛ - A` is minus the spectral flow of `A`, for large intervals.** Under the
hypotheses of
`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow`,
without pre-specifying an interval containing the crossings, the index of `u ↦ (ι ∘ u)' - A u`
equals `-TauCeti.domainSpectralFlow ι A a b` for every `a` far enough to the left and every `b` far
enough to the right. -/
theorem eventually_index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] fun s ↦ -A s)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        -domainSpectralFlow ι A ab.1 ab.2 := by
  filter_upwards [ContinuousLinearMap.eventually_le_and_forall_notMem_Ioo_isInvertible
      hBbot hBtop hbot htop] with ⟨a, b⟩ ⟨hab, hinv⟩
  exact index_familyDomainTrajectoryOperator_of_ae_eq_neg_eq_neg_domainSpectralFlow hι hA hSymm hab
    hinv hBbot hBtop hAL hbot htop hc

/-- **The regular-crossing index formula over a compactly embedded domain.** Under the hypotheses
of `TauCeti.WeakDerivStep.eventually_index_familyDomainTrajectoryOperator_eq_domainSpectralFlow`,
if at every crossing `t` (where `ker A t ≠ ⊥`) the path has a derivative `A' t` whose crossing form
`Γₜ : x ↦ ⟪A' t x, ι x⟫` on `ker A t` is nondegenerate, then the index of `u ↦ (ι ∘ u)' + A u` is
the sum over all crossings of the signatures `sigPos Γₜ - sigNeg Γₜ`. -/
theorem index_familyDomainTrajectoryOperator_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖)
    {A' : ℝ → D →L[ℝ] H} (hderiv : ∀ t, (A t).ker ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t, (A t).ker ≠ ⊥ → (ι.domainCrossingForm (A t) (A' t)).Nondegenerate) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index =
      ∑ᶠ t, ((sigPos (ι.domainCrossingForm (A t) (A' t)) : ℤ) -
        sigNeg (ι.domainCrossingForm (A t) (A' t))) := by
  obtain ⟨⟨a, b⟩, hab, hinv⟩ :=
    (ContinuousLinearMap.eventually_le_and_forall_notMem_Ioo_isInvertible
      hBbot hBtop hbot htop).exists
  have hb := exists_forall_mem_Icc_norm_sub_apply_le_of_ae hA hc
  have h₀ (t : ℝ) (_ : t ∈ Icc a b) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible := by
    obtain ⟨C, hC⟩ := exists_norm_sub_apply_le hb t
    simpa using ι.exists_isInvertible_ofReal_smul_sub_of_isInvertible_of_norm_sub_apply_le hι
      hBtop (hSymm t) hC
  have hker {s : ℝ} (hs : s ∉ Ioo a b) : (A s).ker = ⊥ :=
    LinearMap.ker_eq_bot.2 (hinv s hs).injective
  rw [index_familyDomainTrajectoryOperator_eq_domainSpectralFlow hι hA hSymm hab hinv hBbot hBtop
      hAL hbot htop hc,
    domainSpectralFlow_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm hι hab hA.continuousOn
      (fun t _ ↦ hSymm t) h₀ (hker left_notMem_Ioo) (hker right_notMem_Ioo)
      (fun t _ hne ↦ hderiv t hne) (fun t _ hne ↦ hreg t hne)]
  refine (finsum_mem_inter_support_eq' _ (Ioo a b) univ fun t ht ↦
    iff_of_true ?_ (mem_univ t)).trans (finsum_mem_univ _)
  by_contra htab
  exact ht (ContinuousLinearMap.sigPos_sub_sigNeg_domainCrossingForm_eq_zero_of_ker_eq_bot
    (hker htab) _)

end Main

end TauCeti.WeakDerivStep
