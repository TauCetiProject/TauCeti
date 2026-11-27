/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Neg
public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.RegularCrossings
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.ShiftPath
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Homotopy
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Perturbation
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.InvertiblePath
import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.LocallyConstant.Preconnected

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
  (`index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow` and
  `eventually_index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow` in
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

/-! ### Smooth segment models and bounds through `ι` -/

private theorem memLp_smoothSegmentPath (B₀ B : D →L[ℝ] H) :
    MemLp (smoothSegmentPath B₀ B) ∞ μ₀ := by
  refine memLp_top_of_bound ((contDiff_smoothSegmentPath (x := B₀) (y := B) (n := 0)).continuous
    |>.aestronglyMeasurable) (‖B₀‖ + ‖B - B₀‖) (ae_of_all _ fun s ↦ ?_)
  rw [smoothSegmentPath_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg s)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one s)

/-- The `L∞` class of `TauCeti.smoothSegmentPath B₀ B`. -/
private def smoothSegmentPathL (B₀ B : D →L[ℝ] H) : Lp (D →L[ℝ] H) ∞ μ₀ :=
  (memLp_smoothSegmentPath B₀ B).toLp _

private theorem smoothSegmentPathL_ae (B₀ B : D →L[ℝ] H) :
    smoothSegmentPathL B₀ B =ᵐ[μ₀] smoothSegmentPath B₀ B :=
  (memLp_smoothSegmentPath B₀ B).coeFn_toLp

private theorem norm_smoothSegmentPath_sub_apply_le {B₀ B : D →L[ℝ] H} {c : ℝ}
    (hc : ∀ x, ‖(B - B₀) x‖ ≤ c * ‖ι x‖) (s : ℝ) (x : D) :
    ‖(smoothSegmentPath B₀ B s - B) x‖ ≤ c * ‖ι x‖ := by
  have heq : (smoothSegmentPath B₀ B s - B) x = (1 - Real.smoothTransition s) • -((B - B₀) x) := by
    simp only [smoothSegmentPath_def, sub_apply, add_apply, smul_apply]
    module
  rw [heq, norm_smul, norm_neg, Real.norm_of_nonneg (sub_nonneg.2 (Real.smoothTransition.le_one s))]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (sub_le_self _ (Real.smoothTransition.nonneg s)) |>.trans (hc x)

private theorem ae_norm_smoothSegmentPath_sub_apply_le {B₀ B : D →L[ℝ] H}
    (hbdd : ∃ c, ∀ x, ‖(B - B₀) x‖ ≤ c * ‖ι x‖) (T : ℝ) :
    ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(smoothSegmentPath B₀ B s - B) x‖ ≤ c * ‖ι x‖ :=
  hbdd.imp fun _ hc ↦ ae_of_all _ fun s _ x ↦ norm_smoothSegmentPath_sub_apply_le hc s x

private theorem exists_norm_sub_smul_sub_apply_le {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H}
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖)
    (r t c₁ c₂ : ℝ) : ∃ C, ∀ x, ‖((A r - c₁ • ι) - (A t - c₂ • ι)) x‖ ≤ C * ‖ι x‖ := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_sub_apply_le hb r
  obtain ⟨C₂, hC₂⟩ := exists_norm_sub_apply_le hb t
  refine ⟨C₁ + C₂ + |c₂ - c₁|, fun x ↦ ?_⟩
  have heq : ((A r - c₁ • ι) - (A t - c₂ • ι)) x =
      (A r - Btop) x - (A t - Btop) x + (c₂ - c₁) • ι x := by
    simp only [sub_apply, smul_apply]
    module
  rw [heq, add_mul, add_mul, ← Real.norm_eq_abs, ← norm_smul]
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (hC₁ x) (hC₂ x)))
    le_rfl)

private theorem exists_isInvertible_smul_sub_of_norm_sub_apply_le [CompleteSpace D]
    [CompleteSpace H] (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H}
    (hBtop : Btop.IsInvertible) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖) (t : ℝ) :
    ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible := by
  obtain ⟨C, hC⟩ := exists_norm_sub_apply_le hb t
  have h0 : ((0 : ℝ) • ι - Btop).IsInvertible := by
    simpa [ContinuousLinearMap.isInvertible_neg_iff] using hBtop
  obtain ⟨c, hc⟩ := ι.exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le hι h0 (hSymm t) hC
  exact ⟨c, ContinuousLinearMap.isInvertible_ofReal_smul_sub_iff.1 hc⟩

private theorem isSymm_sub_smul {B : D →L[ℝ] H}
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (c : ℝ) (x y : D) :
    ⟪(B - c • ι) x, ι y⟫_ℝ = ⟪ι x, (B - c • ι) y⟫_ℝ := by
  simp only [sub_apply, smul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hSymm x y]

variable [CompleteSpace D]

/-- Outside a bounded interval, `A s` is eventually invertible when its limits at `±∞` are
invertible. -/
private theorem exists_forall_notMem_Ioo_isInvertible {A : ℝ → D →L[ℝ] H} {Bbot Btop : D →L[ℝ] H}
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop)) :
    ∃ a₀ b₀ : ℝ, ∀ s ∉ Ioo a₀ b₀, (A s).IsInvertible := by
  obtain ⟨a₀, ha₀⟩ := eventually_atBot.1 (hbot.eventually hBbot.eventually_nhds)
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (htop.eventually hBtop.eventually_nhds)
  refine ⟨min a₀ b₀, max a₀ b₀, fun s hs ↦ ?_⟩
  rcases not_and_or.1 hs with h | h
  · exact ha₀ s ((not_lt.1 h).trans (min_le_left _ _))
  · exact hb₀ s ((le_max_right _ _).trans (not_lt.1 h))

variable [CompleteSpace H]

/-- The index of the trajectory operator along `TauCeti.smoothSegmentPath B₀ B`. -/
private def modelIndex (ι B₀ B : D →L[ℝ] H) : ℤ :=
  (familyDomainTrajectoryOperator (p := 2) ι (smoothSegmentPathL B₀ B)).index

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
    (ae_norm_smoothSegmentPath_sub_apply_le ⟨c₁₂, hc₁₂⟩)
    (smoothSegmentPathL_ae B₂ B₃) (eventuallyEq_smoothSegmentPath_atBot B₂ B₃).tendsto
    (eventuallyEq_smoothSegmentPath_atTop B₂ B₃).tendsto
    (ae_norm_smoothSegmentPath_sub_apply_le ⟨c₂₃, hc₂₃⟩)
    (smoothSegmentPathL_ae B₁ B₃) (eventuallyEq_smoothSegmentPath_atBot B₁ B₃).tendsto
    (eventuallyEq_smoothSegmentPath_atTop B₁ B₃).tendsto
    (ae_norm_smoothSegmentPath_sub_apply_le h₁₃)

private theorem modelIndex_sub_smul_eq_zero (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {u v c : ℝ}
    (huv : u ≤ v) (hinv : ∀ t ∈ Icc u v, (A t - c • ι).IsInvertible)
    (hbdd : ∀ t ∈ Icc u v, ∃ C, ∀ x, ‖(A t - A u) x‖ ≤ C * ‖ι x‖) :
    modelIndex ι (A u - c • ι) (A v - c • ι) = 0 := by
  let φ : unitInterval → ℝ := fun t ↦ (1 - (t : ℝ)) * u + t * v
  have hmem (t : unitInterval) : φ t ∈ Icc u v := by
    rw [← segment_eq_Icc huv]
    exact ⟨1 - t, t, sub_nonneg.2 t.property.2, t.property.1, by ring, rfl⟩
  let γ : Path (A u - c • ι) (A v - c • ι) :=
    { toFun t := A (φ t) - c • ι
      continuous_toFun := (hA.comp (by fun_prop)).sub continuous_const
      source' := by simp [φ]
      target' := by simp [φ] }
  have hγbdd (t : unitInterval) : ∃ C, ∀ x, ‖(γ t - (A u - c • ι)) x‖ ≤ C * ‖ι x‖ := by
    obtain ⟨C, hC⟩ := hbdd (φ t) (hmem t)
    exact ⟨C, fun x ↦ by simpa [γ] using hC x⟩
  have hvu : ∃ C, ∀ x, ‖((A v - c • ι) - (A u - c • ι)) x‖ ≤ C * ‖ι x‖ := by
    obtain ⟨C, hC⟩ := hbdd v (right_mem_Icc.2 huv)
    exact ⟨C, fun x ↦ by simpa [γ] using hC x⟩
  exact index_familyDomainTrajectoryOperator_eq_zero_of_path hι γ
    (fun t ↦ isSymm_sub_smul (hSymm (φ t)) c) (fun t ↦ hinv (φ t) (hmem t)) hγbdd
    (smoothSegmentPathL_ae _ _) (eventuallyEq_smoothSegmentPath_atBot _ _).tendsto
    (eventuallyEq_smoothSegmentPath_atTop _ _).tendsto
    (ae_norm_smoothSegmentPath_sub_apply_le hvu)

private theorem domainSpectralFlow_sub_smul_smoothSegmentPath (hι : IsCompactOperator ι)
    {B : D →L[ℝ] H} (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c₁ c₂ a b : ℝ}
    (hc₁ : (B - c₁ • ι).IsInvertible) (hc₂ : (B - c₂ • ι).IsInvertible)
    (ha : a ≤ 0) (hb : 1 ≤ b) :
    domainSpectralFlow ι (fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι) a b =
      domainSpectralFlow ι (fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι) 0 1 := by
  have h0 {lam : ℝ} : ∃ c₀ : ℝ, (c₀ • ι - (B - lam • ι)).IsInvertible := ⟨c₁ - lam, by
    have heq : (c₁ - lam) • ι - (B - lam • ι) = -(B - c₁ • ι) := by
      rw [sub_smul]
      abel
    rw [heq, ContinuousLinearMap.isInvertible_neg_iff]
    exact hc₁⟩
  have hcont : Continuous fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι :=
    continuous_const.sub ((contDiff_smoothSegmentPath (x := c₁) (y := c₂) (n := 0)).continuous.smul
      continuous_const)
  have hcut : domainSpectralFlow ι (fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι) a b =
      domainSpectralFlow ι (fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι) 0 1 := by
    rw [domainSpectralFlow_add_adjacent_intervals hι ha (hb.trans' zero_le_one)
        hcont.continuousOn (fun s _ ↦ isSymm_sub_smul hSymm _) (fun _ _ ↦ h0),
      domainSpectralFlow_add_adjacent_intervals hι zero_le_one hb
        hcont.continuousOn (fun s _ ↦ isSymm_sub_smul hSymm _) (fun _ _ ↦ h0),
      domainSpectralFlow_eq_zero_of_forall_isInvertible hι ha hcont.continuousOn
        (fun s _ ↦ isSymm_sub_smul hSymm _) fun s hs ↦ by
          simpa only [smoothSegmentPath_of_nonpos c₁ c₂ hs.2] using hc₁,
      domainSpectralFlow_eq_zero_of_forall_isInvertible hι hb hcont.continuousOn
        (fun s _ ↦ isSymm_sub_smul hSymm _) fun s hs ↦ by
          simpa only [smoothSegmentPath_of_one_le c₁ c₂ hs.1] using hc₂,
      zero_add, add_zero]
  have heq : (fun s ↦ B - smoothSegmentPath c₁ c₂ s • ι) =
      (fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι) ∘ Real.smoothTransition := by
    ext s x
    simp only [Function.comp_apply, smoothSegmentPath_def, smul_eq_mul, sub_apply, smul_apply]
    module
  rw [hcut, heq]
  simpa [Real.smoothTransition.zero_of_nonpos le_rfl,
    Real.smoothTransition.one_of_one_le le_rfl] using
    domainSpectralFlow_comp_of_mapsTo (A := fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι) hι
      zero_le_one Real.smoothTransition.continuous.continuousOn
      (fun s _ ↦ ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩)
      (by simp [Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl])
      (by fun_prop) (fun σ _ ↦ isSymm_sub_smul hSymm _) fun _ _ ↦ h0

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
  rw [hab, domainSpectralFlow_sub_smul_smoothSegmentPath hι hSymm hc₁ hc₂ ha hb]

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

private theorem domainSpectralFlow_shift_segment_add (hι : IsCompactOperator ι) {B : D →L[ℝ] H}
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c₁ c₂ : ℝ} (hc₁ : (B - c₁ • ι).IsInvertible) :
    domainSpectralFlow ι (fun σ ↦ B - (σ * c₁) • ι) 0 1 +
        domainSpectralFlow ι (fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι) 0 1 =
      domainSpectralFlow ι (fun σ ↦ B - (σ * c₂) • ι) 0 1 := by
  let K : ℝ → ℝ → D →L[ℝ] H := fun τ σ ↦ B - ((1 - σ) * (τ * c₁) + σ * c₂) • ι
  have hK₀ (τ σ : ℝ) : ∃ c₀ : ℝ, (c₀ • ι - K τ σ).IsInvertible := ⟨c₁ - ((1 - σ) * (τ * c₁) +
    σ * c₂), by
    have heq : (c₁ - ((1 - σ) * (τ * c₁) + σ * c₂)) • ι - K τ σ = -(B - c₁ • ι) := by
      simp only [K, sub_smul]
      abel
    rw [heq, ContinuousLinearMap.isInvertible_neg_iff]
    exact hc₁⟩
  have hrect := domainSpectralFlow_add_domainSpectralFlow_eq_add (G := K) hι zero_le_one zero_le_one
    (by fun_prop) (fun τ _ σ _ ↦ isSymm_sub_smul hSymm _) (fun τ _ σ _ ↦ hK₀ τ σ)
  have htop : domainSpectralFlow ι (fun τ ↦ K τ 1) 0 1 = 0 :=
    domainSpectralFlow_eq_zero_of_forall_eq hι zero_le_one (isSymm_sub_smul hSymm _)
      (hK₀ 0 1) fun τ _ ↦ by simp [K]
  have hbot : K 0 = fun σ ↦ B - (σ * c₂) • ι := funext fun σ ↦ by simp [K]
  have hright : K 1 = fun σ ↦ B - ((1 - σ) * c₁ + σ * c₂) • ι := funext fun σ ↦ by simp [K]
  have hleft : (fun τ ↦ K τ 0) = fun τ ↦ B - (τ * c₁) • ι := funext fun τ ↦ by simp [K]
  rw [hbot, hright, hleft, htop, add_zero] at hrect
  linarith

private theorem staircaseDefect_eq_of_isInvertible (hι : IsCompactOperator ι)
    {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H} (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖) {a t c₁ c₂ : ℝ}
    (ha : (A a).IsInvertible) (hc₁ : (A t - c₁ • ι).IsInvertible)
    (hc₂ : (A t - c₂ • ι).IsInvertible) :
    staircaseDefect ι A a t c₁ = staircaseDefect ι A a t c₂ := by
  have hm := modelIndex_eq_add hι (B₁ := A a) (B₂ := A t - c₁ • ι) (B₃ := A t - c₂ • ι)
    (hSymm a) ha (isSymm_sub_smul (hSymm t) c₁) hc₁ (isSymm_sub_smul (hSymm t) c₂) hc₂
    (by simpa using exists_norm_sub_smul_sub_apply_le hb t a c₁ 0)
    (exists_norm_sub_smul_sub_apply_le hb t t c₂ c₁)
  have hseg := modelIndex_sub_smul hι (hSymm t) hc₁ hc₂
  have htri := domainSpectralFlow_shift_segment_add hι (hSymm t) (c₂ := c₂) hc₁
  simp only [staircaseDefect]
  linarith

private theorem domainSpectralFlow_add_shift_segment (hι : IsCompactOperator ι)
    {A : ℝ → D →L[ℝ] H} (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (h₀ : ∀ t, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) {u v c : ℝ} (huv : u ≤ v)
    (hinv : ∀ t ∈ Icc u v, (A t - c • ι).IsInvertible) :
    domainSpectralFlow ι A u v + domainSpectralFlow ι (fun σ ↦ A v - (σ * c) • ι) 0 1 =
      domainSpectralFlow ι (fun σ ↦ A u - (σ * c) • ι) 0 1 := by
  let G : ℝ → ℝ → D →L[ℝ] H := fun σ t ↦ A t - (σ * c) • ι
  have hGc : ContinuousOn (Function.uncurry G) (Icc 0 1 ×ˢ Icc u v) :=
    ((hA.comp continuous_snd).sub (((continuous_fst.mul continuous_const).smul
      continuous_const))).continuousOn
  have hG₀ (σ t : ℝ) : ∃ c₀ : ℝ, (c₀ • ι - G σ t).IsInvertible := by
    obtain ⟨c₀, hc₀⟩ := h₀ t
    have heq : (c₀ - σ * c) • ι - G σ t = c₀ • ι - A t := by
      simp only [G, sub_smul]
      abel
    exact ⟨c₀ - σ * c, by rwa [heq]⟩
  have hrect := domainSpectralFlow_add_domainSpectralFlow_eq_add (G := G) hι huv zero_le_one hGc
    (fun σ _ t _ ↦ isSymm_sub_smul (hSymm t) _) (fun σ _ t _ ↦ hG₀ σ t)
  have hG1 : G 1 = fun t ↦ A t - c • ι := funext fun t ↦ by simp [G]
  have htop : domainSpectralFlow ι (G 1) u v = 0 := by
    rw [hG1]
    exact domainSpectralFlow_eq_zero_of_forall_isInvertible hι huv
      (hA.sub continuous_const).continuousOn (fun t _ ↦ isSymm_sub_smul (hSymm t) c) hinv
  have hbot : G 0 = A := funext fun t ↦ by simp [G]
  rw [hbot, htop, add_zero] at hrect
  exact hrect

private theorem staircaseDefect_eq_of_forall_isInvertible (hι : IsCompactOperator ι)
    {A : ℝ → D →L[ℝ] H} {Btop : D →L[ℝ] H} (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖)
    (h₀ : ∀ t, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) {a u v c : ℝ} (hau : a ≤ u) (huv : u ≤ v)
    (ha : (A a).IsInvertible) (hinv : ∀ t ∈ Icc u v, (A t - c • ι).IsInvertible) :
    staircaseDefect ι A a u c = staircaseDefect ι A a v c := by
  have hu : u ∈ Icc u v := left_mem_Icc.2 huv
  have hv : v ∈ Icc u v := right_mem_Icc.2 huv
  have hm := modelIndex_eq_add hι (B₁ := A a) (B₂ := A u - c • ι) (B₃ := A v - c • ι)
    (hSymm a) ha (isSymm_sub_smul (hSymm u) c) (hinv u hu)
    (isSymm_sub_smul (hSymm v) c) (hinv v hv)
    (by simpa using exists_norm_sub_smul_sub_apply_le hb u a c 0)
    (exists_norm_sub_smul_sub_apply_le hb v u c c)
  have hm0 := modelIndex_sub_smul_eq_zero hι hA hSymm huv hinv fun t _ ↦ by
    simpa using exists_norm_sub_smul_sub_apply_le hb t u 0 0
  have hadd := domainSpectralFlow_add_adjacent_intervals hι hau huv hA.continuousOn
    (fun t _ ↦ hSymm t) fun t _ ↦ h₀ t
  have hsq := domainSpectralFlow_add_shift_segment hι hA hSymm h₀ huv hinv
  simp only [staircaseDefect]
  linarith

private theorem modelIndex_eq_domainSpectralFlow (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    {Btop : D →L[ℝ] H} (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBtop : Btop.IsInvertible)
    (hb : ∀ R, ∃ c, ∀ r ∈ Icc (-R) R, ∀ x, ‖(A r - Btop) x‖ ≤ c * ‖ι x‖)
    {a b : ℝ} (hab : a ≤ b) (ha : (A a).IsInvertible) (hbInv : (A b).IsInvertible) :
    modelIndex ι (A a) (A b) = domainSpectralFlow ι A a b := by
  classical
  have h₀ (t : ℝ) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible :=
    exists_isInvertible_smul_sub_of_norm_sub_apply_le hι hBtop hSymm hb t
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
      simpa using modelIndex_sub_smul_eq_zero (u := a) (v := a) (c := 0) hι hA hSymm le_rfl
        (fun t ht ↦ by obtain rfl : t = a := le_antisymm ht.2 ht.1; simpa using ha)
        fun t ht ↦ ⟨0, fun x ↦ by obtain rfl : t = a := le_antisymm ht.2 ht.1; simp⟩
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
  have hb := forall_norm_sub_apply_le hA hc
  have hm : MemLp (fun s ↦ A (max a (min b s))) ∞ μ₀ :=
    memLp_top_of_bound (hA.comp (by fun_prop)).aestronglyMeasurable C (.of_forall fun s ↦ hC _)
  have hloc := index_familyDomainTrajectoryOperator_eq_of_ae_eq_IccExtend hι hA hSymm hab hInv
    hBbot hBtop hAL hbot htop hc (AL' := hm.toLp _) <|
    hm.coeFn_toLp.trans <| EventuallyEq.of_eq <| funext fun s ↦ by
      rw [IccExtend_apply, domRestrict_apply]
  have hbotI : Tendsto (fun s ↦ A (max a (min b s))) atBot (𝓝 (A a)) :=
    tendsto_const_nhds.congr' ((eventually_le_atBot a).mono fun s hs ↦ by
      simp only [min_eq_right (hs.trans hab), max_eq_left hs])
  have htopI : Tendsto (fun s ↦ A (max a (min b s))) atTop (𝓝 (A b)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop b).mono fun s hs ↦ by
      simp only [min_eq_left hs, max_eq_right hab])
  have hba : ∃ c, ∀ x, ‖(A b - A a) x‖ ≤ c * ‖ι x‖ := by
    simpa using exists_norm_sub_smul_sub_apply_le hb b a 0 0
  rw [hloc]
  exact index_familyDomainTrajectoryOperator_eq hι (hSymm a) (hInv a fun h ↦ lt_irrefl a h.1)
    (hSymm b) (hInv b fun h ↦ lt_irrefl b h.2) hm.coeFn_toLp hbotI htopI
    (ae_norm_comp_sub_apply_le hb (exists_norm_sub_apply_le hb b) (by fun_prop))
    (smoothSegmentPathL_ae (A a) (A b)) (eventuallyEq_smoothSegmentPath_atBot _ _).tendsto
    (eventuallyEq_smoothSegmentPath_atTop _ _).tendsto
    (ae_norm_smoothSegmentPath_sub_apply_le hba)

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
    modelIndex_eq_domainSpectralFlow hι hA hSymm hBtop (forall_norm_sub_apply_le hA hc) hab
      (hInv a fun h ↦ lt_irrefl a h.1) (hInv b fun h ↦ lt_irrefl b h.2)]

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
  obtain ⟨a₀, b₀, hout⟩ := exists_forall_notMem_Ioo_isInvertible hBbot hBtop hbot htop
  filter_upwards [(eventually_le_atBot (min a₀ b₀)).prod_mk (eventually_ge_atTop (max a₀ b₀))]
    with ⟨a, b⟩ ⟨ha, hb⟩
  have hab : a ≤ b := ha.trans ((min_le_max).trans hb)
  have hinv (s : ℝ) (hs : s ∉ Ioo a b) : (A s).IsInvertible :=
    hout s fun hs' ↦ hs ⟨(ha.trans (min_le_left _ _)).trans_lt hs'.1,
      hs'.2.trans_le ((le_max_right _ _).trans hb)⟩
  exact index_familyDomainTrajectoryOperator_eq_domainSpectralFlow hι hA hSymm hab hinv hBbot hBtop
    hAL hbot htop hc

/-- **The index of `∂ₛ - A` is minus the spectral flow of `A`.** Let `ι : D →L[ℝ] H` be compact,
and let `A` be a continuous path of `ι`-symmetric operators with invertible limits `Bbot` and `Btop`
at `±∞`, differing from `Btop` on bounded windows by operators bounded through `ι`, and invertible
outside `(a, b)` for `a ≤ b`. Then the index of `u ↦ (ι ∘ u)' - A u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`, whose coefficient is `-A`, is
`-TauCeti.domainSpectralFlow ι A a b`. -/
theorem index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) {a b : ℝ} (hab : a ≤ b)
    (hInv : ∀ s ∉ Ioo a b, (A s).IsInvertible) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] fun s ↦ -A s)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = -domainSpectralFlow ι A a b := by
  have hb := forall_norm_sub_apply_le hA hc
  have h₀ (t : ℝ) (_ : t ∈ Icc a b) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible :=
    exists_isInvertible_smul_sub_of_norm_sub_apply_le hι hBtop hSymm hb t
  have hind := index_familyDomainTrajectoryOperator_eq_domainSpectralFlow (A := fun s ↦ -A s)
    hι hA.neg (fun s x y ↦ by simp [hSymm s x y]) hab
    (fun s hs ↦ ContinuousLinearMap.isInvertible_neg_iff.2 (hInv s hs))
    (ContinuousLinearMap.isInvertible_neg_iff.2 hBbot)
    (ContinuousLinearMap.isInvertible_neg_iff.2 hBtop) hAL hbot.neg htop.neg fun T ↦ by
      obtain ⟨c, hcT⟩ := hc T
      exact ⟨c, hcT.mono fun s hs hsT x ↦ by
        rw [sub_apply, neg_apply, neg_apply, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
          norm_sub_rev]
        simpa only [sub_apply] using hs hsT x⟩
  rw [hind, domainSpectralFlow_neg_of_ker_eq_bot hι hab hA.continuousOn (fun t _ ↦ hSymm t) h₀
    (LinearMap.ker_eq_bot.2 (hInv a fun h ↦ lt_irrefl a h.1).injective)
    (LinearMap.ker_eq_bot.2 (hInv b fun h ↦ lt_irrefl b h.2).injective)]

/-- **The index of `∂ₛ - A` is minus the spectral flow of `A`, for large intervals.** Under the
hypotheses of
`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow`, without
pre-specifying an interval containing the crossings, the index of `u ↦ (ι ∘ u)' - A u` equals
`-TauCeti.domainSpectralFlow ι A a b` for every `a` far enough to the left and every `b` far enough
to the right. -/
theorem eventually_index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA : Continuous A)
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] fun s ↦ -A s)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        -domainSpectralFlow ι A ab.1 ab.2 := by
  obtain ⟨a₀, b₀, hout⟩ := exists_forall_notMem_Ioo_isInvertible hBbot hBtop hbot htop
  filter_upwards [(eventually_le_atBot (min a₀ b₀)).prod_mk (eventually_ge_atTop (max a₀ b₀))]
    with ⟨a, b⟩ ⟨ha, hb⟩
  have hab : a ≤ b := ha.trans ((min_le_max).trans hb)
  have hinv (s : ℝ) (hs : s ∉ Ioo a b) : (A s).IsInvertible :=
    hout s fun hs' ↦ hs ⟨(ha.trans (min_le_left _ _)).trans_lt hs'.1,
      hs'.2.trans_le ((le_max_right _ _).trans hb)⟩
  exact index_familyDomainTrajectoryOperator_neg_eq_neg_domainSpectralFlow hι hA hSymm hab hinv
    hBbot hBtop hAL hbot htop hc

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
  obtain ⟨a₀, b₀, hout⟩ := exists_forall_notMem_Ioo_isInvertible hBbot hBtop hbot htop
  set a := min a₀ b₀
  set b := max a₀ b₀
  have hab : a ≤ b := min_le_max
  have hinv (s : ℝ) (hs : s ∉ Ioo a b) : (A s).IsInvertible :=
    hout s fun hs' ↦ hs ⟨(min_le_left _ _).trans_lt hs'.1, hs'.2.trans_le (le_max_right _ _)⟩
  have hb := forall_norm_sub_apply_le hA hc
  have h₀ (t : ℝ) (_ : t ∈ Icc a b) : ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible :=
    exists_isInvertible_smul_sub_of_norm_sub_apply_le hι hBtop hSymm hb t
  have hker {s : ℝ} (hs : s ∉ Ioo a b) : (A s).ker = ⊥ :=
    LinearMap.ker_eq_bot.2 (hinv s hs).injective
  rw [index_familyDomainTrajectoryOperator_eq_domainSpectralFlow hι hA hSymm hab hinv hBbot hBtop
      hAL hbot htop hc,
    domainSpectralFlow_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm hι hab hA.continuousOn
      (fun t _ ↦ hSymm t) h₀ (hker fun h ↦ lt_irrefl a h.1) (hker fun h ↦ lt_irrefl b h.2)
      (fun t _ hne ↦ hderiv t hne) (fun t _ hne ↦ hreg t hne)]
  refine (finsum_mem_inter_support_eq' _ (Ioo a b) univ fun t ht ↦
    iff_of_true ?_ (mem_univ t)).trans (finsum_mem_univ _)
  by_contra htab
  exact ht (ContinuousLinearMap.sigPos_sub_sigNeg_domainCrossingForm_eq_zero_of_ker_eq_bot
    (hker htab) _)

end Main

end TauCeti.WeakDerivStep
