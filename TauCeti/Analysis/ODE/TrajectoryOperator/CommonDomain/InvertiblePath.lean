/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Fredholm
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.IndexLocalization

/-!
# The index of the trajectory operator between limits joined by invertible operators

Let `ι : D →L[ℝ] H` be a compact embedding of a Banach space `D` into a Hilbert space `H`, and
let `A` be a family of operators `D →L[ℝ] H` with an `L∞` class `AL`, converging to invertible
`ι`-symmetric operators `B₀` at `-∞` and `B₁` at `∞` (`⟪B x, ι y⟫ = ⟪ι x, B y⟫`), and differing
from `B₁` on every bounded interval by operators bounded through `ι`. Then
`D_A u = (ι ∘ u)' + A u`, from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`, is Fredholm
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`), and its index depends only
on `B₀` and `B₁` (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`).

This file proves that the index vanishes when `B₀` and `B₁` are joined by a path `γ` of
invertible `ι`-symmetric operators whose differences from `B₀` are bounded through `ι`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_path`). This is the
counterpart for the index of `∂ₛ + A(s)` of the vanishing of the spectral flow of a path of
invertible operators (`TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`). In particular,
for an `ι`-symmetric `B` such that `B - c ι` is invertible for every `c` between `a` and `b`, that
is, when no eigenvalue of `B` lies between `a` and `b`, a family from `B - a ι` to `B - b ι` gives
an operator of index zero
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_isInvertible_sub_smul`).

When the family `A` is itself a continuous path of invertible operators, its operator has index
zero (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`),
and so, since such a path has no spectral flow, the index of `D_A` is the spectral flow of `A`
over every interval
(`index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible`). Combined
with the catenation law (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add`),
the limit at `∞` of a family can be moved along any continuous path of invertible operators
without changing the index
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible`): the
index can change only when the limits pass through noninvertible operators.

For each `t`, the family `M_t(s) = B₀ + ψ(s) (γ t - B₀)`, where `ψ` is
`Real.smoothTransition`, runs from `B₀` to `γ t`. Its trajectory operator is Fredholm for every
`t`, since `γ t` is invertible, and it depends continuously on `t`, so its index does not depend
on `t`. At `t = 0` the family is constant, with index zero, and at `t = 1` it has the limits of
`A`, so it has the index of `D_A`.

## Main results

* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_path`: the index vanishes
  when the limits are joined by a path of invertible `ι`-symmetric operators.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_isInvertible_sub_smul`:
  the index vanishes between the shifts `B - a ι` and `B - b ι` when every intermediate shift is
  invertible.
* `index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible`: for a
  continuous path of invertible operators, the index is the spectral flow of the path.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible`: moving
  the limit at `∞` along a path of invertible operators does not change the index.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι : D →L[ℝ] H}

/-- The family `s ↦ B₀ + ψ(s) (B - B₀)` from `B₀` to `B`, for `ψ = Real.smoothTransition`. -/
private def model (B₀ B : D →L[ℝ] H) (s : ℝ) : D →L[ℝ] H :=
  B₀ + Real.smoothTransition s • (B - B₀)

private theorem continuous_model (B₀ B : D →L[ℝ] H) : Continuous (model B₀ B) :=
  continuous_const.add (Real.smoothTransition.continuous.smul continuous_const)

private theorem norm_model_sub_model_le (B₀ B B' : D →L[ℝ] H) (s : ℝ) :
    ‖model B₀ B s - model B₀ B' s‖ ≤ ‖B - B'‖ := by
  have : model B₀ B s - model B₀ B' s = Real.smoothTransition s • (B - B') := by
    simp only [model, smul_sub]
    abel
  rw [this, norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg s)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one s)

private theorem memLp_model (B₀ B : D →L[ℝ] H) : MemLp (model B₀ B) ∞ μ₀ := by
  refine memLp_top_of_bound (continuous_model B₀ B).aestronglyMeasurable (‖B₀‖ + ‖B - B₀‖)
    (ae_of_all _ fun s ↦ ?_)
  have h := norm_model_sub_model_le B₀ B B₀ s
  rw [show model B₀ B₀ s = B₀ by simp [model]] at h
  calc ‖model B₀ B s‖ ≤ ‖B₀‖ + ‖model B₀ B s - B₀‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖B₀‖ + ‖B - B₀‖ := by gcongr

/-- The `L∞` class of the family `s ↦ B₀ + ψ(s) (B - B₀)`. -/
private def modelL (B₀ B : D →L[ℝ] H) : Lp (D →L[ℝ] H) ∞ μ₀ :=
  (memLp_model B₀ B).toLp _

private theorem modelL_ae (B₀ B : D →L[ℝ] H) : modelL B₀ B =ᵐ[μ₀] model B₀ B :=
  (memLp_model B₀ B).coeFn_toLp

/-- The class of the family `s ↦ B₀ + ψ(s) (B - B₀)` depends `1`-Lipschitz on `B`. -/
private theorem lipschitzWith_modelL (B₀ : D →L[ℝ] H) : LipschitzWith 1 (modelL B₀) :=
  LipschitzWith.of_dist_le_mul fun B B' ↦ by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_of_ae_bound_top (norm_nonneg _) ?_
    filter_upwards [Lp.coeFn_sub (modelL B₀ B) (modelL B₀ B'), modelL_ae B₀ B, modelL_ae B₀ B']
      with s hs h h'
    rw [hs, Pi.sub_apply, h, h']
    exact norm_model_sub_model_le B₀ B B' s

private theorem tendsto_model_atBot (B₀ B : D →L[ℝ] H) : Tendsto (model B₀ B) atBot (𝓝 B₀) :=
  tendsto_const_nhds.congr' <| (eventually_le_atBot 0).mono fun s hs ↦ by
    simp [model, Real.smoothTransition.zero_of_nonpos hs]

private theorem tendsto_model_atTop (B₀ B : D →L[ℝ] H) : Tendsto (model B₀ B) atTop (𝓝 B) :=
  tendsto_const_nhds.congr' <| (eventually_ge_atTop 1).mono fun s hs ↦ by
    simp [model, Real.smoothTransition.one_of_one_le hs]

/-- If `B - B₀` is bounded through `ι`, then so is `B₀ + ψ(s) (B - B₀) - B`, uniformly in `s`. -/
private theorem norm_model_sub_apply_le {B₀ B : D →L[ℝ] H} {c : ℝ}
    (hc : ∀ x, ‖(B - B₀) x‖ ≤ c * ‖ι x‖) (s : ℝ) (x : D) :
    ‖(model B₀ B s - B) x‖ ≤ c * ‖ι x‖ := by
  have : (model B₀ B s - B) x = (1 - Real.smoothTransition s) • -((B - B₀) x) := by
    simp only [model, sub_apply, add_apply, smul_apply]
    module
  rw [this, norm_smul, norm_neg, Real.norm_of_nonneg
    (sub_nonneg.2 (Real.smoothTransition.le_one s))]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (sub_le_self _ (Real.smoothTransition.nonneg s)) |>.trans (hc x)

/-- **The index vanishes between limits joined by invertible operators.** Let `ι` be compact and
let `γ` be a path from `B₀` to `B₁` of invertible `ι`-symmetric operators `γ t` whose differences
`γ t - B₀` are bounded through `ι`. Let `A(s)` converge to `B₀` at `-∞` and to `B₁` at `∞`, and
differ from `B₁` on every bounded interval by operators bounded through `ι`. Then
`u ↦ (ι ∘ u)' + A u` has index zero. -/
theorem index_familyDomainTrajectoryOperator_eq_zero_of_path [CompleteSpace D] [CompleteSpace H]
    (hι : IsCompactOperator ι)
    {B₀ B₁ : D →L[ℝ] H} (γ : Path B₀ B₁)
    (hSymm : ∀ t, ∀ x y : D, ⟪γ t x, ι y⟫_ℝ = ⟪ι x, γ t y⟫_ℝ) (hγ : ∀ t, (γ t).IsInvertible)
    (hbdd : ∀ t, ∃ c, ∀ x, ‖(γ t - B₀) x‖ ≤ c * ‖ι x‖) {A : ℝ → D →L[ℝ] H}
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 B₀))
    (htop : Tendsto A atTop (𝓝 B₁))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B₁) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = 0 := by
  have hSymm₀ : ∀ x y : D, ⟪B₀ x, ι y⟫_ℝ = ⟪ι x, B₀ y⟫_ℝ := by simpa using hSymm 0
  have hB₀ : B₀.IsInvertible := by simpa using hγ 0
  have hSymm₁ : ∀ x y : D, ⟪B₁ x, ι y⟫_ℝ = ⟪ι x, B₁ y⟫_ℝ := by simpa using hSymm 1
  have hB₁ : B₁.IsInvertible := by simpa using hγ 1
  -- The model family from `B₀` to `γ t` satisfies the hypotheses of the Fredholm theorem.
  have hc' (t : unitInterval) (T : ℝ) : ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T →
      ∀ x, ‖(model B₀ (γ t) s - γ t) x‖ ≤ c * ‖ι x‖ := by
    obtain ⟨c, hc⟩ := hbdd t
    exact ⟨c, ae_of_all _ fun s _ x ↦ norm_model_sub_apply_le hc s x⟩
  have hF (t : unitInterval) :
      (familyDomainTrajectoryOperator (p := 2) ι (modelL B₀ (γ t))).IsFredholm :=
    isFredholm_familyDomainTrajectoryOperator hι hSymm₀ hB₀ (hSymm t) (hγ t) (modelL_ae _ _)
      (tendsto_model_atBot _ _) (tendsto_model_atTop _ _) (hc' t)
  -- Along the path, the index of the model family is constant.
  have hpath := Continuous.index_eq_of_preconnectedSpace
    ((continuous_familyDomainTrajectoryOperator ι).comp
      ((lipschitzWith_modelL B₀).continuous.comp γ.continuous)) hF 0 1
  simp only [Path.source, Path.target] at hpath
  -- At `t = 0` the model family is constant, at `t = 1` it has the limits of `A`.
  rw [index_familyDomainTrajectoryOperator_eq hι hSymm₀ hB₀ hSymm₁ hB₁ hAL hbot htop hc
    (modelL_ae B₀ B₁) (tendsto_model_atBot _ _) (tendsto_model_atTop _ _)
    (by simpa using hc' 1), ← hpath]
  exact index_familyDomainTrajectoryOperator_eq_zero hι hSymm₀ hB₀ (modelL_ae B₀ B₀)
    (tendsto_model_atBot _ _) (tendsto_model_atTop _ _) (by simpa using hc' 0)

/-- **The index vanishes between shifts across no eigenvalue.** Let `ι` be compact and `B` an
`ι`-symmetric operator such that `B - c ι` is invertible for every `c` between `a` and `b`. Let
`A(s)` converge to `B - a ι` at `-∞` and to `B - b ι` at `∞`, and differ from `B - b ι` on every
bounded interval by operators bounded through `ι`. Then `u ↦ (ι ∘ u)' + A u` has index zero. -/
theorem index_familyDomainTrajectoryOperator_eq_zero_of_isInvertible_sub_smul [CompleteSpace D]
    [CompleteSpace H] (hι : IsCompactOperator ι) {B : D →L[ℝ] H}
    (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {a b : ℝ}
    (hB : ∀ c ∈ uIcc a b, (B - c • ι).IsInvertible) {A : ℝ → D →L[ℝ] H}
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 (B - a • ι)))
    (htop : Tendsto A atTop (𝓝 (B - b • ι)))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - (B - b • ι)) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = 0 := by
  -- The shifts `c t = (1 - t) a + t b` run through the interval between `a` and `b`.
  have hmem (t : unitInterval) : (1 - (t : ℝ)) * a + t * b ∈ uIcc a b := by
    rw [← segment_eq_uIcc]
    exact ⟨1 - t, t, sub_nonneg.2 t.property.2, t.property.1, by ring, by simp [smul_eq_mul]⟩
  let γ : Path (B - a • ι) (B - b • ι) :=
    { toFun t := B - ((1 - (t : ℝ)) * a + t * b) • ι
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  refine index_familyDomainTrajectoryOperator_eq_zero_of_path hι γ (fun t x y ↦ ?_)
    (fun t ↦ hB _ (hmem t)) (fun t ↦ ⟨|a - ((1 - (t : ℝ)) * a + t * b)|, fun x ↦ le_of_eq ?_⟩)
    hAL hbot htop hc
  · simp [γ, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hSymm]
  · rw [← Real.norm_eq_abs, ← norm_smul]
    congr 1
    simp only [γ, Path.coe_mk_mk, sub_apply, smul_apply]
    module

/-- **The index is the spectral flow, for a path of invertible operators.** Under the hypotheses
of `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`,
the index of `u ↦ (ι ∘ u)' + A u` is the spectral flow of `A` over every interval `[a, b]`; both
vanish. -/
theorem index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_forall_isInvertible
    [CompleteSpace D] [CompleteSpace H] (hι : IsCompactOperator ι) {A : ℝ → D →L[ℝ] H}
    (hA : Continuous A) (hSymm : ∀ s x y, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hinv : ∀ s, (A s).IsInvertible) {Bbot Btop : D →L[ℝ] H} (hBbot : Bbot.IsInvertible)
    (hBtop : Btop.IsInvertible) {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖)
    {a b : ℝ} (hab : a ≤ b) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = domainSpectralFlow ι A a b := by
  rw [index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι hA hSymm hinv hBbot
    hBtop hAL hbot htop hc, domainSpectralFlow_eq_zero_of_forall_isInvertible hι hab
    hA.continuousOn (fun t _ ↦ hSymm t) fun t _ ↦ hinv t]

/-- **Deforming the limit at `∞` through invertible operators preserves the index.** Let `ι` be
compact, and let `A` run from `B₀` at `-∞` to `B₁` at `∞` and `A'` from `B₀` to `B₂`, each
differing from its limit at `∞` on every bounded interval by an operator bounded through `ι`, with
`B₀`, `B₁`, `B₂` invertible, `B₀` symmetric through `ι` and `B₁ - B₂` bounded through `ι`. If a
continuous path `γ` of invertible `ι`-symmetric operators runs from `B₁` at `-∞` to `B₂` at `∞`,
differing from `B₂` on every bounded interval by operators bounded through `ι`, then
`u ↦ (ι ∘ u)' + A u` and `u ↦ (ι ∘ u)' + A' u` have the same index. -/
theorem index_familyDomainTrajectoryOperator_eq_of_forall_isInvertible [CompleteSpace D]
    [CompleteSpace H] (hι : IsCompactOperator ι)
    {B₀ B₁ B₂ : D →L[ℝ] H} (hSymm₀ : ∀ x y : D, ⟪B₀ x, ι y⟫_ℝ = ⟪ι x, B₀ y⟫_ℝ)
    (hB₀ : B₀.IsInvertible) (hB₁ : B₁.IsInvertible) (hB₂ : B₂.IsInvertible)
    (h₁₂ : ∃ c, ∀ x, ‖(B₁ - B₂) x‖ ≤ c * ‖ι x‖) {γ : ℝ → D →L[ℝ] H} (hγ : Continuous γ)
    (hγSymm : ∀ s x y, ⟪γ s x, ι y⟫_ℝ = ⟪ι x, γ s y⟫_ℝ) (hγinv : ∀ s, (γ s).IsInvertible)
    {γL : Lp (D →L[ℝ] H) ∞ μ₀} (hγL : γL =ᵐ[μ₀] γ) (hγbot : Tendsto γ atBot (𝓝 B₁))
    (hγtop : Tendsto γ atTop (𝓝 B₂))
    (hγc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(γ s - B₂) x‖ ≤ c * ‖ι x‖)
    {A A' : ℝ → D →L[ℝ] H} {AL AL' : Lp (D →L[ℝ] H) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 B₀)) (htop : Tendsto A atTop (𝓝 B₁))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B₁) x‖ ≤ c * ‖ι x‖)
    (hAL' : AL' =ᵐ[μ₀] A') (hbot' : Tendsto A' atBot (𝓝 B₀)) (htop' : Tendsto A' atTop (𝓝 B₂))
    (hc' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A' s - B₂) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL').index =
      (familyDomainTrajectoryOperator (p := 2) ι AL).index := by
  -- Catenate `A` with `γ`; the operator of `γ` has index zero.
  rw [index_familyDomainTrajectoryOperator_eq_add hι hSymm₀ hB₀
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hγbot
      (.of_forall (hγSymm · x y))) hB₁
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hγtop
      (.of_forall (hγSymm · x y))) hB₂ h₁₂
    hAL hbot htop hc hγL hγbot hγtop hγc hAL' hbot' htop' hc',
    index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι hγ hγSymm hγinv hB₁ hB₂
      hγL hγbot hγtop hγc, add_zero]

end TauCeti.WeakDerivStep
