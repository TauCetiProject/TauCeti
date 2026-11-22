/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.IntegrabilityGain
public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Interior `W^{2,q}` regularity for continuous principal coefficients

Let `E` be a finite-dimensional real inner product space, `Ω ⊆ E` open and `1 < p, q < ∞`. Let `a`
be a field of endomorphisms of `E`, continuous on `Ω` and elliptic at each point of `Ω`:
`λₓ ‖ξ‖² ≤ ⟪a(x) ξ, ξ⟫` for some `λₓ > 0`. This file proves the interior part of
Gilbarg–Trudinger, Lemma 9.16: a strong solution `u ∈ W^{2,p}(Ω)` of

`tr (a D²u) = f`

with `f`, `u` and the weak gradient `∇u` in `L^q(Ω)` lies in `W^{2,q}` near every point of `Ω`
(`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn`). The exponents
`p` and `q` are unrelated: the statement improves integrability when `q > p` and is a localization
statement when `q < p`.

Lower-order terms are covered: if `u` solves `tr (a D²u) + ⟪b, ∇u⟫ + c u = f` with bounded
measurable `b` and `c`, then `tr (a D²u) = f - ⟪b, ∇u⟫ - c u`, and the right side lies in `L^q(Ω)`
because `u` and `∇u` do.

## The argument

Fix `x₀ ∈ Ω`, freeze the coefficient at `A = a(x₀)` with ellipticity constant `λ`, and let `δ` be
the constant of the whole-space integrability gain for a frozen elliptic operator
(`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le`). By continuity
there is `ρ > 0` with `K = closedBall x₀ (2ρ) ⊆ Ω` and `‖a(x) - A‖ ≤ δ λ` on `K`. Let `ζ` be a
smooth cutoff equal to `1` on `closedBall x₀ ρ` and supported in `B(x₀, 2ρ)`. The product `ζ u`,
extended by zero, is an element `w` of `W^{2,p}(E)` with weak Hessian `ζ D²u + T` on `K` and `0`
off `K`, where `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is the Leibniz remainder
(`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`). So `w` solves

`tr (ã D²w) = 1_K (ζ f + tr (a T))`,

where `ã = a` on `K` and `ã = A` off `K`, so that `‖ã - A‖ ≤ δ λ` everywhere. The right side lies
in `L^q(E)` since `a` is bounded on `K` and `u, ∇u ∈ L^q(Ω)`, and so does the value `ζ u` of `w`.
The whole-space theorem places `w` in `W^{2,q}(E)`, and on `B(x₀, ρ)`, where `ζ = 1`, `w` is `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16, and the proof of Theorem 9.11 (freezing the coefficients and localizing by a
  cutoff).
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  {Omega : Opens E}

/-- The Leibniz remainder `∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` of the cutoff `ζ u` of `u ∈ W^{2,p}(Ω)`. -/
private def cutoffRemainder (zeta : E → ℝ) (u : Wkp (volume : Measure E) Omega p 2) (x : E) :
    E →L[ℝ] E :=
  leibnizRemainder zeta (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- By continuity, a coefficient continuous on `Ω` stays within `ε` of its value at `x₀` on a
closed ball `closedBall x₀ (2ρ) ⊆ Ω`. -/
private theorem exists_closedBall_subset_and_norm_sub_le {a : E → E →L[ℝ] E}
    (ha : ContinuousOn a Omega) {x₀ : E} (hx₀ : x₀ ∈ Omega) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, closedBall x₀ (2 * ρ) ⊆ Omega ∧
      ∀ x ∈ closedBall x₀ (2 * ρ), ‖a x - a x₀‖ ≤ ε := by
  obtain ⟨η, hη, hηΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen x₀ hx₀
  obtain ⟨θ, hθ, hθa⟩ :=
    Metric.continuousAt_iff.1 (ha.continuousAt (Omega.isOpen.mem_nhds hx₀)) ε hε
  have hm : 0 < min η θ := lt_min hη hθ
  have hlt : ∀ x ∈ closedBall x₀ (2 * (min η θ / 3)), dist x x₀ < min η θ := fun x hx ↦ by
    rw [mem_closedBall] at hx
    linarith
  refine ⟨min η θ / 3, by positivity, fun x hx ↦ hηΩ ?_, fun x hx ↦ ?_⟩
  · exact mem_ball.2 ((hlt x hx).trans_le (min_le_left _ _))
  · rw [← dist_eq_norm]
    exact (hθa ((hlt x hx).trans_le (min_le_right _ _))).le

/-- **The cutoff of `u`, extended by zero.** For a smooth `ζ` with compact support in a measurable
`K ⊆ Ω`, some `w ∈ W^{2,p}(E)` has value `1_K ζ u` and weak Hessian `1_K (ζ D²u + T)`, where `T` is
the Leibniz remainder; the remainder is measurable on `Ω`. -/
private theorem exists_wkp_value_ae_eq_indicator_mul (hp_top : p ≠ ⊤) {K : Set E}
    (hKΩ : K ⊆ Omega) {zeta : E → ℝ} (hzeta : ContDiff ℝ ∞ zeta) (hcpt : HasCompactSupport zeta)
    (hts : tsupport zeta ⊆ K) (u : Wkp (volume : Measure E) Omega p 2) :
    ∃ w : Wkp (volume : Measure E) ⊤ p 2,
      (Wkp.value 2 w : E → ℝ) =ᵐ[volume] K.indicator (fun x ↦ zeta x * Wkp.value 2 u x) ∧
      (Wkp.iteratedGradient 1 w : E → E →L[ℝ] E) =ᵐ[volume] K.indicator (fun x ↦
        zeta x • (Wkp.iteratedGradient 1 u x : E →L[ℝ] E) + cutoffRemainder zeta u x) ∧
      AEStronglyMeasurable (cutoffRemainder zeta u) (volume.restrict (Omega : Set E)) := by
  have hΩm := Omega.isOpen.measurableSet
  have hz : ∀ x ∉ K, zeta x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hts h)
  obtain ⟨w0, hw0, hwv⟩ :=
    Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul hp_top hzeta hcpt (hts.trans hKΩ) 2 u
  obtain ⟨W, rfl⟩ : ∃ W : Wkp0 (volume : Measure E) Omega p 2, (W : Wkp volume Omega p 2) = w0 :=
    ⟨⟨w0, hw0⟩, rfl⟩
  have hD0 := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hzeta hwv
  have hv := coeFn_extendByZeroLpₗᵢ ℝ hΩm.nullMeasurableSet (SetLike.coe_subset_coe.mpr le_top)
    (Wkp.value 2 (W : Wkp volume Omega p 2))
  have hD := Wkp0.iteratedGradient_extendByZeroₗᵢ_ae_eq_indicator le_top 1 W
  rw [Filter.EventuallyEq, Measure.ae_restrict_coe_opens_top] at hv hD
  refine ⟨Wkp0.extendByZeroₗᵢ le_top 2 W, ?_, ?_, ?_⟩
  · rw [Wkp0.value_extendByZeroₗᵢ]
    filter_upwards [hv, (ae_restrict_iff' hΩm).1 hwv] with x h₁ h₂
    rw [h₁]
    by_cases hxΩ : x ∈ (Omega : Set E)
    · rw [indicator_of_mem hxΩ, h₂ hxΩ]
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK]
      · rw [indicator_of_notMem hxK, hz x hxK, zero_mul]
    · rw [indicator_of_notMem hxΩ, indicator_of_notMem fun h ↦ hxΩ (hKΩ h)]
  · filter_upwards [hD, (ae_restrict_iff' hΩm).1 hD0] with x h₁ h₂
    rw [h₁]
    by_cases hxΩ : x ∈ (Omega : Set E)
    · rw [indicator_of_mem hxΩ, h₂ hxΩ]
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, cutoffRemainder]
      · rw [indicator_of_notMem hxK, hz x hxK, zero_smul, zero_add,
          leibnizRemainder_eq_zero_of_notMem_tsupport fun h ↦ hxK (hts h)]
    · rw [indicator_of_notMem hxΩ, indicator_of_notMem fun h ↦ hxΩ (hKΩ h)]
  · refine ((Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 (W : Wkp volume Omega p 2))).sub
      (hzeta.continuous.aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 u)))).congr ?_
    filter_upwards [hD0] with x hx
    simp only [Pi.sub_apply, Pi.smul_apply', cutoffRemainder]
    rw [hx, add_sub_cancel_left]

omit [Fact (1 ≤ q)] in
/-- **The forcing term of the localized equation lies in `L^q`.** If `a` is continuous and bounded
by `Λ` on a compact `K ⊆ Ω`, `ζ` is essentially bounded, and `f`, `u` and `∇u` lie in `L^q(Ω)`,
then `1_K (ζ f + tr (a T))` lies in `L^q(E)`, where `T` is the Leibniz remainder. -/
private theorem memLp_indicator_mul_add_traceCLM {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) {zeta : E → ℝ} (hzeta : ContDiff ℝ ∞ zeta) (hzetaTop : MemLp zeta ∞ volume)
    {a : E → E →L[ℝ] E} (ha : ContinuousOn a K) {Λ : ℝ} (haΛ : ∀ x ∈ K, ‖a x‖ ≤ Λ)
    (u : Wkp (volume : Measure E) Omega p 2) {f : E → ℝ}
    (hf : MemLp f q (volume.restrict (Omega : Set E)))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set E)))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set E)))
    (hR : AEStronglyMeasurable (cutoffRemainder zeta u) (volume.restrict (Omega : Set E))) :
    MemLp (K.indicator fun x ↦ zeta x * f x + traceCLM ℝ E ((a x).comp (cutoffRemainder zeta u x)))
      q volume := by
  have hKm := hK.measurableSet
  have hres : volume.restrict K ≤ volume.restrict (Omega : Set E) :=
    Measure.restrict_mono hKΩ le_rfl
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    (hzeta.continuous_gradient (by simp)).continuousOn
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
    ((hzeta.gradient_right (m := 1) (by simp)).continuous_fderiv (by simp)).continuousOn
  rw [memLp_indicator_iff_restrict hKm.nullMeasurableSet]
  refine ((hzetaTop.restrict K).fun_mul (hf.mono_measure hres)).add ?_
  have hmaj := (((hgq.mono_measure hres).norm.const_mul (2 * M₁)).add
    ((huq.mono_measure hres).norm.const_mul M₂)).const_mul (‖traceCLM ℝ E‖ * Λ)
  refine hmaj.of_le ((traceCLM ℝ E).continuous.comp_aestronglyMeasurable
    ((ContinuousLinearMap.compL ℝ E E E).aestronglyMeasurable_comp₂
      (ha.aestronglyMeasurable hKm) (hR.mono_measure hres))) ?_
  filter_upwards [ae_restrict_mem hKm] with x hx
  have hT : ‖cutoffRemainder zeta u x‖ ≤ 2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x‖ +
      M₂ * ‖Wkp.value 2 u x‖ := by
    refine (norm_leibnizRemainder_le zeta _ _ x).trans ?_
    gcongr
    exacts [hM₁ x hx, hM₂ x hx]
  refine le_trans ?_ (Real.le_norm_self _)
  calc ‖traceCLM ℝ E ((a x).comp (cutoffRemainder zeta u x))‖
      ≤ ‖traceCLM ℝ E‖ * (‖a x‖ * ‖cutoffRemainder zeta u x‖) :=
        ((traceCLM ℝ E).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((a x).opNorm_comp_le _) (norm_nonneg _))
    _ ≤ ‖traceCLM ℝ E‖ * (Λ * (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x‖ +
          M₂ * ‖Wkp.value 2 u x‖)) := by
        gcongr
        · exact (norm_nonneg _).trans (haΛ x hx)
        · exact haΛ x hx
    _ = _ := by simp only [Pi.add_apply, Real.norm_eq_abs]; ring

/-- **The localized equation.** If `D²w = 1_K (ζ D²u + T)` and `tr (a D²u) = f` on `Ω ⊇ K`, then
`tr (ã D²w) = 1_K (ζ f + tr (a T))` for `ã = A + 1_K (a - A)`, which is `a` on `K` and `A` off
`K`. -/
private theorem ae_trace_comp_eq_indicator {K : Set E} (hKΩ : K ⊆ Omega) {zeta : E → ℝ}
    {a : E → E →L[ℝ] E} (A : E →L[ℝ] E) {u : Wkp (volume : Measure E) Omega p 2} {f : E → ℝ}
    (htr : ∀ᵐ x ∂volume.restrict (Omega : Set E),
      LinearMap.trace ℝ E ((a x).comp (Wkp.iteratedGradient 1 u x)) = f x)
    {w : Wkp (volume : Measure E) ⊤ p 2}
    (hD : (Wkp.iteratedGradient 1 w : E → E →L[ℝ] E) =ᵐ[volume] K.indicator (fun x ↦
      zeta x • (Wkp.iteratedGradient 1 u x : E →L[ℝ] E) + cutoffRemainder zeta u x)) :
    ∀ᵐ x ∂volume, LinearMap.trace ℝ E
        ((A + K.indicator (fun y ↦ a y - A) x).comp (Wkp.iteratedGradient 1 w x)) =
      K.indicator (fun x ↦ zeta x * f x +
        traceCLM ℝ E ((a x).comp (cutoffRemainder zeta u x))) x := by
  filter_upwards [hD, (ae_restrict_iff' Omega.isOpen.measurableSet).1 htr] with x h₁ h₂
  rw [h₁]
  by_cases hxK : x ∈ K
  · have h₂' : traceCLM ℝ E ((a x).comp (Wkp.iteratedGradient 1 u x)) = f x := by
      rw [traceCLM_apply]; exact h₂ (hKΩ hxK)
    simp only [indicator_of_mem hxK, add_sub_cancel, ← traceCLM_apply]
    rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
    simp only [map_add, map_smul, h₂', smul_eq_mul]
  · rw [indicator_of_notMem hxK, indicator_of_notMem hxK, indicator_of_notMem hxK,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.toLinearMap_zero, map_zero]

/-- Restricting a whole-space `W^{2,q}` function whose value agrees with that of
`u ∈ W^{2,p}(Ω)` on an open `B ⊆ Ω` gives an element of `W^{2,q}(B)` with the value and the weak
Hessian of `u`. -/
private theorem exists_restrict_value_ae_eq {B : Opens E} (hB : B ≤ Omega)
    (u : Wkp (volume : Measure E) Omega p 2) (v₀ : Wkp (volume : Measure E) ⊤ q 2)
    (h : (Wkp.value 2 v₀ : E → ℝ) =ᵐ[volume.restrict (B : Set E)] Wkp.value 2 u) :
    ∃ v : Wkp (volume : Measure E) B q 2,
      (Wkp.value 2 v : E → ℝ) =ᵐ[volume.restrict (B : Set E)] Wkp.value 2 u ∧
      (Wkp.iteratedGradient 1 v : E → IteratedGradient E 1) =ᵐ[volume.restrict (B : Set E)]
        Wkp.iteratedGradient 1 u := by
  have hv := (Wkp.value_restrictL_ae le_top 2 v₀).trans h
  refine ⟨Wkp.restrictL le_top 2 v₀, hv, ?_⟩
  exact (Wkp.iteratedGradient_ae_eq_of_value_ae_eq 1
    (hv.trans (Wkp.value_restrictL_ae hB 2 u).symm)).trans
      (Wkp.iteratedGradient_restrictL_ae hB 1 u)

/-- **Interior `W^{2,q}` regularity for continuous principal coefficients** (Gilbarg–Trudinger,
Lemma 9.16). Let `1 < p, q < ∞`, let `Ω ⊆ E` be open, and let `a` be a field of endomorphisms of
`E`, continuous on `Ω`, with `λₓ ‖ξ‖² ≤ ⟪a(x) ξ, ξ⟫` for some `λₓ > 0` at each `x ∈ Ω`. Let
`u ∈ W^{2,p}(Ω)` solve `tr (a D²u) = f` almost everywhere on `Ω`, where `f`, the value of `u` and
its weak gradient `∇u = TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` lie in
`L^q(Ω)`. Then every `x₀ ∈ Ω` has a ball `B(x₀, ρ) ⊆ Ω` on which `u` lies in `W^{2,q}`: some
`v ∈ W^{2,q}(B(x₀, ρ))` has the value and the weak Hessian of `u` there.

No relation between `p` and `q` is assumed, and `a` need not be symmetric. Lower-order terms
`⟪b, ∇u⟫ + c u` with bounded measurable `b` and `c` are covered by moving them into `f`, which
keeps `f` in `L^q(Ω)` because `u` and `∇u` lie there. -/
theorem exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hq_top : q ≠ ⊤) {a : E → E →L[ℝ] E}
    (ha : ContinuousOn a Omega) (hell : ∀ x ∈ Omega, ∃ lam > 0, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ)
    (u : Wkp (volume : Measure E) Omega p 2) {f : E → ℝ}
    (hf : MemLp f q (volume.restrict (Omega : Set E)))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set E)))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set E)))
    (htr : ∀ᵐ x ∂volume.restrict (Omega : Set E),
      LinearMap.trace ℝ E ((a x).comp (Wkp.iteratedGradient 1 u x)) = f x)
    {x₀ : E} (hx₀ : x₀ ∈ Omega) :
    ∃ ρ > 0, ball x₀ ρ ⊆ Omega ∧
      ∃ v : Wkp (volume : Measure E) ⟨ball x₀ ρ, isOpen_ball⟩ q 2,
        (Wkp.value 2 v : E → ℝ) =ᵐ[volume.restrict (ball x₀ ρ)] Wkp.value 2 u ∧
        (Wkp.iteratedGradient 1 v : E → IteratedGradient E 1) =ᵐ[volume.restrict (ball x₀ ρ)]
          Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hgain⟩ :=
    exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le (E := E) hp hp_top hq
      hq_top
  obtain ⟨lam, hlam, hA⟩ := hell x₀ hx₀
  obtain ⟨ρ, hρ, hKΩ, hosc⟩ := exists_closedBall_subset_and_norm_sub_le ha hx₀ (mul_pos hδ hlam)
  set K := closedBall x₀ (2 * ρ)
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet
  have hBK : ball x₀ ρ ⊆ K :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ))
  -- A cutoff `ζ`, equal to `1` on `closedBall x₀ ρ` and supported in `B(x₀, 2ρ)`.
  obtain ⟨zeta, hzeta, hrange, hone, hcpt, hts⟩ :=
    (isCompact_closedBall x₀ ρ).exists_contDiff_cutoff isOpen_ball
      (closedBall_subset_ball (by linarith : ρ < 2 * ρ))
  have hzetaTop : MemLp zeta ∞ volume :=
    memLp_top_of_bound hzeta.continuous.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      obtain ⟨h₀, h₁⟩ := hrange (mem_range_self x)
      exact (Real.norm_eq_abs _).trans_le (abs_le.2 ⟨by linarith, h₁⟩))
  obtain ⟨w, hwv, hwD, hR⟩ := exists_wkp_value_ae_eq_indicator_mul hp_top hKΩ hzeta hcpt
    (hts.trans ball_subset_closedBall) u
  -- The whole-space integrability gain for `w = ζ u` and the coefficient `A + 1_K (a - A)`.
  obtain ⟨v₀, hv₀, -⟩ := hgain (a x₀) lam hlam hA
    (fun x ↦ a x₀ + K.indicator (fun y ↦ a y - a x₀) x)
    (aestronglyMeasurable_const.add ((aestronglyMeasurable_indicator_iff hKm).2
      (((ha.mono hKΩ).aestronglyMeasurable hKm).sub aestronglyMeasurable_const)))
    (ae_of_all _ fun x ↦ by
      rw [add_sub_cancel_left]
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]; exact hosc x hx
      · rw [indicator_of_notMem hx, norm_zero]; positivity)
    w _ (memLp_indicator_mul_add_traceCLM (isCompact_closedBall x₀ (2 * ρ)) hKΩ hzeta hzetaTop
      (ha.mono hKΩ) (Λ := ‖a x₀‖ + δ * lam) (fun x hx ↦
        (norm_le_norm_add_norm_sub' (a x) (a x₀)).trans (by linarith [hosc x hx])) u hf huq hgq hR)
    (((memLp_indicator_iff_restrict hKm.nullMeasurableSet).2
      ((hzetaTop.restrict K).fun_mul (huq.mono_measure (Measure.restrict_mono hKΩ le_rfl)))).ae_eq
        hwv.symm)
    (ae_trace_comp_eq_indicator hKΩ (a x₀) htr hwD)
  -- On `B(x₀, ρ)`, where `ζ = 1`, the value of `w` is that of `u`.
  refine ⟨ρ, hρ, hBK.trans hKΩ, exists_restrict_value_ae_eq (B := ⟨ball x₀ ρ, isOpen_ball⟩)
    (fun x hx ↦ hKΩ (hBK hx)) u v₀ ?_⟩
  filter_upwards [ae_restrict_of_ae (hv₀.trans hwv), ae_restrict_mem measurableSet_ball]
    with x h hx
  have h1 : zeta x = 1 := interior_subset (hone (ball_subset_closedBall hx))
  rw [h, indicator_of_mem (hBK hx), h1, one_mul]

end TauCeti
