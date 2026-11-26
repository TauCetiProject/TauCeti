/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.Calculus.Gradient

/-!
# Freezing the coefficients of a localized trace-form equation

Let `E` be a finite-dimensional real inner product space and `Ω ⊆ E` open. Let `u ∈ W^{2,p}(Ω)`
solve `tr (A D²u) = f` almost everywhere on `Ω`, and let `ζ` be a smooth cutoff supported in a
compact set `K`. This file collects the pointwise and integrability facts behind the standard
localization of such an equation by `ζ`, with the coefficient frozen at an operator `A₀` off
`Ω ∩ K` (Gilbarg–Trudinger, proofs of Theorem 9.11 and Lemma 9.16). They are shared by the
interior and the flat-boundary forms of Lemma 9.16
(`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn` and
`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_normalHalfSpace`).

* `TauCeti.exists_ball_subset_forall_norm_sub_le`: a coefficient continuous within `Ω` at `x`, and
  elliptic at `x` when `x` lies in the closure of `Ω`, stays within `δ λ` of an elliptic operator
  `A₀` with constant `λ` on `Ω ∩ B(x, ρ)` for some small ball `B(x, ρ)`. Only the flat-boundary
  results use this form, which also covers points `x` on or outside the boundary of `Ω`.
* `TauCeti.aestronglyMeasurable_add_indicator_sub_and_norm_sub_le`: the frozen coefficient
  `Ã = A₀ + 1_s (A - A₀)` is measurable, and within `ε` of `A₀` everywhere when `A` is on `s`.
* `TauCeti.memLp_indicator_mul_add_traceCLM_comp_leibnizRemainder`: the forcing term
  `1_{Ω ∩ K} (ζ f + tr (A T))` of the localized equation lies in `L^q`, where
  `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is the Leibniz remainder of the cutoff `ζ u`.
* `TauCeti.ae_traceCLM_add_indicator_sub_comp_eq_indicator`: if `D = 1_Ω (ζ D²u + T)`, then
  `tr (Ã D) = 1_{Ω ∩ K} (ζ f + tr (A T))` for `Ã = A₀ + 1_{Ω ∩ K} (A - A₀)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16, and the proof of Theorem 9.11 (freezing the coefficients and localizing by a
  cutoff).
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Gradient ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  {Omega : Opens E}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
open Metric InnerProductSpace in
/-- **Frozen coefficients near a point.** Let `A` be continuous within `Ω` at `x ∈ U`, and elliptic
at `x` if `x` lies in the closure of `Ω`. Then for every `δ > 0` there are an operator `A₀` with
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫`, `0 < λ`, and a ball `B(x, ρ) ⊆ U` with `‖A y - A₀‖ ≤ δ λ` for every
`y ∈ Ω ∩ B(x, ρ)`: `A₀ = A x` if `x` lies in the closure of `Ω`, and the identity otherwise, when
a small ball about `x` misses `Ω`. -/
theorem exists_ball_subset_forall_norm_sub_le {Omega U : Set E} (hU : IsOpen U)
    {A : E → E →L[ℝ] E} {x : E} (hxU : x ∈ U) (hcont : ContinuousWithinAt A Omega x)
    (hell : x ∈ closure Omega → ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₀ : E →L[ℝ] E, ∃ lam : ℝ, 0 < lam ∧
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ U ∧
        ∀ y ∈ Omega, y ∈ ball x ρ → ‖A y - A₀‖ ≤ δ * lam := by
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub (ρ₁ : ℝ) : ball x (min ρ₀ ρ₁) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρ₀U
  by_cases hx : x ∈ closure Omega
  · obtain ⟨lam, hlam, hA⟩ := hell hx
    -- `y ↦ ‖A y - A x‖` is continuous within `Ω` at `x`, where it vanishes.
    have hg : ContinuousWithinAt (fun y => ‖A y - A x‖) Omega x :=
      ContinuousWithinAt.norm (f := fun y => A y - A x) (hcont.sub continuousWithinAt_const)
    have h0 : ‖A x - A x‖ ≤ 0 := ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v => by
      rw [sub_apply, sub_self, norm_zero, zero_mul]
    have hev := hg.eventually (Iio_mem_nhds (h0.trans_lt (mul_pos hδ hlam)))
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨ρ₁, hρ₁, hρ₁A⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨A x, lam, hlam, hA, min ρ₀ ρ₁, lt_min hρ₀ hρ₁, hsub ρ₁, fun y hyΩ hy =>
      (hρ₁A ((mem_ball.1 hy).trans_le (min_le_right _ _)) hyΩ).le⟩
  · obtain ⟨ρ₁, hρ₁, hρ₁Ω⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
    refine ⟨ContinuousLinearMap.id ℝ _, 1, one_pos, fun ξ => by
      rw [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, one_mul], min ρ₀ ρ₁,
      lt_min hρ₀ hρ₁, hsub ρ₁, fun y hyΩ hy => ?_⟩
    exact absurd (subset_closure hyΩ) (hρ₁Ω (ball_subset_ball (min_le_right _ _) hy))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Freezing a coefficient field off a set.** If `A` is measurable on a measurable set `s` and
within `ε` of an operator `A₀` there, then `A₀ + 1_s (A - A₀)`, which is `A` on `s` and `A₀`
elsewhere, is measurable and within `ε` of `A₀` everywhere. -/
theorem aestronglyMeasurable_add_indicator_sub_and_norm_sub_le {μ : Measure E} {s : Set E}
    (hs : MeasurableSet s) {A₀ : E →L[ℝ] E} {A : E → E →L[ℝ] E}
    (hA : AEStronglyMeasurable A (μ.restrict s)) {ε : ℝ} (hε : 0 ≤ ε)
    (hAε : ∀ x ∈ s, ‖A x - A₀‖ ≤ ε) :
    AEStronglyMeasurable (fun x ↦ A₀ + s.indicator (fun y ↦ A y - A₀) x) μ ∧
      ∀ x, ‖A₀ + s.indicator (fun y ↦ A y - A₀) x - A₀‖ ≤ ε :=
  ⟨aestronglyMeasurable_const.add
    ((aestronglyMeasurable_indicator_iff hs).2 (hA.sub aestronglyMeasurable_const)), fun x ↦ by
    rw [add_sub_cancel_left]
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]; exact hAε x hx
    · rw [indicator_of_notMem hx, ContinuousLinearMap.opNorm_zero]; exact hε⟩

omit [Fact (1 ≤ q)] in
/-- **The forcing term of a localized equation lies in `L^q`.** Let `K` be compact, let `a` be a
field of endomorphisms of `E`, measurable on `Ω` and bounded by `Λ` on `Ω ∩ K`, let `ζ` be smooth
and essentially bounded, and let `f`, `u` and `∇u` lie in `L^q(Ω)`. Then
`1_{Ω ∩ K} (ζ f + tr (a T))` lies in `L^q(E)`, where `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is the Leibniz
remainder of the cutoff `ζ u` (`TauCeti.leibnizRemainder`), assumed measurable on `Ω`. -/
theorem memLp_indicator_mul_add_traceCLM_comp_leibnizRemainder {K : Set E} (hK : IsCompact K)
    {zeta : E → ℝ} (hzeta : ContDiff ℝ ∞ zeta) (hzetaTop : MemLp zeta ∞ volume)
    {a : E → E →L[ℝ] E} (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set E))) {Λ : ℝ}
    (haΛ : ∀ x ∈ (Omega : Set E) ∩ K, ‖a x‖ ≤ Λ) (u : Wkp (volume : Measure E) Omega p 2)
    {f : E → ℝ} (hf : MemLp f q (volume.restrict (Omega : Set E)))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set E)))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set E)))
    (hR : AEStronglyMeasurable (fun x ↦ leibnizRemainder zeta
      (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x)
      (volume.restrict (Omega : Set E))) :
    MemLp (((Omega : Set E) ∩ K).indicator fun x ↦ zeta x * f x + traceCLM ℝ E ((a x).comp
      (leibnizRemainder zeta (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x)))
      q volume := by
  have hΩK : MeasurableSet ((Omega : Set E) ∩ K) :=
    Omega.isOpen.measurableSet.inter hK.measurableSet
  have hres : volume.restrict ((Omega : Set E) ∩ K) ≤ volume.restrict (Omega : Set E) :=
    Measure.restrict_mono inter_subset_left le_rfl
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    (hzeta.continuous_gradient (by simp)).continuousOn
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
    ((hzeta.gradient_right (m := 1) (by simp)).continuous_fderiv (by simp)).continuousOn
  rw [memLp_indicator_iff_restrict hΩK.nullMeasurableSet]
  refine ((hzetaTop.restrict _).fun_mul (hf.mono_measure hres)).add ?_
  have hmaj := (((hgq.mono_measure hres).norm.const_mul (2 * M₁)).add
    ((huq.mono_measure hres).norm.const_mul M₂)).const_mul (‖traceCLM ℝ E‖ * Λ)
  refine hmaj.of_le (Continuous.comp_aestronglyMeasurable₂
    (g := fun B M : E →L[ℝ] E ↦ traceCLM ℝ E (B.comp M))
    ((traceCLM ℝ E).continuous.comp (continuous_fst.clm_comp continuous_snd))
    (ha.mono_measure hres) (hR.mono_measure hres)) ?_
  filter_upwards [ae_restrict_mem hΩK] with x hx
  have hT : ‖leibnizRemainder zeta (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
      (Wkp.value 2 u x) x‖ ≤
      2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x‖ + M₂ * ‖Wkp.value 2 u x‖ := by
    refine (norm_leibnizRemainder_le zeta _ _ x).trans ?_
    gcongr
    exacts [hM₁ x hx.2, hM₂ x hx.2]
  refine le_trans ?_ (Real.le_norm_self _)
  calc ‖traceCLM ℝ E ((a x).comp (leibnizRemainder zeta
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x))‖
      ≤ ‖traceCLM ℝ E‖ * (‖a x‖ * ‖leibnizRemainder zeta
          (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x‖) :=
        ((traceCLM ℝ E).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((a x).opNorm_comp_le _) (norm_nonneg _))
    _ ≤ ‖traceCLM ℝ E‖ * (Λ * (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x‖ +
          M₂ * ‖Wkp.value 2 u x‖)) := by
        gcongr
        · exact (norm_nonneg _).trans (haΛ x hx)
        · exact haΛ x hx
    _ = _ := by simp only [Pi.add_apply, Real.norm_eq_abs]; ring

/-- **The localized equation.** Let `ζ` vanish off `K`, let `u ∈ W^{2,p}(Ω)` solve
`tr (A D²u) = f` at almost every point of `Ω`, and let `D = 1_Ω (ζ D²u + T)` almost everywhere,
where `T` is the Leibniz remainder of the cutoff `ζ u`. Then almost everywhere
`tr (Ã D) = 1_{Ω ∩ K} (ζ f + tr (A T))` for the frozen coefficient `Ã = A₀ + 1_{Ω ∩ K} (A - A₀)`,
which is `A` on `Ω ∩ K` and `A₀` elsewhere. -/
theorem ae_traceCLM_add_indicator_sub_comp_eq_indicator {μ : Measure E} {K : Set E}
    {zeta : E → ℝ} (htsK : tsupport zeta ⊆ K) (A₀ : E →L[ℝ] E) {A : E → E →L[ℝ] E}
    {u : Wkp (volume : Measure E) Omega p 2} {f : E → ℝ}
    (htr : ∀ᵐ x ∂μ, x ∈ (Omega : Set E) →
      traceCLM ℝ E (A x ∘L Wkp.iteratedGradient 1 u x) = f x)
    {D : E → E →L[ℝ] E}
    (hD : ∀ᵐ x ∂μ, D x = (Omega : Set E).indicator (fun x ↦
      zeta x • Wkp.iteratedGradient 1 u x + leibnizRemainder zeta
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x) x) :
    ∀ᵐ x ∂μ, traceCLM ℝ E ((A₀ + ((Omega : Set E) ∩ K).indicator (fun y ↦ A y - A₀) x) ∘L D x) =
      ((Omega : Set E) ∩ K).indicator (fun x ↦
        zeta x * f x + traceCLM ℝ E (A x ∘L leibnizRemainder zeta
          (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x)) x := by
  filter_upwards [hD, htr] with x h₁ h₂
  rw [h₁]
  by_cases hxΩ : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxΩ]
    by_cases hxK : x ∈ K
    · have hx : x ∈ (Omega : Set E) ∩ K := ⟨hxΩ, hxK⟩
      rw [indicator_of_mem hx, indicator_of_mem hx, add_sub_cancel, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.comp_smul, map_add, map_smul, smul_eq_mul, h₂ hxΩ]
    · have hx : x ∉ (Omega : Set E) ∩ K := fun h ↦ hxK h.2
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxK (htsK h), zero_smul, zero_add,
        leibnizRemainder_eq_zero_of_notMem_tsupport (fun h ↦ hxK (htsK h)),
        ContinuousLinearMap.comp_zero, map_zero, indicator_of_notMem hx]
  · have hx : x ∉ (Omega : Set E) ∩ K := fun h ↦ hxΩ h.1
    rw [indicator_of_notMem hxΩ, ContinuousLinearMap.comp_zero, map_zero, indicator_of_notMem hx]

end TauCeti
