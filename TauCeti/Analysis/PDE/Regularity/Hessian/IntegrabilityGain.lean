/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Resolvent
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.InnerProductSpace.Positive.Definite
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Affine
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Integrability gain for strong solutions with coefficients close to the identity

Let `E` be a finite-dimensional real inner product space and `1 < p, r < ∞`. This file proves the
core step of Gilbarg–Trudinger, Lemma 9.16: there is `δ > 0`, depending only on `E`, `p` and `r`,
such that whenever the principal coefficient `a` is uniformly within `δ` of the identity, every
strong solution `u ∈ W^{2,p}(E)` of

`tr (a D²u) = f`

with `u, f ∈ Lʳ(E)` lies in `W^{2,r}(E)`: it is the value of an element `v` of `W^{2,r}(E)`, with
the same weak Hessian
(`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le`). No
smoothness of `a` is needed, only measurability.

More generally the identity may be replaced by any operator `A` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫`, `λ > 0`,
when `‖a - A‖ ≤ δ λ`, with the same `δ`
(`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le`). This is the
form used to localize: freezing a continuous coefficient at a point gives the interior regularity
theorem of
`TauCeti.Analysis.PDE.Regularity.Hessian.ContinuousCoefficient.Regularity`.

## The argument

Write `b = a - 1`. The equation says `u - Δu = (u - f) + tr (b D²u)`. So `u` is a fixed point of

`Φ(z) = (1 - Δ)⁻¹ (u - f + tr (b D²z))`,

where `(1 - Δ)⁻¹ : Lˢ(E) → W^{2,s}(E)` is the inverse of `1 - Δ` for `s = p, r`
(`TauCeti.Wkp.oneSubLaplacianEquiv`). Since `|tr (b T)| ≤ ‖tr‖ δ ‖T‖`, `Φ` is a contraction of
`W^{2,s}(E)` with constant `1 / 2` for both `s = p` and `s = r` once `δ` is small compared with the
norms of the two inverses. The iterates `Φⁿ(0)` in the two spaces have the same values: the data
agree almost everywhere, because almost everywhere equal values have almost everywhere equal weak
Hessians, and on every `Lˢ` the operator `(1 - Δ)⁻¹` is convolution with the same kernel `G₁`
(`TauCeti.Wkp.value_oneSubLaplacianEquiv_symm_ae`). The iterates converge to `u` in `W^{2,p}` and
to the fixed point `v` of `Φ` in `W^{2,r}`, so in measure to both values, which therefore agree.

For a general `A`, write `(A + A†) / 2 = e e†` with `‖e⁻¹‖ ≤ λ^{-1/2}`
(`ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_two_inv_smul_add`). Since the
weak Hessian is self-adjoint, only the symmetric part of `a` enters the equation, and `u ∘ e` solves
`tr (b D²(u ∘ e)) = f ∘ e` with `b = e⁻¹ ((a + a†) / 2)(e ·) e⁻†`, which lies within `δ` of the
identity. Composition with `e` and `e⁻¹` preserves `W^{2,s}(E)` and `Lˢ(E)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16 and §9.5, and Section 6.1 (reduction of a constant-coefficient operator to the
  Laplacian by a linear change of variables).
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- The whole-space form of `TauCeti.Wkp.iteratedGradient_ae_eq_of_value_ae_eq` for the weak
Hessian, with almost everywhere taken for the volume. -/
private theorem iteratedGradient_ae_eq_of_value_ae_eq {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    {z₁ : Wkp (volume : Measure E) ⊤ p 2} {z₂ : Wkp (volume : Measure E) ⊤ r 2}
    (h : (Wkp.value 2 z₁ : E → ℝ) =ᵐ[volume] Wkp.value 2 z₂) :
    (Wkp.iteratedGradient 1 z₁ : E → IteratedGradient E 1) =ᵐ[volume]
      Wkp.iteratedGradient 1 z₂ := by
  rw [← Measure.ae_restrict_coe_opens_top (volume : Measure E)] at h ⊢
  exact Wkp.iteratedGradient_ae_eq_of_value_ae_eq 1 h

omit [MeasurableSpace E] [BorelSpace E] in
/-- The trace of `B ∘ T - B ∘ T'` is bounded by `‖tr‖ c ‖T - T'‖` when `‖B‖ ≤ c`. -/
private theorem norm_traceCLM_comp_sub_le {B : E →L[ℝ] E} {c : ℝ} (hB : ‖B‖ ≤ c)
    (T T' : E →L[ℝ] E) :
    ‖traceCLM ℝ E (B.comp T) - traceCLM ℝ E (B.comp T')‖ ≤ ‖traceCLM ℝ E‖ * c * ‖T - T'‖ := by
  rw [← map_sub, ← ContinuousLinearMap.comp_sub, mul_assoc]
  refine ((traceCLM ℝ E).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (B.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

section Perturbation

variable {s : ℝ≥0∞} [Fact (1 ≤ s)] {b : E → E →L[ℝ] E} {c : ℝ}

omit [Fact (1 ≤ s)] in
/-- For a bounded measurable field `b` of endomorphisms and `H ∈ Lˢ`, `x ↦ tr (b(x) ∘ H(x))` lies
in `Lˢ`. -/
private theorem memLp_traceCLM_comp (hb : AEStronglyMeasurable b volume)
    (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c)
    (H : Lp (IteratedGradient E 1) s ((volume : Measure E).restrict (⊤ : Opens E))) :
    MemLp (fun x ↦ traceCLM ℝ E ((b x).comp (H x))) s
      ((volume : Measure E).restrict (⊤ : Opens E)) := by
  refine ((Lp.memLp H).norm.const_mul (‖traceCLM ℝ E‖ * c)).of_le
    ((traceCLM ℝ E).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.compL ℝ E E E).aestronglyMeasurable_comp₂ hb.restrict
        (Lp.aestronglyMeasurable H))) ?_
  filter_upwards [ae_restrict_of_ae hbc] with x hx
  have h := norm_traceCLM_comp_sub_le hx (H x) 0
  simp only [ContinuousLinearMap.comp_zero, map_zero, sub_zero] at h
  exact h.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)

/-- The perturbation `x ↦ tr (b(x) ∘ D²z(x))` of `1 - Δ`, as an element of `Lˢ`. -/
private def perturbation (hb : AEStronglyMeasurable b volume) (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c)
    (z : Wkp (volume : Measure E) ⊤ s 2) : Lp ℝ s ((volume : Measure E).restrict (⊤ : Opens E)) :=
  (memLp_traceCLM_comp hb hbc (Wkp.iteratedGradient 1 z)).toLp _

/-- `TauCeti.perturbation` is represented by `x ↦ tr (b(x) ∘ D²z(x))`. -/
private theorem perturbation_ae (hb : AEStronglyMeasurable b volume)
    (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c) (z : Wkp (volume : Measure E) ⊤ s 2) :
    (perturbation hb hbc z : E → ℝ) =ᵐ[(volume : Measure E).restrict (⊤ : Opens E)]
      fun x ↦ traceCLM ℝ E ((b x).comp (Wkp.iteratedGradient 1 z x)) :=
  MemLp.coeFn_toLp _

/-- The perturbation is Lipschitz with constant `‖tr‖ c`. -/
private theorem norm_perturbation_sub_le (hb : AEStronglyMeasurable b volume)
    (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c) (z z' : Wkp (volume : Measure E) ⊤ s 2) :
    ‖perturbation hb hbc z - perturbation hb hbc z'‖ ≤ ‖traceCLM ℝ E‖ * c * ‖z - z'‖ := by
  have hc : 0 ≤ c := by
    obtain ⟨x, hx⟩ := hbc.exists
    exact (norm_nonneg _).trans hx
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := Wkp.iteratedGradient 1 (z - z')) ?_).trans
    (mul_le_mul_of_nonneg_left (Wkp.norm_iteratedGradient_le 1 _) (by positivity))
  rw [Wkp.iteratedGradient_sub]
  filter_upwards [Lp.coeFn_sub (perturbation hb hbc z) (perturbation hb hbc z'),
    perturbation_ae hb hbc z, perturbation_ae hb hbc z',
    Lp.coeFn_sub (Wkp.iteratedGradient 1 z) (Wkp.iteratedGradient 1 z'),
    ae_restrict_of_ae hbc] with x h₁ h₂ h₃ h₄ hx
  rw [h₁, Pi.sub_apply, h₂, h₃, h₄, Pi.sub_apply]
  exact norm_traceCLM_comp_sub_le hx _ _

/-- The fixed-point map `z ↦ (1 - Δ)⁻¹ (g + tr (b ∘ D²z))` on `W^{2,s}(E)`. -/
private def iterationMap (hs : 1 < s) (hs_top : s ≠ ⊤) (hb : AEStronglyMeasurable b volume)
    (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c) (g : Lp ℝ s ((volume : Measure E).restrict (⊤ : Opens E)))
    (z : Wkp (volume : Measure E) ⊤ s 2) : Wkp (volume : Measure E) ⊤ s 2 :=
  (Wkp.oneSubLaplacianEquiv (E := E) hs hs_top).symm (g + perturbation hb hbc z)

/-- The fixed-point map is a contraction with constant `1 / 2` once `K ‖tr‖ c ≤ 1 / 2`, where `K`
bounds the inverse of `1 - Δ`. -/
private theorem contractingWith_iterationMap (hs : 1 < s) (hs_top : s ≠ ⊤)
    (hb : AEStronglyMeasurable b volume) (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c)
    (g : Lp ℝ s ((volume : Measure E).restrict (⊤ : Opens E))) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ f, ‖(Wkp.oneSubLaplacianEquiv (E := E) hs hs_top).symm f‖ ≤ K * ‖f‖)
    (hKc : K * ‖traceCLM ℝ E‖ * c ≤ 2⁻¹) :
    ContractingWith 2⁻¹ (iterationMap hs hs_top hb hbc g) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, iterationMap, iterationMap, ← map_sub,
    add_sub_add_left_eq_sub]
  calc _ ≤ K * ‖perturbation hb hbc z - perturbation hb hbc z'‖ := hK _
    _ ≤ K * (‖traceCLM ℝ E‖ * c * ‖z - z'‖) :=
        mul_le_mul_of_nonneg_left (norm_perturbation_sub_le hb hbc z z') hK0
    _ = K * ‖traceCLM ℝ E‖ * c * ‖z - z'‖ := by ring
    _ ≤ 2⁻¹ * ‖z - z'‖ := mul_le_mul_of_nonneg_right hKc (norm_nonneg _)
    _ = _ := by norm_num

end Perturbation

/-- The fixed-point maps in `W^{2,p}(E)` and `W^{2,r}(E)` preserve almost everywhere equality of
values, when their data agree almost everywhere: both are convolution with `G₁`. -/
private theorem value_iterationMap_ae_eq {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r) (hr_top : r ≠ ⊤) {b : E → E →L[ℝ] E} {c : ℝ}
    (hb : AEStronglyMeasurable b volume) (hbc : ∀ᵐ x ∂volume, ‖b x‖ ≤ c)
    {g₁ : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E))}
    {g₂ : Lp ℝ r ((volume : Measure E).restrict (⊤ : Opens E))} (hg : (g₁ : E → ℝ) =ᵐ[volume] g₂)
    {z₁ : Wkp (volume : Measure E) ⊤ p 2} {z₂ : Wkp (volume : Measure E) ⊤ r 2}
    (hz : (Wkp.value 2 z₁ : E → ℝ) =ᵐ[volume] Wkp.value 2 z₂) :
    (Wkp.value 2 (iterationMap hp hp_top hb hbc g₁ z₁) : E → ℝ) =ᵐ[volume]
      Wkp.value 2 (iterationMap hr hr_top hb hbc g₂ z₂) := by
  have hdata : ((g₁ + perturbation hb hbc z₁ : Lp ℝ p _) : E → ℝ) =ᵐ[volume]
      (g₂ + perturbation hb hbc z₂ : Lp ℝ r _) := by
    rw [← Measure.ae_restrict_coe_opens_top (volume : Measure E)] at hg ⊢
    filter_upwards [Lp.coeFn_add g₁ (perturbation hb hbc z₁),
      Lp.coeFn_add g₂ (perturbation hb hbc z₂), hg, perturbation_ae hb hbc z₁,
      perturbation_ae hb hbc z₂, ae_restrict_of_ae (iteratedGradient_ae_eq_of_value_ae_eq hz)]
      with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄, h₅, h₆]
  unfold iterationMap
  refine (Wkp.value_oneSubLaplacianEquiv_symm_ae hp hp_top _).trans ?_
  rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) hdata]
  exact (Wkp.value_oneSubLaplacianEquiv_symm_ae hr hr_top _).symm

/-- Two contractions of `W^{2,p}(E)` and `W^{2,r}(E)` which preserve almost everywhere equality of
values have fixed points with almost everywhere equal values. -/
private theorem exists_value_ae_eq_of_contractingWith {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    {Φp : Wkp (volume : Measure E) ⊤ p 2 → Wkp (volume : Measure E) ⊤ p 2}
    {Φr : Wkp (volume : Measure E) ⊤ r 2 → Wkp (volume : Measure E) ⊤ r 2} {Kp Kr : ℝ≥0}
    (hΦp : ContractingWith Kp Φp) (hΦr : ContractingWith Kr Φr)
    (hΦ : ∀ z₁ z₂, (Wkp.value 2 z₁ : E → ℝ) =ᵐ[volume] Wkp.value 2 z₂ →
      (Wkp.value 2 (Φp z₁) : E → ℝ) =ᵐ[volume] Wkp.value 2 (Φr z₂))
    {u : Wkp (volume : Measure E) ⊤ p 2} (hu : Function.IsFixedPt Φp u) :
    ∃ v : Wkp (volume : Measure E) ⊤ r 2, (Wkp.value 2 v : E → ℝ) =ᵐ[volume] Wkp.value 2 u := by
  -- The iterates from `0` have almost everywhere equal values.
  have hiter : ∀ n, (Wkp.value 2 (Φp^[n] 0) : E → ℝ) =ᵐ[volume] Wkp.value 2 (Φr^[n] 0) := by
    intro n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Wkp.value_zero']
      exact ((Lp.coeFn_zero ℝ p _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top).trans
        ((Lp.coeFn_zero ℝ r _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hΦ _ _ ih
  have hlimp := hΦp.tendsto_iterate_fixedPoint 0
  rw [← hΦp.fixedPoint_unique hu] at hlimp
  have h₁ := tendstoInMeasure_of_tendsto_Lp (Wkp.tendsto_value hlimp)
  have h₂ := tendstoInMeasure_of_tendsto_Lp (Wkp.tendsto_value (hΦr.tendsto_iterate_fixedPoint 0))
  refine ⟨ContractingWith.fixedPoint Φr hΦr, ?_⟩
  rw [← Measure.ae_restrict_coe_opens_top (volume : Measure E)]
  exact tendstoInMeasure_ae_unique h₂ (h₁.congr_left fun n ↦ ae_restrict_of_ae (hiter n))

/-- The smallness condition on `δ`: `K n δ ≤ 1 / 2` for `δ = 1 / (2 (Kp + Kr + 1) (n + 1))`
and `K ≤ Kp + Kr`. -/
private theorem mul_mul_inv_le_inv_two {Kp Kr n K : ℝ} (hKp : 0 ≤ Kp) (hKr : 0 ≤ Kr) (hn : 0 ≤ n)
    (hK : K ≤ Kp + Kr) : K * n * (2 * ((Kp + Kr + 1) * (n + 1)))⁻¹ ≤ 2⁻¹ := by
  have hM : 0 < (Kp + Kr + 1) * (n + 1) := by positivity
  have h : K * n ≤ (Kp + Kr + 1) * (n + 1) :=
    mul_le_mul (by linarith) (by linarith) hn (by positivity)
  calc K * n * (2 * ((Kp + Kr + 1) * (n + 1)))⁻¹
      ≤ (Kp + Kr + 1) * (n + 1) * (2 * ((Kp + Kr + 1) * (n + 1)))⁻¹ := by gcongr
    _ = 2⁻¹ := by rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hM.ne', mul_one]

/-- **Integrability gain for strong solutions with coefficients close to the identity**
(Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, r < ∞`. There is `δ > 0`, depending only on `E`, `p`
and `r`, with the following property. Let `a` be a measurable field of endomorphisms of `E` with
`‖a(x) - 1‖ ≤ δ` almost everywhere, and let `u ∈ W^{2,p}(E)` solve `tr (a D²u) = f` almost
everywhere, where `u, f ∈ Lʳ(E)`. Then `u ∈ W^{2,r}(E)`: its value is the value of an element `v`
of `W^{2,r}(E)`, and the weak Hessians of `u` and `v` agree almost everywhere. -/
theorem exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r)
    (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : E → E →L[ℝ] E, AEStronglyMeasurable a volume →
      (∀ᵐ x ∂volume, ‖a x - ContinuousLinearMap.id ℝ E‖ ≤ δ) →
      ∀ (u : Wkp (volume : Measure E) ⊤ p 2) (f : E → ℝ), MemLp f r volume →
        MemLp (Wkp.value 2 u : E → ℝ) r volume →
        (∀ᵐ x ∂volume, LinearMap.trace ℝ E ((a x).comp (Wkp.iteratedGradient 1 u x)) = f x) →
        ∃ v : Wkp (volume : Measure E) ⊤ r 2,
          (Wkp.value 2 v : E → ℝ) =ᵐ[volume] Wkp.value 2 u ∧
          (Wkp.iteratedGradient 1 v : E → IteratedGradient E 1) =ᵐ[volume]
            Wkp.iteratedGradient 1 u := by
  obtain ⟨Kp, hKp0, hKp⟩ := Wkp.exists_norm_oneSubLaplacianEquiv_symm_le (E := E) hp hp_top
  obtain ⟨Kr, hKr0, hKr⟩ := Wkp.exists_norm_oneSubLaplacianEquiv_symm_le (E := E) hr hr_top
  have hn := norm_nonneg (traceCLM ℝ E)
  -- With `δ = 1 / (2 (Kp + Kr + 1) (‖tr‖ + 1))`, both fixed-point maps contract.
  refine ⟨(2 * ((Kp + Kr + 1) * (‖traceCLM ℝ E‖ + 1)))⁻¹, by positivity,
    fun a ha hδ u f hf hur htr ↦ ?_⟩
  -- The equation `tr (a D²u) = f` says that `u` is a fixed point for the data `u - f`.
  have hb : AEStronglyMeasurable (fun x ↦ a x - ContinuousLinearMap.id ℝ E) volume :=
    ha.sub aestronglyMeasurable_const
  obtain ⟨gp, hgp⟩ : ∃ g, g = Wkp.oneSubLaplacianL u - perturbation hb hδ u := ⟨_, rfl⟩
  have hfr : MemLp (fun x ↦ Wkp.value 2 u x - f x) r
      ((volume : Measure E).restrict (⊤ : Opens E)) :=
    (hur.sub hf).mono_measure Measure.restrict_le_self
  have hg : (gp : E → ℝ) =ᵐ[volume] hfr.toLp _ := by
    rw [← Measure.ae_restrict_coe_opens_top (volume : Measure E)]
    filter_upwards [hgp ▸ Lp.coeFn_sub (Wkp.oneSubLaplacianL u) (perturbation hb hδ u),
      ae_restrict_of_ae (Wkp.oneSubLaplacianL_ae u), perturbation_ae hb hδ u,
      ae_restrict_of_ae htr, hfr.coeFn_toLp] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.sub_apply, h₂, h₃, h₅, ← h₄, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp, map_sub, traceCLM_apply, traceCLM_apply]
    ring
  have hu : Function.IsFixedPt (iterationMap hp hp_top hb hδ gp) u := by
    rw [Function.IsFixedPt, iterationMap, hgp, sub_add_cancel,
      Wkp.oneSubLaplacianEquiv_symm_oneSubLaplacianL]
  obtain ⟨v, hv⟩ := exists_value_ae_eq_of_contractingWith
    (contractingWith_iterationMap hp hp_top hb hδ gp hKp0 hKp
      (mul_mul_inv_le_inv_two hKp0 hKr0 hn (by linarith)))
    (contractingWith_iterationMap hr hr_top hb hδ (hfr.toLp _) hKr0 hKr
      (mul_mul_inv_le_inv_two hKp0 hKr0 hn (by linarith)))
    (fun _ _ hz ↦ value_iterationMap_ae_eq hp hp_top hr hr_top hb hδ hg hz) hu
  exact ⟨v, hv, iteratedGradient_ae_eq_of_value_ae_eq hv⟩

/-! ### A general frozen coefficient -/

/-- **Integrability gain for strong solutions with coefficients close to a frozen elliptic
operator** (Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, r < ∞`. There is `δ > 0`, depending only
on `E`, `p` and `r`, with the following property. Let `A` be an operator on `E` with
`λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `0 < λ`, and let `a` be a measurable field of endomorphisms of `E` with
`‖a(x) - A‖ ≤ δ λ` almost everywhere. Let `u ∈ W^{2,p}(E)` solve `tr (a D²u) = f` almost
everywhere, where `u, f ∈ Lʳ(E)`. Then `u ∈ W^{2,r}(E)`: its value is the value of an element `v`
of `W^{2,r}(E)`, and the weak Hessians of `u` and `v` agree almost everywhere.

Neither `A` nor `a` need be symmetric. -/
theorem exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_le
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hp : 1 < p) (hp_top : p ≠ ⊤) (hr : 1 < r)
    (hr_top : r ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (A : E →L[ℝ] E) (lam : ℝ), 0 < lam →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) →
      ∀ a : E → E →L[ℝ] E, AEStronglyMeasurable a volume →
      (∀ᵐ x ∂volume, ‖a x - A‖ ≤ δ * lam) →
      ∀ (u : Wkp (volume : Measure E) ⊤ p 2) (f : E → ℝ), MemLp f r volume →
        MemLp (Wkp.value 2 u : E → ℝ) r volume →
        (∀ᵐ x ∂volume, LinearMap.trace ℝ E ((a x).comp (Wkp.iteratedGradient 1 u x)) = f x) →
        ∃ v : Wkp (volume : Measure E) ⊤ r 2,
          (Wkp.value 2 v : E → ℝ) =ᵐ[volume] Wkp.value 2 u ∧
          (Wkp.iteratedGradient 1 v : E → IteratedGradient E 1) =ᵐ[volume]
            Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hid⟩ :=
    exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_norm_sub_id_le (E := E) hp
      hp_top hr hr_top
  refine ⟨δ, hδ, fun A lam hlam hA a ha haA u f hf hur htr ↦ ?_⟩
  obtain ⟨e, hee, -, he⟩ := A.exists_continuousLinearEquiv_comp_adjoint_eq_two_inv_smul_add hlam
    (fun ξ ↦ by rw [RCLike.re_to_real]; exact hA ξ) (ν := 0)
  have hqe := e.toContinuousAddEquiv.quasiMeasurePreserving_addHaar volume volume
  rw [ContinuousLinearEquiv.toContinuousAddEquiv_coe] at hqe
  have hMN : (e : E →L[ℝ] E) ∘L (e.symm : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    ext x; simp
  -- `w = u ∘ e ∈ W^{2,p}(E)` has weak Hessian `e† D²u(e ·) e`.
  set w := Wkp.compAffineEquiv (U := ⊤) volume e 0 (by simp) 2 u
  have hwv : (Wkp.value 2 w : E → ℝ) =ᵐ[volume] fun x ↦ Wkp.value 2 u (e x) := by
    simpa [Measure.ae_restrict_coe_opens_top] using
      Wkp.value_compAffineEquiv_ae (U := ⊤) volume e 0 (by simp) 2 u
  have hwD : Wkp.iteratedGradient 1 w =ᵐ[volume] fun x ↦
      (e : E →L[ℝ] E).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L (e : E →L[ℝ] E) := by
    simpa [Measure.ae_restrict_coe_opens_top] using
      Wkp.iteratedGradient_one_compAffineEquiv_ae (U := ⊤) volume e 0 (by simp) u
  have hadj := hqe.ae ((Measure.ae_restrict_coe_opens_top (volume : Measure E)) ▸
    Wkp.adjoint_iteratedGradient_one_ae_eq u)
  -- It solves `tr (b D²w) = f ∘ e` with `b(y) = e⁻¹ ((a + a†) / 2)(e y) e⁻†` close to `1`.
  obtain ⟨v', hv', -⟩ := hid (fun y ↦ (e.symm : E →L[ℝ] E) ∘L ((2⁻¹ : ℝ) • (a (e y) +
      (a (e y)).adjoint)) ∘L (e.symm : E →L[ℝ] E).adjoint)
    ((ContinuousLinearMap.continuous_conj_symmPart _).comp_aestronglyMeasurable
      (ha.comp_quasiMeasurePreserving hqe))
    (by
      filter_upwards [hqe.ae haA] with y hy
      exact ContinuousLinearMap.norm_conj_symmPart_sub_id_le_of_norm_sub_le hlam e hee he hy)
    w _ (hf.comp_continuousLinearEquiv e)
    ((hur.comp_continuousLinearEquiv e).ae_eq hwv.symm)
    (by
      filter_upwards [hwD, hadj, hqe.ae htr] with y h₁ h₂ h₃
      rw [h₁, ← traceCLM_apply,
        ContinuousLinearMap.traceCLM_conj_symmPart_comp_of_comp_eq_id hMN _ _ h₂, traceCLM_apply,
        h₃])
  -- Composing back with `e⁻¹` gives `v ∈ W^{2,r}(E)` with value `u`.
  set v := Wkp.compAffineEquiv (U := ⊤) volume e.symm 0 (by simp) 2 v'
  have hvs := Wkp.value_compAffineEquiv_ae (U := ⊤) volume e.symm 0 (by simp) 2 v'
  rw [Measure.ae_restrict_coe_opens_top] at hvs
  have hv : (Wkp.value 2 v : E → ℝ) =ᵐ[volume] Wkp.value 2 u := by
    filter_upwards [hvs,
      (e.symm.toContinuousAddEquiv.quasiMeasurePreserving_addHaar volume volume).ae
        (hv'.trans hwv)] with y h₁ h₂
    rw [ContinuousLinearEquiv.toContinuousAddEquiv_coe] at h₂
    rw [h₁, add_zero, h₂, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨v, hv, iteratedGradient_ae_eq_of_value_ae_eq hv⟩

end TauCeti
