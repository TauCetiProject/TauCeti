/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.LocalApproximation
public import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
public import TauCeti.MeasureTheory.Function.Lp.L1Convergence

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The chain rule and the positive part in `W^{1,p}(Ω)` for `p < ∞`

For `1 ≤ p < ∞`, `W^{1,p}(Ω)` is stable under composition with a Lipschitz `C¹` function `F`
vanishing at `0`, and the weak gradient obeys the classical chain rule

`∇(F ∘ u) = F'(u) ∇u`.

In the same exponent range, its limiting case is the **truncation** property:
`u⁺ ∈ W^{1,p}(Ω)`, with

`∇(u⁺) = 1_{u > 0} ∇u`,

which is the starting point of the truncation arguments of elliptic regularity: the Caccioppoli
inequality for the truncations `(u − k)⁺` of a subsolution, and the weak maximum principle for a
weak solution, both test the equation against a truncation of the solution itself.

## The two limits

Neither statement can be read off from the definition, because a weak derivative is only defined
by integration against test functions and `F ∘ u` has no reason to be smooth.  Both are obtained
by approximation, and the *order* of the two limits matters.

* First, `u` is approximated. On a subdomain `V` relatively compact in `Ω`, test functions on `Ω`
  are dense in `W^{1,p}(V)` (`TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ`), the
  chain rule is classical for them, and it passes to the limit because `V` has finite measure and
  weak derivatives are stable under `L¹` limits
  (`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`).  Here `F'` must be *continuous*: the
  convergence `F'(uₖ) → F'(u)` is what carries the derivative.  Locality of the weak derivative
  then returns the statement to `Ω`.
* Only then is the nonlinearity approximated.  The positive part is the limit of the `C¹`
  functions `Fδ t = ∫₀ᵗ χ(s / δ)`, where `χ` is `Real.smoothTransition`; the point of that choice
  is that `Fδ' = χ(· / δ)` vanishes identically on `(−∞, 0]`, so `Fδ'(t) → 1_{t > 0}` *including*
  at `t = 0`.  Taking the two limits in the other order would instead produce the factor
  `Fδ'(0)`, and the identification of the limit would need the separate fact that `∇u = 0` almost
  everywhere on `{u = 0}`.

## Main declarations

* `TauCeti.W1p.hasWeakFDerivOn_comp`: the chain rule, as a weak-derivative statement.
* `TauCeti.W1p.contDiffComp`: `F ∘ u` as an element of `W^{1,p}(Ω)`.
* `TauCeti.W1p.hasWeakFDerivOn_posPart`: the weak gradient of the positive part.
* `TauCeti.W1p.posPartAbove`: the shifted truncation `(u - k)⁺` for `k ≥ 0`.
* `TauCeti.W1p.posPart`: the positive part `u⁺` as an element of `W^{1,p}(Ω)`, with its value
  `TauCeti.W1p.value_posPart` and its weak gradient `TauCeti.W1p.gradient_posPart_ae`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.6.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §4.2.2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.5.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]
    [Fact (1 ≤ p)] in
private theorem enorm_innerSL_sub (x y : E) :
    ‖innerSL ℝ x - innerSL ℝ y‖ₑ = ‖x - y‖ₑ := by
  rw [← map_sub, ← ofReal_norm, ← ofReal_norm, innerSL_apply_norm]

/-! ### The classical chain rule for a test function -/

omit [MeasurableSpace E] [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
private theorem hasFDerivAt_comp_testFunction {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (phi : 𝓓(Omega, ℝ)) (x : E) :
    HasFDerivAt (fun y => F (phi y)) (innerSL ℝ (deriv F (phi x) • ∇ (phi : E → ℝ) x)) x := by
  have hd : HasFDerivAt (fun y => F (phi y))
      (deriv F (phi x) • fderiv ℝ (phi : E → ℝ) x) x :=
    HasDerivAt.comp_hasFDerivAt x ((hF.differentiable one_ne_zero).differentiableAt.hasDerivAt)
      ((phi.contDiff.differentiable (by simp)) x).hasFDerivAt
  refine hd.congr_fderiv ?_
  ext y
  simp [inner_gradient_left (𝕜 := ℝ) (f := (phi : E → ℝ)) (x := x) (y := y)]

private theorem hasWeakFDerivOn_comp_testFunction {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (fun x => F (phi x))
      fun x => innerSL ℝ (deriv F (phi x) • ∇ (phi : E → ℝ) x) := by
  have heq : fderiv ℝ (fun y => F (phi y)) =
      fun x => innerSL ℝ (deriv F (phi x) • ∇ (phi : E → ℝ) x) :=
    funext fun x => (hasFDerivAt_comp_testFunction hF phi x).fderiv
  have hcd : ContDiff ℝ 1 fun y => F (phi y) := hF.comp (phi.contDiff.of_le (by simp))
  rw [← heq]
  refine hasWeakFDerivOn_of_differentiableOn ?_ ?_ fun x _ =>
    (hasFDerivAt_comp_testFunction hF phi x).differentiableAt
  · exact (hcd.continuous.locallyIntegrable).locallyIntegrableOn _
  · exact ((hcd.continuous_fderiv one_ne_zero).locallyIntegrable).locallyIntegrableOn _

/-! ### The chain rule in `W^{1,p}(Ω)` for `p < ∞` -/

section ChainRule

variable {F : ℝ → ℝ} {M : ℝ≥0}

omit [FiniteDimensional ℝ E] in
private theorem memLp_comp_value (hlip : LipschitzWith M F) (hF0 : F 0 = 0)
    (u : W1p mu Omega p) :
    MemLp (fun x => F (W1p.value u x)) p (mu.restrict Omega) :=
  hlip.comp_memLp hF0 (Lp.memLp (W1p.value u))

omit [FiniteDimensional ℝ E] in
private theorem memLp_deriv_smul_gradient (hF : ContDiff ℝ 1 F) (hM : ∀ t, ‖deriv F t‖₊ ≤ M)
    (u : W1p mu Omega p) :
    MemLp (fun x => deriv F (W1p.value u x) • W1p.gradient u x) p (mu.restrict Omega) := by
  have hcont : Continuous (deriv F) := (contDiff_one_iff_deriv.mp hF).2
  refine MemLp.of_le ((Lp.memLp (W1p.gradient u)).const_smul (M : ℝ)) ?_ ?_
  · exact ((hcont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).smul
      (Lp.aestronglyMeasurable _))
  · filter_upwards with x
    have hb : ‖deriv F (W1p.value u x)‖ ≤ (M : ℝ) := by
      simpa [← NNReal.coe_le_coe] using hM (W1p.value u x)
    rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg M.coe_nonneg]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem locallyIntegrableOn_comp_value (hlip : LipschitzWith M F)
    (u : W1p mu Omega p) :
    LocallyIntegrableOn (fun x => F (W1p.value u x)) Omega mu := by
  have hzero : LipschitzWith M (fun t => F t - F 0) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_sub_right] using hlip.dist_le_mul x y
  have hloc : LocallyIntegrableOn (fun x => F (W1p.value u x) - F 0) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((memLp_comp_value hzero (by simp) u).locallyIntegrable Fact.out)
  have heq : (fun x => F (W1p.value u x)) =
      (fun x => F (W1p.value u x) - F 0) + fun _ => F 0 := by
    funext x
    simp
  rw [heq]
  exact hloc.add (locallyIntegrableOn_const (F 0))

private theorem locallyIntegrableOn_deriv_smul_gradient (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, ‖deriv F t‖₊ ≤ M) (u : W1p mu Omega p) (v : E) :
    LocallyIntegrableOn
      (fun x => innerSL ℝ (deriv F (W1p.value u x) • W1p.gradient u x) v) Omega mu := by
  refine locallyIntegrableOn_of_locallyIntegrable_restrict
    (((memLp_deriv_smul_gradient hF hM u).const_inner (𝕜 := ℝ) v).locallyIntegrable Fact.out
      |>.congr ?_)
  filter_upwards with x
  simp [real_inner_comm, real_inner_smul_right]


/-- The chain rule on a subdomain relatively compact in `Ω`, where test functions on `Ω` are
dense and the measure is finite. -/
private theorem hasWeakFDerivOn_comp_aux (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, ‖deriv F t‖₊ ≤ M) (u : W1p mu Omega p)
    {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    HasWeakFDerivOn mu V (fun x => F (W1p.value u x))
      fun x => innerSL ℝ (deriv F (W1p.value u x) • W1p.gradient u x) := by
  classical
  have hlip : LipschitzWith M F :=
    lipschitzWith_of_nnnorm_deriv_le (hF.differentiable one_ne_zero) hM
  have hcont : Continuous (deriv F) := (contDiff_one_iff_deriv.mp hF).2
  have hMr : ∀ t, ‖deriv F t‖ ≤ (M : ℝ) := fun t => by simpa [← NNReal.coe_le_coe] using hM t
  have hVΩ : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  have hVsub : (V : Set E) ⊆ (Omega : Set E) := SetLike.coe_subset_coe.mpr hVΩ
  have hres : mu.restrict (V : Set E) ≤ mu.restrict (Omega : Set E) :=
    Measure.restrict_mono_set mu hVsub
  have hfin : IsFiniteMeasure (mu.restrict (V : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top⟩
  -- the value and the gradient of the limit, as functions
  set fu : E → ℝ := ⇑(W1p.value u)
  set gu : E → E := ⇑(W1p.gradient u)
  have hfu_meas : AEStronglyMeasurable fu (mu.restrict (V : Set E)) :=
    (Lp.aestronglyMeasurable (W1p.value u)).mono_measure hres
  have hgu_meas : AEStronglyMeasurable gu (mu.restrict (V : Set E)) :=
    (Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure hres
  have hgu_int : ∫⁻ x in (V : Set E), ‖gu x‖ₑ ∂mu ≠ ∞ := by
    have h1 : MemLp gu 1 (mu.restrict (V : Set E)) :=
      ((Lp.memLp (W1p.gradient u)).mono_measure hres).mono_exponent Fact.out
    have h2 := h1.2
    rwa [eLpNorm_one_eq_lintegral_enorm, lt_top_iff_ne_top] at h2
  -- approximation by test functions on `Ω`
  obtain ⟨a, ha_mem, ha_tendsto⟩ := mem_closure_iff_seq_limit.mp
    (W1p.restrictL_mem_closure_range_ofTestFunctionₗ hp hVc hVO u)
  choose phi hphi using ha_mem
  have hval : Tendsto (fun n => W1p.value (a n)) atTop (𝓝 (W1p.value (W1p.restrictL hVΩ u))) := by
    simpa only [Function.comp_def, W1p.valueL_apply] using
      (W1p.valueL.continuous.tendsto (W1p.restrictL hVΩ u)).comp ha_tendsto
  have hgrad : Tendsto (fun n => W1p.gradient (a n))
      atTop (𝓝 (W1p.gradient (W1p.restrictL hVΩ u))) := by
    simpa only [Function.comp_def, W1p.gradientL_apply] using
      (W1p.gradientL.continuous.tendsto (W1p.restrictL hVΩ u)).comp ha_tendsto
  have hval1 : Tendsto (fun n => ∫⁻ x in (V : Set E), ‖W1p.value (a n) x - fu x‖ₑ ∂mu)
      atTop (𝓝 0) := by
    refine (tendsto_lintegral_enorm_sub_of_tendsto_Lp hval).congr fun n => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [W1p.value_restrictL_ae hVΩ u] with x hx
    rw [hx]
  have hgrad1 : Tendsto (fun n => ∫⁻ x in (V : Set E), ‖W1p.gradient (a n) x - gu x‖ₑ ∂mu)
      atTop (𝓝 0) := by
    refine (tendsto_lintegral_enorm_sub_of_tendsto_Lp hgrad).congr fun n => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hVΩ u] with x hx
    rw [hx]
  -- an almost-everywhere convergent subsequence of the values
  have hInMeas : TendstoInMeasure (mu.restrict (V : Set E))
      (fun n => ⇑(W1p.value (a n))) atTop fu := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      (fun n => Lp.aestronglyMeasurable _) hfu_meas ?_
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hval1
  obtain ⟨ns, hns, hns_ae⟩ := hInMeas.exists_seq_tendsto_ae
  have hsub : ∀ h : ℕ → ℝ≥0∞, Tendsto h atTop (𝓝 0) → Tendsto (fun i => h (ns i)) atTop (𝓝 0) :=
    fun h hh => hh.comp hns.tendsto_atTop
  -- the chain rule holds for each approximant, because it is smooth
  have hchain : ∀ i, HasWeakFDerivOn mu V (fun x => F (W1p.value (a (ns i)) x))
      fun x => innerSL ℝ (deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x) := by
    intro i
    have hv : ⇑(W1p.value (a (ns i))) =ᵐ[mu.restrict (V : Set E)] (phi (ns i) : E → ℝ) := by
      rw [← hphi (ns i)]
      refine (W1p.value_restrictL_ae hVΩ _).trans ?_
      rw [W1p.value_ofTestFunctionₗ]
      exact (testFunctionLp_apply_ae (mu := mu) p (phi (ns i))).filter_mono (ae_mono hres)
    have hg : ⇑(W1p.gradient (a (ns i))) =ᵐ[mu.restrict (V : Set E)]
        fun x => ∇ ((phi (ns i) : E → ℝ)) x := by
      rw [← hphi (ns i)]
      refine (W1p.gradient_restrictL_ae hVΩ _).trans ?_
      rw [W1p.gradient_ofTestFunctionₗ]
      exact (gradientTestFunctionLp_apply_ae (mu := mu) p (phi (ns i))).filter_mono (ae_mono hres)
    refine ((((hasWeakFDerivOn_comp_testFunction (mu := mu) hF (phi (ns i))).mono hVΩ).congr_ae
      ?_).congr_ae_deriv ?_)
    · filter_upwards [hv] with x hx; rw [hx]
    · filter_upwards [hv, hg] with x hx hgx; rw [hx, hgx]
  -- the values converge in `L¹(V)`, because `F` is Lipschitz
  have hconv1 : Tendsto (fun i => ∫⁻ x in (V : Set E),
      ‖F (W1p.value (a (ns i)) x) - F (fu x)‖ₑ ∂mu) atTop (𝓝 0) := by
    have hb : ∀ i, ∫⁻ x in (V : Set E), ‖F (W1p.value (a (ns i)) x) - F (fu x)‖ₑ ∂mu ≤
        (M : ℝ≥0∞) * ∫⁻ x in (V : Set E), ‖W1p.value (a (ns i)) x - fu x‖ₑ ∂mu := by
      intro i
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine lintegral_mono fun x => ?_
      rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
      exact hlip _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hb
    simpa using ENNReal.Tendsto.const_mul (hsub _ hval1) (Or.inr ENNReal.coe_ne_top)
  -- the gradients converge in `L¹(V)`: the coefficient is bounded and continuous
  have hconv2 : Tendsto (fun i => ∫⁻ x in (V : Set E),
      ‖innerSL ℝ (deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x) -
        innerSL ℝ (deriv F (fu x) • gu x)‖ₑ ∂mu) atTop (𝓝 0) := by
    have hnorm : ∀ i, ∀ x, ‖innerSL ℝ (deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x)
        - innerSL ℝ (deriv F (fu x) • gu x)‖ₑ =
        ‖deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x -
          deriv F (fu x) • gu x‖ₑ := by
      intro i x
      exact enorm_innerSL_sub _ _
    have hpt : ∀ i, ∀ x, ‖deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x -
        deriv F (fu x) • gu x‖ₑ ≤
        (M : ℝ≥0∞) * ‖W1p.gradient (a (ns i)) x - gu x‖ₑ +
          ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ * ‖gu x‖ₑ := by
      intro i x
      have hsplit : deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x -
          deriv F (fu x) • gu x =
          deriv F (W1p.value (a (ns i)) x) • (W1p.gradient (a (ns i)) x - gu x) +
            (deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)) • gu x := by
        rw [smul_sub, sub_smul]; abel
      rw [hsplit]
      refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
      · rw [enorm_smul]
        gcongr
        simpa [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hMr (W1p.value (a (ns i)) x))
      · rw [enorm_smul]
    have hmeas : ∀ i, AEMeasurable (fun x => (M : ℝ≥0∞) * ‖W1p.gradient (a (ns i)) x - gu x‖ₑ)
        (mu.restrict (V : Set E)) := fun i =>
      (((Lp.aestronglyMeasurable (W1p.gradient (a (ns i)))).sub hgu_meas).enorm).const_mul _
    have hB : Tendsto (fun i => (M : ℝ≥0∞) *
        ∫⁻ x in (V : Set E), ‖W1p.gradient (a (ns i)) x - gu x‖ₑ ∂mu) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hsub _ hgrad1) (Or.inr ENNReal.coe_ne_top)
    have hC : Tendsto (fun i => ∫⁻ x in (V : Set E),
        ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ * ‖gu x‖ₑ ∂mu) atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = ∫⁻ _x in (V : Set E), (0 : ℝ≥0∞) ∂mu := by simp
      rw [h0]
      refine tendsto_lintegral_of_dominated_convergence'
        (fun x => (2 * M : ℝ≥0∞) * ‖gu x‖ₑ)
        (fun i => ((((hcont.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable (W1p.value (a (ns i))))).sub
          (hcont.comp_aestronglyMeasurable hfu_meas)).enorm).mul hgu_meas.enorm))
        (fun i => ?_) ?_ ?_
      · filter_upwards with x
        gcongr
        have h2 : ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ ≤ 2 * (M : ℝ) :=
          le_trans (norm_sub_le _ _) (by linarith [hMr (W1p.value (a (ns i)) x), hMr (fu x)])
        calc ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ
            ≤ ENNReal.ofReal (2 * (M : ℝ)) := by
              simpa [← ofReal_norm] using ENNReal.ofReal_le_ofReal h2
          _ = (2 * M : ℝ≥0∞) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
              simp [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
      · have h2M : (2 * M : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
        rw [lintegral_const_mul' _ _ h2M]
        exact ENNReal.mul_ne_top h2M hgu_int
      · filter_upwards [hns_ae] with x hx
        have hd : Tendsto (fun i => deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)) atTop
            (𝓝 0) := by
          have h1 : Tendsto (fun i => deriv F (W1p.value (a (ns i)) x)) atTop
              (𝓝 (deriv F (fu x))) := (hcont.tendsto (fu x)).comp hx
          simpa using h1.sub (tendsto_const_nhds (x := deriv F (fu x)))
        have h2 : Tendsto (fun i => ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ) atTop
            (𝓝 0) := by
          simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp hd
        simpa using ENNReal.Tendsto.mul_const h2 (Or.inr enorm_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hB.add hC)
      (fun _ => zero_le) fun i => ?_
    calc ∫⁻ x in (V : Set E), ‖innerSL ℝ (deriv F (W1p.value (a (ns i)) x) •
            W1p.gradient (a (ns i)) x) - innerSL ℝ (deriv F (fu x) • gu x)‖ₑ ∂mu
        = ∫⁻ x in (V : Set E), ‖deriv F (W1p.value (a (ns i)) x) • W1p.gradient (a (ns i)) x -
            deriv F (fu x) • gu x‖ₑ ∂mu := by
          exact lintegral_congr fun x => hnorm i x
      _ ≤ ∫⁻ x in (V : Set E), ((M : ℝ≥0∞) * ‖W1p.gradient (a (ns i)) x - gu x‖ₑ +
            ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ * ‖gu x‖ₑ) ∂mu :=
          lintegral_mono fun x => hpt i x
      _ = (M : ℝ≥0∞) * (∫⁻ x in (V : Set E), ‖W1p.gradient (a (ns i)) x - gu x‖ₑ ∂mu) +
            ∫⁻ x in (V : Set E), ‖deriv F (W1p.value (a (ns i)) x) - deriv F (fu x)‖ₑ *
              ‖gu x‖ₑ ∂mu := by
          rw [lintegral_add_left' (hmeas i), lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  exact hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub
    ((locallyIntegrableOn_comp_value hlip u).mono_set hVsub)
    (fun v => (locallyIntegrableOn_deriv_smul_gradient hF hM u v).mono_set hVsub)
    hchain hconv1 hconv2

/-- **The local chain rule for `W^{1,p}(Ω)` when `1 ≤ p < ∞`.** If `F` is `C¹` with
derivative bounded by `M`, then `F ∘ u` has the weak gradient `F'(u) ∇u` on `Ω`. No boundary
regularity of `Ω` is needed: the statement is local, and the approximation happens on subdomains
relatively compact in `Ω`. -/
theorem W1p.hasWeakFDerivOn_comp (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, ‖deriv F t‖₊ ≤ M) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (fun x => F (W1p.value u x))
      fun x => innerSL ℝ (deriv F (W1p.value u x) • W1p.gradient u x) :=
  hasWeakFDerivOn_iff_forall_isCompact_closure.2 fun _ hVc hVO =>
    hasWeakFDerivOn_comp_aux hp hF hM u hVc hVO

/-- **For `1 ≤ p < ∞`, `W^{1,p}(Ω)` is stable under composition with a Lipschitz `C¹` function
vanishing at `0`.**  Its value and weak gradient are `F ∘ u` and `F'(u) ∇u`, by
`TauCeti.W1p.value_contDiffComp_ae` and `TauCeti.W1p.gradient_contDiffComp_ae`. -/
def W1p.contDiffComp (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F) (hM : ∀ t, ‖deriv F t‖₊ ≤ M)
    (hF0 : F 0 = 0) (u : W1p mu Omega p) : W1p mu Omega p :=
  W1p.mk
    ((memLp_comp_value (lipschitzWith_of_nnnorm_deriv_le (hF.differentiable one_ne_zero) hM)
      hF0 u).toLp _)
    ((memLp_deriv_smul_gradient hF hM u).toLp _)
    (((W1p.hasWeakFDerivOn_comp hp hF hM u).congr_ae
      (MemLp.coeFn_toLp _).symm).congr_ae_deriv (by
        filter_upwards [MemLp.coeFn_toLp (memLp_deriv_smul_gradient hF hM u)] with x hx
        rw [hx]))

/-- The value of `F ∘ u` produced by `W1p.contDiffComp` agrees almost everywhere with the
pointwise composition. -/
@[simp]
theorem W1p.value_contDiffComp_ae (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, ‖deriv F t‖₊ ≤ M) (hF0 : F 0 = 0) (u : W1p mu Omega p) :
    ⇑(W1p.value (W1p.contDiffComp hp hF hM hF0 u)) =ᵐ[mu.restrict Omega]
      fun x => F (W1p.value u x) := by
  rw [W1p.contDiffComp, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- The weak gradient of `F ∘ u` produced by `W1p.contDiffComp` is `F'(u) ∇u` almost
everywhere. -/
@[simp]
theorem W1p.gradient_contDiffComp_ae (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, ‖deriv F t‖₊ ≤ M) (hF0 : F 0 = 0) (u : W1p mu Omega p) :
    ⇑(W1p.gradient (W1p.contDiffComp hp hF hM hF0 u)) =ᵐ[mu.restrict Omega]
      fun x => deriv F (W1p.value u x) • W1p.gradient u x := by
  rw [W1p.contDiffComp, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

end ChainRule

/-! ### The positive part -/

/-- A `C¹` approximation of the positive part: the primitive of `t ↦ χ(t / δ)`, where `χ` is
`Real.smoothTransition`.  Both `posPartApprox δ` and its derivative vanish on `(−∞, 0]`, which is
what makes the derivative converge to `1_{t > 0}` at every point, `t = 0` included. -/
private noncomputable def posPartApprox (delta t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.smoothTransition (s / delta)

private theorem continuous_smoothTransition_div (delta : ℝ) :
    Continuous fun s : ℝ => Real.smoothTransition (s / delta) :=
  Real.smoothTransition.continuous.comp (continuous_id.div_const _)

private theorem hasDerivAt_posPartApprox (delta t : ℝ) :
    HasDerivAt (posPartApprox delta) (Real.smoothTransition (t / delta)) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_smoothTransition_div delta).intervalIntegrable _ _)
    ((continuous_smoothTransition_div delta).stronglyMeasurableAtFilter _ _)
    (continuous_smoothTransition_div delta).continuousAt

private theorem deriv_posPartApprox (delta : ℝ) :
    deriv (posPartApprox delta) = fun t => Real.smoothTransition (t / delta) :=
  funext fun t => (hasDerivAt_posPartApprox delta t).deriv

private theorem contDiff_posPartApprox (delta : ℝ) : ContDiff ℝ 1 (posPartApprox delta) := by
  rw [contDiff_one_iff_deriv, deriv_posPartApprox]
  exact ⟨fun t => (hasDerivAt_posPartApprox delta t).differentiableAt,
    continuous_smoothTransition_div delta⟩

private theorem nnnorm_deriv_posPartApprox_le (delta t : ℝ) :
    ‖deriv (posPartApprox delta) t‖₊ ≤ 1 := by
  rw [deriv_posPartApprox, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  simpa using Real.smoothTransition.le_one (t / delta)

private theorem posPartApprox_of_nonpos {delta : ℝ} (hd : 0 < delta) {t : ℝ} (ht : t ≤ 0) :
    posPartApprox delta t = 0 := by
  have hcongr : posPartApprox delta t = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_ge ht] at hs
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [div_nonpos_iff]
    exact Or.inr ⟨hs.2, hd.le⟩
  rw [hcongr, intervalIntegral.integral_zero]

private theorem posPartApprox_nonneg (delta : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ posPartApprox delta t :=
  intervalIntegral.integral_nonneg ht fun _s _ => Real.smoothTransition.nonneg _

private theorem posPartApprox_le (delta : ℝ) {t : ℝ} (ht : 0 ≤ t) : posPartApprox delta t ≤ t := by
  have h : posPartApprox delta t ≤ ∫ _s in (0 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_mono_on ht
      ((continuous_smoothTransition_div delta).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
      fun _s _ => Real.smoothTransition.le_one _
  simpa using h

private theorem abs_posPartApprox_sub_le {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    |posPartApprox delta t - max t 0| ≤ delta := by
  rcases le_or_gt t 0 with ht | ht
  · rw [posPartApprox_of_nonpos hd ht, max_eq_right ht]
    simpa using hd.le
  · rw [max_eq_left ht.le]
    have h1 : posPartApprox delta t ≤ t := posPartApprox_le delta ht.le
    have h2 : t - delta ≤ posPartApprox delta t := by
      rcases le_or_gt t delta with htd | htd
      · have := posPartApprox_nonneg delta ht.le
        linarith
      · have hsplit : (∫ s in (0 : ℝ)..delta, Real.smoothTransition (s / delta)) +
            (∫ s in (delta : ℝ)..t, Real.smoothTransition (s / delta)) = posPartApprox delta t :=
          intervalIntegral.integral_add_adjacent_intervals
            ((continuous_smoothTransition_div delta).intervalIntegrable _ _)
            ((continuous_smoothTransition_div delta).intervalIntegrable _ _)
        have hone : (∫ s in (delta : ℝ)..t, Real.smoothTransition (s / delta)) =
            ∫ _s in (delta : ℝ)..t, (1 : ℝ) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [Set.uIcc_of_le htd.le] at hs
          exact Real.smoothTransition.one_of_one_le ((one_le_div hd).2 hs.1)
        have h3 : (∫ s in (delta : ℝ)..t, Real.smoothTransition (s / delta)) = t - delta := by
          rw [hone]; simp
        have h4 : 0 ≤ ∫ s in (0 : ℝ)..delta, Real.smoothTransition (s / delta) :=
          intervalIntegral.integral_nonneg hd.le fun _s _ => Real.smoothTransition.nonneg _
        linarith
    rw [abs_le]
    constructor <;> linarith

private theorem tendsto_posPartApprox {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hd0 : Tendsto d atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => posPartApprox (d n) t) atTop (𝓝 (max t 0)) := by
  have h : Tendsto (fun n => posPartApprox (d n) t - max t 0) atTop (𝓝 0) :=
    squeeze_zero_norm
      (fun n => by simpa [Real.norm_eq_abs] using abs_posPartApprox_sub_le (hd n) t) hd0
  simpa using h.add_const (max t 0)

private theorem tendsto_deriv_posPartApprox {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hd0 : Tendsto d atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (posPartApprox (d n)) t) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  simp only [deriv_posPartApprox]
  rcases le_or_gt t 0 with ht | ht
  · have hzero : (if 0 < t then (1 : ℝ) else 0) = 0 := by simp [not_lt.mpr ht]
    rw [hzero]
    refine tendsto_const_nhds.congr fun n => ?_
    refine (Real.smoothTransition.zero_of_nonpos ?_).symm
    rw [div_nonpos_iff]
    exact Or.inr ⟨ht, (hd n).le⟩
  · have hone : (if 0 < t then (1 : ℝ) else 0) = 1 := by simp [ht]
    rw [hone]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hd0.eventually (gt_mem_nhds ht)] with n hn
    exact (Real.smoothTransition.one_of_one_le ((one_le_div (hd n)).2 hn.le)).symm

/-! ### The positive part of a Sobolev function -/

section PosPart

/-- The candidate weak gradient of `(u - k)⁺`. -/
private def posPartAboveGradient (k : ℝ) (u : W1p mu Omega p) : E → E :=
  {x | k < W1p.value u x}.indicator ⇑(W1p.gradient u)

omit [FiniteDimensional ℝ E] in
private theorem posPartAboveGradient_apply (k : ℝ) (u : W1p mu Omega p) (x : E) :
    posPartAboveGradient k u x =
      (if k < W1p.value u x then (1 : ℝ) else 0) • W1p.gradient u x := by
  by_cases h : k < W1p.value u x <;> simp [posPartAboveGradient, h]

omit [FiniteDimensional ℝ E] in
private theorem tendsto_deriv_posPartApprox_sub_smul_gradient (k : ℝ) (u : W1p mu Omega p)
    {d : ℕ → ℝ} (hd : ∀ n, 0 < d n) (hd0 : Tendsto d atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x)
      atTop (𝓝 (posPartAboveGradient k u x)) := by
  rw [posPartAboveGradient_apply]
  simpa only [sub_pos] using
    (tendsto_deriv_posPartApprox hd hd0 (W1p.value u x - k)).smul_const (W1p.gradient u x)

omit [FiniteDimensional ℝ E] in
private theorem aestronglyMeasurable_posPartAboveGradient (k : ℝ) (u : W1p mu Omega p) :
    AEStronglyMeasurable (posPartAboveGradient k u) (mu.restrict Omega) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun x => deriv (posPartApprox (1 / (n + 1 : ℝ)))
        (W1p.value u x - k) •
      W1p.gradient u x) (fun n => ?_) ?_
  · exact (((contDiff_one_iff_deriv.mp (contDiff_posPartApprox _)).2.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const)).smul
        (Lp.aestronglyMeasurable _))
  · filter_upwards with x
    exact tendsto_deriv_posPartApprox_sub_smul_gradient k u (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat x

omit [FiniteDimensional ℝ E] in
private theorem norm_posPartAboveGradient_le (k : ℝ) (u : W1p mu Omega p) (x : E) :
    ‖posPartAboveGradient k u x‖ ≤ ‖W1p.gradient u x‖ := by
  by_cases h : k < W1p.value u x <;> simp [posPartAboveGradient, h]

omit [FiniteDimensional ℝ E] in
private theorem memLp_posPartAboveGradient (k : ℝ) (u : W1p mu Omega p) :
    MemLp (posPartAboveGradient k u) p (mu.restrict Omega) :=
  MemLp.of_le (Lp.memLp (W1p.gradient u)) (aestronglyMeasurable_posPartAboveGradient k u)
    (Filter.Eventually.of_forall (norm_posPartAboveGradient_le k u))

omit [FiniteDimensional ℝ E] in
private theorem memLp_posPartAboveValue {k : ℝ} (hk : 0 ≤ k) (u : W1p mu Omega p) :
    MemLp (fun x => max (W1p.value u x - k) 0) p (mu.restrict Omega) := by
  have hlip : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [NNReal.coe_one, one_mul, dist_sub_right] using
      MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (x - k) (y - k)
  exact hlip.comp_memLp (by simp [hk]) (Lp.memLp (W1p.value u))

/-- **For `1 ≤ p < ∞`, truncation above any real level is weakly differentiable**, with
weak gradient `1_{u > k} ∇u`. -/
theorem W1p.hasWeakFDerivOn_posPartAbove (hp : p ≠ ∞) (k : ℝ) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (fun x => max (W1p.value u x - k) 0)
      fun x => innerSL ℝ ({x | k < W1p.value u x}.indicator (⇑(W1p.gradient u)) x) := by
  set d : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hdpos : ∀ n, 0 < d n := fun n => by positivity
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- local integrability of the two limits
  have hlip : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [NNReal.coe_one, one_mul, dist_sub_right] using
      MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (x - k) (y - k)
  have hvalLoc : LocallyIntegrableOn (fun x => max (W1p.value u x - k) 0) Omega mu :=
    locallyIntegrableOn_comp_value hlip u
  have hgradLoc : ∀ v : E, LocallyIntegrableOn
      (fun x => innerSL ℝ (posPartAboveGradient k u x) v) Omega mu := by
    intro v
    refine locallyIntegrableOn_of_locallyIntegrable_restrict
      (((memLp_posPartAboveGradient k u).const_inner (𝕜 := ℝ) v).locallyIntegrable Fact.out
        |>.congr ?_)
    filter_upwards with x
    simp [real_inner_comm]
  -- the chain rule applies to each smooth approximation of the positive part
  have hchain : ∀ n,
      HasWeakFDerivOn mu Omega (fun x => posPartApprox (d n) (W1p.value u x - k))
        fun x => innerSL ℝ
          (deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x) := by
    intro n
    let F : ℝ → ℝ := fun t => posPartApprox (d n) (t - k)
    have hF : ContDiff ℝ 1 F := by
      exact (contDiff_posPartApprox (d n)).comp (contDiff_id.sub contDiff_const)
    have hderiv (t : ℝ) : deriv F t = deriv (posPartApprox (d n)) (t - k) := by
      simpa [F, Function.comp_def, deriv_posPartApprox] using
        ((hasDerivAt_posPartApprox (d n) (t - k)).comp t
          (HasDerivAt.sub_const k (hasDerivAt_id t))).deriv
    have hM : ∀ t, ‖deriv F t‖₊ ≤ 1 := fun t => by
      rw [hderiv]
      exact nnnorm_deriv_posPartApprox_le (d n) (t - k)
    simpa only [F, hderiv] using W1p.hasWeakFDerivOn_comp hp hF hM u
  rw [hasWeakFDerivOn_iff_forall_isCompact_closure]
  intro V hVc hVO
  have hVΩ : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  have hVsub : (V : Set E) ⊆ (Omega : Set E) := SetLike.coe_subset_coe.mpr hVΩ
  have hres : mu.restrict (V : Set E) ≤ mu.restrict (Omega : Set E) :=
    Measure.restrict_mono_set mu hVsub
  have hfin : IsFiniteMeasure (mu.restrict (V : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top⟩
  have hgu_meas : AEStronglyMeasurable (⇑(W1p.gradient u)) (mu.restrict (V : Set E)) :=
    (Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure hres
  have hgu_int : ∫⁻ x in (V : Set E), ‖W1p.gradient u x‖ₑ ∂mu ≠ ∞ := by
    have h1 : MemLp (⇑(W1p.gradient u)) 1 (mu.restrict (V : Set E)) :=
      ((Lp.memLp (W1p.gradient u)).mono_measure hres).mono_exponent Fact.out
    have h2 := h1.2
    rwa [eLpNorm_one_eq_lintegral_enorm, lt_top_iff_ne_top] at h2
  -- the values converge uniformly, hence in `L¹(V)`
  have hconv1 : Tendsto (fun n => ∫⁻ x in (V : Set E),
      ‖posPartApprox (d n) (W1p.value u x - k) - max (W1p.value u x - k) 0‖ₑ ∂mu)
      atTop (𝓝 0) := by
    have hb : ∀ n, ∫⁻ x in (V : Set E),
        ‖posPartApprox (d n) (W1p.value u x - k) - max (W1p.value u x - k) 0‖ₑ ∂mu ≤
        ENNReal.ofReal (d n) * mu (V : Set E) := by
      intro n
      calc ∫⁻ x in (V : Set E),
            ‖posPartApprox (d n) (W1p.value u x - k) - max (W1p.value u x - k) 0‖ₑ ∂mu
          ≤ ∫⁻ _x in (V : Set E), ENNReal.ofReal (d n) ∂mu := by
            refine lintegral_mono fun x => ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal
              (by simpa [Real.norm_eq_abs] using abs_posPartApprox_sub_le (hdpos n) _)
        _ = ENNReal.ofReal (d n) * mu (V : Set E) := by
            rw [setLIntegral_const]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hb
    have hV : mu (V : Set E) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top).ne
    have : Tendsto (fun n => ENNReal.ofReal (d n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hd0
    simpa using ENNReal.Tendsto.mul_const this (Or.inr hV)
  -- the gradients converge by dominated convergence
  have hconv2 : Tendsto (fun n => ∫⁻ x in (V : Set E),
      ‖innerSL ℝ (deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x) -
        innerSL ℝ (posPartAboveGradient k u x)‖ₑ ∂mu) atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _x in (V : Set E), (0 : ℝ≥0∞) ∂mu := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖W1p.gradient u x‖ₑ)
      (fun n => ?_) (fun n => ?_) hgu_int ?_
    · refine AEStronglyMeasurable.enorm ?_
      refine AEStronglyMeasurable.sub ?_ ?_
      · exact (innerSL ℝ (E := E)).continuous.comp_aestronglyMeasurable
          (((contDiff_one_iff_deriv.mp (contDiff_posPartApprox (d n))).2.comp_aestronglyMeasurable
            (((Lp.aestronglyMeasurable (W1p.value u)).mono_measure hres).sub
              aestronglyMeasurable_const)).smul hgu_meas)
      · exact (innerSL ℝ (E := E)).continuous.comp_aestronglyMeasurable
          ((aestronglyMeasurable_posPartAboveGradient k u).mono_measure hres)
    · filter_upwards with x
      have hnorm : ‖innerSL ℝ
          (deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x) -
          innerSL ℝ (posPartAboveGradient k u x)‖ₑ =
          ‖deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x -
            posPartAboveGradient k u x‖ₑ := by
        exact enorm_innerSL_sub _ _
      rw [hnorm, posPartAboveGradient_apply, ← sub_smul, enorm_smul]
      refine mul_le_of_le_one_left' ?_
      simp only [deriv_posPartApprox]
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Real.smoothTransition.nonneg ((W1p.value u x - k) / d n)
      have h2 := Real.smoothTransition.le_one ((W1p.value u x - k) / d n)
      have hite : (if k < W1p.value u x then (1 : ℝ) else 0) = 1 ∨
          (if k < W1p.value u x then (1 : ℝ) else 0) = 0 := by
        by_cases h : k < W1p.value u x <;> simp [h]
      rw [Real.norm_eq_abs, abs_le]
      rcases hite with h | h <;> rw [h] <;> constructor <;> linarith
    · filter_upwards with x
      have hd := tendsto_deriv_posPartApprox_sub_smul_gradient k u hdpos hd0 x
      have : Tendsto
          (fun n => deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x -
            posPartAboveGradient k u x) atTop (𝓝 0) := by
        simpa using hd.sub (tendsto_const_nhds (x := posPartAboveGradient k u x))
      have henorm : Tendsto (fun n =>
          ‖deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x -
            posPartAboveGradient k u x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : E)).comp this
      refine henorm.congr fun n => ?_
      exact (enorm_innerSL_sub
        (deriv (posPartApprox (d n)) (W1p.value u x - k) • W1p.gradient u x)
        (posPartAboveGradient k u x)).symm
  exact hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (hvalLoc.mono_set hVsub)
    (fun v => (hgradLoc v).mono_set hVsub) (fun n => (hchain n).mono hVΩ) hconv1 hconv2

/-- **For `1 ≤ p < ∞`, the positive part of a Sobolev function is weakly differentiable**, with
weak gradient `1_{u > 0} ∇u`. -/
theorem W1p.hasWeakFDerivOn_posPart (hp : p ≠ ∞) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (fun x => max (W1p.value u x) 0)
      fun x => innerSL ℝ ({x | 0 < W1p.value u x}.indicator (⇑(W1p.gradient u)) x) := by
  simpa using W1p.hasWeakFDerivOn_posPartAbove hp 0 u

/-- **For `1 ≤ p < ∞`, truncation above a nonnegative level preserves `W^{1,p}(Ω)`.**
The value of `W1p.posPartAbove hp hk u` is `(u - k)⁺`, and its weak gradient is
`1_{u > k} ∇u`. -/
def W1p.posPartAbove (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k) (u : W1p mu Omega p) :
    W1p mu Omega p :=
  W1p.mk ((memLp_posPartAboveValue hk u).toLp _)
    ((memLp_posPartAboveGradient k u).toLp _)
    (((W1p.hasWeakFDerivOn_posPartAbove hp k u).congr_ae
      (MemLp.coeFn_toLp (memLp_posPartAboveValue hk u)).symm).congr_ae_deriv (by
        filter_upwards [MemLp.coeFn_toLp (memLp_posPartAboveGradient k u)] with x hx
        rw [hx]
        rfl))

/-- The value of `W1p.posPartAbove hp hk u` is `(u - k)⁺` almost everywhere. -/
@[simp]
theorem W1p.value_posPartAbove_ae (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega p) :
    ⇑(W1p.value (W1p.posPartAbove hp hk u)) =ᵐ[mu.restrict Omega]
      fun x => max (W1p.value u x - k) 0 := by
  rw [W1p.posPartAbove, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- The weak gradient of `(u - k)⁺` is `1_{u > k} ∇u` almost everywhere. -/
@[simp]
theorem W1p.gradient_posPartAbove_ae (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega p) :
    ⇑(W1p.gradient (W1p.posPartAbove hp hk u)) =ᵐ[mu.restrict Omega]
      {x | k < W1p.value u x}.indicator ⇑(W1p.gradient u) := by
  rw [W1p.posPartAbove, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

/-- **For `1 ≤ p < ∞`, the positive part `u⁺` of a Sobolev function is again in
`W^{1,p}(Ω)`.**  Its value is Mathlib's `MeasureTheory.Lp.posPart` of the value of `u`, and its
weak gradient is `1_{u > 0} ∇u` (`TauCeti.W1p.gradient_posPart_ae`). -/
def W1p.posPart (hp : p ≠ ∞) (u : W1p mu Omega p) : W1p mu Omega p :=
  W1p.mk (Lp.posPart (W1p.value u)) ((memLp_posPartAboveGradient 0 u).toLp _)
    (((W1p.hasWeakFDerivOn_posPart hp u).congr_ae (Lp.coeFn_posPart _).symm).congr_ae_deriv (by
      filter_upwards [MemLp.coeFn_toLp (memLp_posPartAboveGradient 0 u)] with x hx
      rw [hx]
      rfl))

/-- The value of `W1p.posPart hp u` is the `Lᵖ` positive part of the value of `u`. -/
@[simp]
theorem W1p.value_posPart (hp : p ≠ ∞) (u : W1p mu Omega p) :
    W1p.value (W1p.posPart hp u) = Lp.posPart (W1p.value u) :=
  W1p.value_mk _ _ _

/-- The weak gradient of `u⁺` is `1_{u > 0} ∇u` almost everywhere. -/
@[simp]
theorem W1p.gradient_posPart_ae (hp : p ≠ ∞) (u : W1p mu Omega p) :
    ⇑(W1p.gradient (W1p.posPart hp u)) =ᵐ[mu.restrict Omega]
      {x | 0 < W1p.value u x}.indicator ⇑(W1p.gradient u) := by
  rw [W1p.posPart, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

end PosPart

end TauCeti
