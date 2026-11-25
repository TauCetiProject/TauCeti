/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Convex.Exhaustion
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.MeasureTheory.Function.LocallyAEConst
import TauCeti.MeasureTheory.Function.Lp.Const
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure.  This
file proves, for `1 ≤ p ≤ ∞` and every `u ∈ W^{1,p}(Ω)`,

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * ‖∇u‖_{Lᵖ(Ω)}`,

the inequality that `TauCeti.eLpNorm_sub_setAverage_le_of_convex` proves, with the same constant,
for `C¹` functions.  A weakly differentiable function need not be `C¹`, so the two are genuinely
different statements, and it is the Sobolev one that an existence or regularity argument can use.

Subtracting the mean is not a normalisation that could be dropped: no inequality of this shape
holds for the deviation from an arbitrary constant, since the nonzero constants themselves lie in
`W^{1,p}(Ω)` with vanishing gradient.

## The approximation

Test functions on `Ω` are dense in `W^{1,p}(Ω)` only after `Ω` is shrunk:
`TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ` approximates `u`
on a subdomain `U` whose closure is a compact subset of `Ω`.  Two limits are therefore taken.

* On a fixed such `U`, convex so that the `C¹` inequality applies to it, the Sobolev functions
  satisfying the inequality form a closed set — the mean over `S` is a continuous functional, by
  `Set.setIntegralLp` — which contains every test function, hence their closure.
* The convex subdomains are then increased to `Ω`, along the exhaustion
  `TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`.  The means over `S ∩ U`
  converge to the mean over `S`, and Fatou's lemma for the `Lᵖ` seminorm,
  `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`, passes the inequality to the limit.  Only the
  measure of `S ∩ U` needs to be tracked, since `diam U ≤ diam Ω` already bounds the numerator of
  the constant.

These limits are taken for finite `p`.  The constant does not depend on `p`, so the case `p = ∞`
follows by applying the finite case to `u` at the exponents `q < ∞`, on the domain `Ω` of finite
measure, and letting `q → ∞` (`TauCeti.tendsto_eLpNorm_atTop`).

## Main declarations

* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`: the inequality on `W^{1,p}(Ω)`.
* `TauCeti.W1p.setAverage_norm_sub_setAverage_le_of_convex`: the mean oscillation of `u` over
  `Ω`, by Hölder's inequality.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball`: the constant on a ball of radius `R`
  is `2 ^ (n + 1) * R`.
* `TauCeti.W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset`: the same bound in `L²`,
  for a ball contained in `Ω`, with both sides written as integrals over the ball.
* `TauCeti.W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset`: the same bound in `L¹`,
  for a ball contained in `Ω` and any `u ∈ W^{1,p}(Ω)`.
* `TauCeti.W1p.exists_value_ae_eq_const_of_gradient_eq_zero`: on a preconnected `Ω`, a Sobolev
  function with vanishing weak gradient is almost everywhere constant.
* `TauCeti.W1p.exists_eq_const_of_gradient_eq_zero`: if moreover `Ω` has finite measure, such a
  Sobolev function is the constant `TauCeti.W1p.const c`.
* `TauCeti.W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero`: on a preconnected `Ω`, a
  Sobolev function with vanishing gradient and vanishing integral over a set of positive measure
  is zero.
* `TauCeti.W1p.integralL`: the integral `∫_Ω u` as a continuous linear functional on
  `W^{1,p}(Ω)`, for `Ω` of finite measure.
* `TauCeti.W1p.eq_zero_of_gradient_eq_zero_of_integralL_eq_zero`: on a preconnected `Ω` of finite
  measure, a Sobolev function with vanishing gradient and vanishing integral over `Ω` is zero.
* `TauCeti.W1p.eq_zero_of_gradient_eq_zero`: for `p < ∞`, a Sobolev function on the whole of a
  nontrivial space with vanishing weak gradient is zero.
* `TauCeti.W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq`: on a preconnected `Ω`, a Sobolev
  function whose weak gradient agrees almost everywhere with `∇ q` for a `C¹` function `q` equals
  `q + c` almost everywhere.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16.
* L. C. Evans, *Partial Differential Equations*, Section 5.8.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

/-! ### The inequality on a relatively compact convex subdomain -/

/-- The `C¹` Poincaré–Wirtinger inequality, transported to the restriction to `U` of a test
function. -/
private theorem norm_value_sub_setAverage_restrictL_ofTestFunctionₗ_le (hp : p ≠ ∞)
    (hU : U ≤ Omega) (hUc : Convex ℝ (U : Set E)) (hUb : Bornology.IsBounded (U : Set E))
    (hSU : S ⊆ (U : Set E)) (hS0 : mu S ≠ 0) (phi : 𝓓(Omega, ℝ))
    [IsFiniteMeasure (mu.restrict (U : Set E))] :
    ‖W1p.value (W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)) -
        Lp.const p (mu.restrict (U : Set E))
          (⨍ y in S, W1p.value (W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)) y ∂mu)‖ ≤
      (mu.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient (W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi))‖ := by
  set C : ℝ := mu.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / mu.real S
  have hC0 : 0 ≤ C :=
    div_nonneg (mul_nonneg measureReal_nonneg (pow_nonneg Metric.diam_nonneg _))
      measureReal_nonneg
  set w := W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)
  have haeU : W1p.value w =ᵐ[mu.restrict (U : Set E)] fun x ↦ phi x := by
    refine (W1p.value_restrictL_ae hU _).trans ?_
    rw [W1p.value_ofTestFunctionₗ]
    exact (testFunctionLp_apply_ae (mu := mu) p phi).filter_mono
      (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
  have hgradU : W1p.gradient w =ᵐ[mu.restrict (U : Set E)] fun x ↦ ∇ (phi : E → ℝ) x := by
    refine (W1p.gradient_restrictL_ae hU _).trans ?_
    rw [W1p.gradient_ofTestFunctionₗ]
    exact (gradientTestFunctionLp_apply_ae (mu := mu) p phi).filter_mono
      (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
  have havg : (⨍ y in S, W1p.value w y ∂mu) = ⨍ y in S, phi y ∂mu :=
    average_congr (haeU.filter_mono (ae_mono (Measure.restrict_mono hSU le_rfl)))
  have hmain := eLpNorm_sub_setAverage_le_of_convex (μ := mu) (u := fun x ↦ (phi : E → ℝ) x)
    hUc hUb (phi.contDiff.of_le (by simp)).contDiffOn hSU hS0
    (Fact.out : (1 : ℝ≥0∞) ≤ p) hp
  have hkey : ‖W1p.value w - Lp.const p (mu.restrict (U : Set E))
      (⨍ y in S, W1p.value w y ∂mu)‖ₑ ≤ ENNReal.ofReal C * ‖W1p.gradient w‖ₑ := by
    rw [← eLpNorm_sub_const_eq_enorm, Lp.eNorm_def]
    calc eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) p (mu.restrict U)
        = eLpNorm (fun x ↦ (phi : E → ℝ) x - ⨍ y in S, (phi : E → ℝ) y ∂mu) p
            (mu.restrict U) := by
          rw [havg]
          exact eLpNorm_congr_ae (haeU.mono fun x hx ↦ by simp only [hx])
      _ ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ (phi : E → ℝ)) p (mu.restrict U) := hmain
      _ = ENNReal.ofReal C * eLpNorm (W1p.gradient w) p (mu.restrict U) := by
          congr 1
          refine eLpNorm_congr_norm_ae
            (phi.contDiff.continuous_fderiv (by simp)).aestronglyMeasurable
            (Lp.aestronglyMeasurable _) ?_
          filter_upwards [hgradU] with x hx
          rw [hx, norm_gradient_eq_norm_fderiv]
  rw [← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC0] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hkey

/-- **The Poincaré–Wirtinger inequality for a limit of test functions.**  It holds for every
Sobolev function on `U` that is a `W^{1,p}`-limit of restrictions of test functions on a larger
domain. -/
private theorem eLpNorm_value_sub_setAverage_le_of_mem_closure (hp : p ≠ ∞) (hU : U ≤ Omega)
    (hUc : Convex ℝ (U : Set E)) (hUb : Bornology.IsBounded (U : Set E))
    (hSU : S ⊆ (U : Set E)) (hS0 : mu S ≠ 0) {v : W1p mu U p}
    (hv : v ∈ closure (Set.range fun (phi : 𝓓(Omega, ℝ)) ↦
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi))) :
    eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S, W1p.value v y ∂mu) p (mu.restrict U) ≤
      ENNReal.ofReal (mu.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient v‖ₑ := by
  have hUfin : mu (U : Set E) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hUb.isCompact_closure.measure_lt_top).ne
  have hfin : IsFiniteMeasure (mu.restrict (U : Set E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUfin.lt_top⟩
  set C : ℝ := mu.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / mu.real S
  have hC0 : 0 ≤ C :=
    div_nonneg (mul_nonneg measureReal_nonneg (pow_nonneg Metric.diam_nonneg _))
      measureReal_nonneg
  -- The inequality, written with real norms, cuts out a closed subset of `W^{1,p}(U)`.
  have hclosed : IsClosed {w : W1p mu U p |
      ‖W1p.value w - Lp.const p (mu.restrict (U : Set E))
        (⨍ y in S, W1p.value w y ∂mu)‖ ≤ C * ‖W1p.gradient w‖} := by
    have h1 : Continuous fun w : W1p mu U p ↦
        ‖W1p.value w - Lp.const p (mu.restrict (U : Set E)) (⨍ y in S, W1p.value w y ∂mu)‖ := by
      refine Continuous.norm (Continuous.sub ?_ ?_)
      · have hcont : Continuous fun w : W1p mu U p ↦ W1p.valueL w :=
          (W1p.valueL (mu := mu) (Omega := U) (p := p)).continuous
        simpa only [W1p.valueL_apply] using hcont
      · exact (Lp.constL p (mu.restrict (U : Set E)) ℝ).continuous.comp
          (W1p.continuous_setAverage_value hSU)
    have h2 : Continuous fun w : W1p mu U p ↦ C * ‖W1p.gradient w‖ := by
      refine continuous_const.mul (Continuous.norm ?_)
      have hcont : Continuous fun w : W1p mu U p ↦ W1p.gradientL w :=
        (W1p.gradientL (mu := mu) (Omega := U) (p := p)).continuous
      simpa only [W1p.gradientL_apply] using hcont
    exact isClosed_le h1 h2
  -- Every test function satisfies it, by the `C¹` inequality on the convex set `U`.
  have hrange : (Set.range fun (phi : 𝓓(Omega, ℝ)) ↦
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)) ⊆ {w : W1p mu U p |
      ‖W1p.value w - Lp.const p (mu.restrict (U : Set E))
        (⨍ y in S, W1p.value w y ∂mu)‖ ≤ C * ‖W1p.gradient w‖} := by
    rintro _ ⟨phi, rfl⟩
    exact norm_value_sub_setAverage_restrictL_ofTestFunctionₗ_le hp hU hUc hUb hSU hS0 phi
  have hv' := closure_minimal hrange hclosed hv
  rw [eLpNorm_sub_const_eq_enorm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal hv'


/-- The Poincaré–Wirtinger inequality on a convex open `V` with compact closure inside `Ω`,
for a Sobolev function on `Ω`, with the constant of the whole domain `Ω` in the numerator. -/
private theorem eLpNorm_value_sub_setAverage_le_of_isCompact_closure (hp : p ≠ ∞)
    (hb : Bornology.IsBounded (Omega : Set E)) {V : Opens E} (hVconv : Convex ℝ (V : Set E))
    (hVcompact : IsCompact (closure (V : Set E))) (hVclosure : closure (V : Set E) ⊆ Omega)
    {S' : Set E} (hSV : S' ⊆ V) (hn : mu S' ≠ 0) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S', W1p.value u y ∂mu) p (mu.restrict V) ≤
      ENNReal.ofReal (mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) /
        mu.real S') * ‖W1p.gradient u‖ₑ := by
  have hVsub : (V : Set E) ⊆ Omega := subset_closure.trans hVclosure
  have hWle : V ≤ Omega := SetLike.coe_subset_coe.mp hVsub
  set v : W1p mu V p := W1p.restrictL hWle u
  have hval : W1p.value v =ᵐ[mu.restrict V] W1p.value u := W1p.value_restrictL_ae _ u
  have hgrad : W1p.gradient v =ᵐ[mu.restrict V] W1p.gradient u :=
    W1p.gradient_restrictL_ae _ u
  have havg : (⨍ y in S', W1p.value v y ∂mu) = ⨍ y in S', W1p.value u y ∂mu :=
    average_congr (hval.filter_mono
      (ae_mono (Measure.restrict_mono hSV le_rfl)))
  have hbase := eLpNorm_value_sub_setAverage_le_of_mem_closure (S := S') (v := v) hp
    hWle hVconv (hb.subset hVsub) hSV hn
    (W1p.restrictL_mem_closure_range_ofTestFunctionₗ (U := V) hp hVcompact hVclosure u)
  rw [havg] at hbase
  have hpos : 0 < mu.real S' :=
    ENNReal.toReal_pos hn ((measure_mono (hSV.trans subset_closure)).trans_lt
      hVcompact.measure_lt_top).ne
  have hcongr : eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S', W1p.value u y ∂mu) p
        (mu.restrict V) =
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S', W1p.value u y ∂mu) p
        (mu.restrict V) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hval] with x hx
    exact congrArg (· - ⨍ y in S', W1p.value u y ∂mu) hx
  have hconst : mu.real (ball (0 : E) 1) * diam (V : Set E) ^ (finrank ℝ E + 1) /
      mu.real S' ≤
      mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S' := by
    gcongr
    exact Metric.diam_mono hVsub hb
  have hgradle : ‖W1p.gradient v‖ₑ ≤ ‖W1p.gradient u‖ₑ :=
    calc ‖W1p.gradient v‖ₑ
        = eLpNorm (W1p.gradient u) p (mu.restrict V) := by
          rw [Lp.eNorm_def]
          exact eLpNorm_congr_ae hgrad
      _ ≤ eLpNorm (W1p.gradient u) p (mu.restrict (Omega : Set E)) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hVsub le_rfl)
      _ = ‖W1p.gradient u‖ₑ := (Lp.eNorm_def _).symm
  exact hcongr ▸ hbase.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) hgradle)

/-! ### The inequality on the whole domain -/

/-- The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)` for a null-measurable set `S`; see
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` for the statement without measurability. -/
private theorem W1p.eLpNorm_value_sub_setAverage_le_of_convex_of_nullMeasurableSet (hp : p ≠ ∞)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hSm : NullMeasurableSet S mu) (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0)
    (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict Omega) ≤
      ENNReal.ofReal (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient u‖ₑ := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, -, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Omega.isOpen hconv
  have hSfin : mu S ≠ ∞ := (hb.subset hS).measure_lt_top.ne
  have hSRpos : 0 < mu.real S := ENNReal.toReal_pos hS0 hSfin
  have hSR0 : mu.real S ≠ 0 := hSRpos.ne'
  -- The means over `S ∩ V n` converge to the mean over `S`.
  have hSV : S ⊆ ⋃ n, V n := hVunion ▸ hS
  have hmeasR : Tendsto (fun n ↦ mu.real (S ∩ V n)) atTop (𝓝 (mu.real S)) :=
    tendsto_measureReal_inter_of_monotone hVmono hSV hSfin
  have hint : IntegrableOn (W1p.value u) S mu := by
    have : IsFiniteMeasure (mu.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
    exact ((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hS le_rfl)).integrable Fact.out
  have ha : Tendsto (fun n ↦ ⨍ y in S ∩ V n, W1p.value u y ∂mu) atTop
      (𝓝 (⨍ y in S, W1p.value u y ∂mu)) :=
    tendsto_setAverage_inter_of_monotone hVmono hSV
      (fun n ↦ hSm.inter (hVopen n).measurableSet.nullMeasurableSet) hSfin hint
  -- The inequality on each piece, with the constant of the whole domain in the numerator.
  set K : ℝ := mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1)
  have hpiece : ∀ n, mu (S ∩ V n) ≠ 0 →
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) p
          (mu.restrict (V n)) ≤
        ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ := fun n hn ↦
    eLpNorm_value_sub_setAverage_le_of_isCompact_closure (V := ⟨V n, hVopen n⟩) hp hb
      (hVconv n) (hVcompact n) (hVclosure n) inter_subset_right hn u
  -- Fatou along the exhaustion.
  set a : ℕ → ℝ := fun n ↦ ⨍ y in S ∩ V n, W1p.value u y ∂mu
  set b : ℝ := ⨍ y in S, W1p.value u y ∂mu
  have hlim := eLpNorm_sub_const_restrict_le_liminf (μ := mu) (p := p)
    (W1p.value u : E →ₘ[mu.restrict (Omega : Set E)] ℝ).stronglyMeasurable.aestronglyMeasurable
    (fun n ↦ (hVopen n).measurableSet) hVmono hVunion ha
  have hbound : ∀ᶠ n in atTop, eLpNorm (fun x ↦ W1p.value u x - a n) p (mu.restrict (V n)) ≤
      ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ := by
    filter_upwards [hmeasR.eventually (lt_mem_nhds hSRpos)] with n hn
    refine hpiece n fun h0 ↦ ?_
    rw [measureReal_def, h0] at hn
    simp at hn
  have htend : Tendsto (fun n ↦ ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ)
      atTop (𝓝 (ENNReal.ofReal (K / mu.real S) * ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeasR hSR0))
      (Or.inr (by simp))
  calc eLpNorm (fun x ↦ W1p.value u x - b) p (mu.restrict Omega)
      ≤ atTop.liminf fun n ↦ eLpNorm (fun x ↦ W1p.value u x - a n) p (mu.restrict (V n)) := hlim
    _ ≤ atTop.liminf fun n ↦ ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ :=
        Filter.liminf_le_liminf hbound
    _ = ENNReal.ofReal (K / mu.real S) * ‖W1p.gradient u‖ₑ := htend.liminf_eq

/-- **The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`.**  Let `Ω` be a bounded convex open set
in a finite-dimensional real inner product space of dimension `n`, and let `S ⊆ Ω` have positive
measure.  For `1 ≤ p ≤ ∞`, every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at most
`μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times the `Lᵖ` norm of its weak gradient.  The constant
does not depend on `p`, so the case `p = ∞` is the limit of the finite exponents. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_convex
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict Omega) ≤
      ENNReal.ofReal (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient u‖ₑ := by
  set C := ENNReal.ofReal
    (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S)
  -- Replace `S` by a measurable subset `S'` of `Ω` with the same restricted measure.
  set S' : Set E := (Omega : Set E) ∩ toMeasurable mu S
  have hres : mu.restrict S' = mu.restrict S :=
    Measure.restrict_inter_toMeasurable (hb.subset hS).measure_lt_top.ne
      Omega.isOpen.measurableSet hS
  have hS'm : MeasurableSet S' :=
    Omega.isOpen.measurableSet.inter (measurableSet_toMeasurable mu S)
  have hmu : mu S' = mu S := by
    rw [← Measure.restrict_apply_univ, hres, Measure.restrict_apply_univ]
  have hmuR : mu.real S' = mu.real S := by rw [measureReal_def, measureReal_def, hmu]
  -- The inequality at every finite exponent.
  have hfin (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ∞) (v : W1p mu Omega q) :
      eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S, W1p.value v y ∂mu) q (mu.restrict Omega) ≤
        C * ‖W1p.gradient v‖ₑ := by
    have h := W1p.eLpNorm_value_sub_setAverage_le_of_convex_of_nullMeasurableSet (S := S') hq
      hconv hb hS'm.nullMeasurableSet inter_subset_left (hmu ▸ hS0) v
    rwa [hres, hmuR] at h
  rcases ne_or_eq p ∞ with hp | rfl
  · exact hfin p hp u
  -- At `p = ∞`, lower `u` to the finite exponents `q ≥ 1` and let `q → ∞`.
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hle : ∀ᶠ q : ℝ≥0 in atTop,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega) ≤
        C * eLpNorm (W1p.gradient u) q (mu.restrict Omega) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
    have hval : W1p.value (W1p.ofExponentLE le_top u) =ᵐ[mu.restrict Omega] W1p.value u :=
      (W1p.coeFn_value_ofExponentLE (le_top : (q : ℝ≥0∞) ≤ ∞) u).eventuallyEq
    have havg : ⨍ y in S, W1p.value (W1p.ofExponentLE le_top u) y ∂mu =
        ⨍ y in S, W1p.value u y ∂mu := average_congr (ae_restrict_of_ae_restrict_of_subset hS hval)
    have h := hfin q ENNReal.coe_ne_top (W1p.ofExponentLE le_top u)
    rw [havg, Lp.eNorm_def,
      eLpNorm_congr_ae (W1p.coeFn_gradient_ofExponentLE _ u).eventuallyEq] at h
    exact (eLpNorm_congr_ae (hval.mono fun x hx ↦ by simp only [hx])).symm.trans_le h
  rw [Lp.eNorm_def]
  exact le_of_tendsto_of_tendsto tendsto_eLpNorm_atTop
    (ENNReal.Tendsto.const_mul tendsto_eLpNorm_atTop (Or.inr ENNReal.ofReal_ne_top)) hle

/-- **The mean oscillation of a `W^{1,p}` function on a bounded convex domain.**  Let `Ω` be a
bounded convex open set of positive measure in a finite-dimensional real inner product space of
dimension `n`.  For `1 ≤ p ≤ ∞`, the mean over `Ω` of `|u - ⨍_Ω u|` is at most
`μ(B(0, 1)) * (diam Ω) ^ (n + 1) * μ(Ω) ^ (-(1 + 1 / p))` times the `Lᵖ` norm of the weak gradient
of `u ∈ W^{1,p}(Ω)`.  This is `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` with
`S = Ω`, combined with Hölder's inequality. -/
theorem W1p.setAverage_norm_sub_setAverage_le_of_convex
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hOmega : mu Omega ≠ 0) (u : W1p mu Omega p) :
    ⨍ y in Omega, ‖W1p.value u y - ⨍ z in Omega, W1p.value u z ∂mu‖ ∂mu ≤
      mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) *
        mu.real Omega ^ (-(1 + 1 / p.toReal)) * ‖W1p.gradient u‖ := by
  set g : E → ℝ := fun y ↦ W1p.value u y - ⨍ z in Omega, W1p.value u z ∂mu
  set m := mu.real Omega
  set K := mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1)
  have hfin : mu Omega ≠ ∞ := hb.measure_lt_top.ne
  have hm : 0 < m := ENNReal.toReal_pos hOmega hfin
  have hK : 0 ≤ K := by positivity
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hfin
  -- The Poincaré–Wirtinger inequality in `Lᵖ(Ω)`.
  have hP : eLpNorm g p (mu.restrict Omega) ≤ ENNReal.ofReal (K / m) * ‖W1p.gradient u‖ₑ :=
    W1p.eLpNorm_value_sub_setAverage_le_of_convex hconv hb subset_rfl hOmega u
  have hPr : (eLpNorm g p (mu.restrict Omega)).toReal ≤ K / m * ‖W1p.gradient u‖ := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top) hP
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hK hm.le), toReal_eNorm] at this
  -- Hölder's inequality: `‖g‖_{L¹(Ω)} ≤ μ(Ω)^(1 - 1/p) ‖g‖_{Lᵖ(Ω)}`.
  have hg : MemLp g p (mu.restrict Omega) := (Lp.memLp (W1p.value u)).sub (memLp_const _)
  have hint := hg.integral_norm_le_mul_eLpNorm (Fact.out : 1 ≤ p)
  rw [Measure.restrict_apply_univ, ← ENNReal.toReal_rpow, ← measureReal_def] at hint
  rw [setAverage_eq, smul_eq_mul]
  calc m⁻¹ * ∫ y in Omega, ‖g y‖ ∂mu
      ≤ m⁻¹ * (m ^ (1 - 1 / p.toReal) * (K / m * ‖W1p.gradient u‖)) := by
        gcongr
        exact hint.trans (by gcongr)
    _ = K * m ^ (-(1 + 1 / p.toReal)) * ‖W1p.gradient u‖ := by
        have h : m ^ (-(1 + 1 / p.toReal)) =
            m ^ (-1 : ℝ) * m ^ (-1 : ℝ) * m ^ (1 - 1 / p.toReal) := by
          rw [← Real.rpow_add hm, ← Real.rpow_add hm]
          congr 1
          ring
        rw [h, Real.rpow_neg_one]
        ring

/-- **The Poincaré–Wirtinger inequality on a ball.**  On a ball of radius `R` the constant of
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` is `2 ^ (n + 1) * R`: the deviation of
`u ∈ W^{1,p}(B(c, R))` from its mean over the ball is at most `2 ^ (n + 1) * R` times the `Lᵖ`
norm of its weak gradient.  The constant is proportional to `R`, as the scaling of both sides
forces. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball {c : E} {R : ℝ}
    (hOmega : (Omega : Set E) = ball c R) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in (Omega : Set E), W1p.value u y ∂mu) p
        (mu.restrict Omega) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * R) * ‖W1p.gradient u‖ₑ := by
  rcases le_or_gt R 0 with hR | hR
  · -- The ball is empty, so the measure vanishes.
    have h0 : mu.restrict (Omega : Set E) = 0 := by
      rw [hOmega, Metric.ball_eq_empty.2 hR, Measure.restrict_empty]
    simp [h0]
  have hpos : mu (Omega : Set E) ≠ 0 := by
    rw [hOmega]
    exact (measure_ball_pos mu c hR).ne'
  have hconst : mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) /
      mu.real (Omega : Set E) ≤ 2 ^ (finrank ℝ E + 1) * R := by
    rw [hOmega]
    exact mu.addHaar_real_ball_mul_diam_ball_pow_div_le c hR
  refine (W1p.eLpNorm_value_sub_setAverage_le_of_convex (hOmega ▸ convex_ball c R)
    (hOmega ▸ Metric.isBounded_ball (x := c) (r := R)) subset_rfl hpos u).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl)

/-- **The Poincaré–Wirtinger inequality on a ball inside the domain, in `L²`.**  If
`u ∈ H¹(Ω)` and `B(c, R) ⊆ Ω`, then `∫_{B(c, R)} |u - ⨍_{B(c, R)} u|²` is at most
`(2 ^ (n + 1) * R)²` times `∫_{B(c, R)} ‖∇u‖²`.  This is
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball` for the restriction of `u` to the ball,
with both sides written as integrals. -/
theorem W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset {c : E} {R : ℝ}
    (hball : ball c R ⊆ (Omega : Set E)) (u : W1p mu Omega 2) :
    ∫ x in ball c R, (W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu) ^ 2 ∂mu ≤
      (2 ^ (finrank ℝ E + 1) * R) ^ 2 * ∫ x in ball c R, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  -- Restrict `u` to the ball `B = B(c, R)`, viewed as a domain of its own.
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  set uB := W1p.restrictL hB u
  set m := ⨍ y in ball c R, W1p.value u y ∂mu
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c R)] W1p.value u := W1p.value_restrictL_ae hB u
  have hP := W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball (p := 2)
    (rfl : (B : Set E) = ball c R) uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = m := average_congr hval
  rw [havg] at hP
  have hcongr : (fun x ↦ W1p.value uB x - m) =ᵐ[mu.restrict (ball c R)]
      fun x ↦ W1p.value u x - m := hval.mono fun x hx ↦ congrArg (· - m) hx
  have : IsFiniteMeasure (mu.restrict (ball c R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmem : MemLp (fun x ↦ W1p.value uB x - m) 2 (mu.restrict (ball c R)) :=
    (Lp.memLp (W1p.value uB)).sub (memLp_const m)
  -- Convert the `eLpNorm` bound into a bound on integrals of squares.
  have hnorm : ‖hmem.toLp _‖ ≤ 2 ^ (finrank ℝ E + 1) * R * ‖W1p.gradient uB‖ := by
    rw [Lp.norm_toLp, ← toReal_eNorm (W1p.gradient uB),
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (finrank ℝ E + 1) * R),
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) hP
  have hsq : ∫ x in ball c R, (W1p.value u x - m) ^ 2 ∂mu = ‖hmem.toLp _‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp, hcongr] with x hx hx'
    rw [hx, hx', Real.norm_eq_abs, sq_abs]
  have hgrad : ‖W1p.gradient uB‖ ^ 2 = ∫ x in ball c R, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  rw [hsq, ← hgrad, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **The Poincaré–Wirtinger inequality on a ball inside the domain, in `L¹`.**  If
`u ∈ W^{1,p}(Ω)` and `B(c, R) ⊆ Ω`, then `∫_{B(c, R)} |u - ⨍_{B(c, R)} u|` is at most
`2 ^ (n + 1) * R` times `∫_{B(c, R)} ‖∇u‖`.  This is
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball` at exponent one, for the restriction of
`u` to the ball, which lies in `W^{1,1}` because the ball has finite measure. -/
theorem W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset {c : E} {R : ℝ}
    (hball : ball c R ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    ∫ x in ball c R, |W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu| ∂mu ≤
      2 ^ (finrank ℝ E + 1) * R * ∫ x in ball c R, ‖W1p.gradient u x‖ ∂mu := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  -- Restrict `u` to the ball `B = B(c, R)`, viewed as a domain of its own, and lower the
  -- exponent to one.
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uB : W1p mu B 1 := W1p.ofExponentLE (Fact.out : 1 ≤ p) (W1p.restrictL hB u)
  set m := ⨍ y in ball c R, W1p.value u y ∂mu
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c R)] W1p.value u :=
    (W1p.coeFn_value_ofExponentLE _ _).eventuallyEq.trans (W1p.value_restrictL_ae hB u)
  have hgrad : W1p.gradient uB =ᵐ[mu.restrict (ball c R)] W1p.gradient u :=
    (W1p.coeFn_gradient_ofExponentLE _ _).eventuallyEq.trans (W1p.gradient_restrictL_ae hB u)
  have hP := W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball (p := 1)
    (rfl : (B : Set E) = ball c R) uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = m := average_congr hval
  rw [havg] at hP
  have hle : mu.restrict (ball c R) ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  have hint : IntegrableOn (W1p.value u) (ball c R) mu :=
    ((Lp.memLp (W1p.value u)).mono_measure hle).integrable Fact.out
  have hgint : IntegrableOn (W1p.gradient u) (ball c R) mu :=
    ((Lp.memLp (W1p.gradient u)).mono_measure hle).integrable Fact.out
  -- Both sides of `hP` are the integrals in the statement.
  rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x ↦ W1p.value uB x - m)
      ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const),
    Lp.eNorm_def, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _)] at hP
  simp_rw [← Real.norm_eq_abs]
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_norm_eq_lintegral_eNorm (f := fun x ↦ W1p.value u x - m)
      (hint.sub (integrable_const m)), ofReal_integral_norm_eq_lintegral_eNorm hgint]
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hP.trans_eq ?_)
  · filter_upwards [hval] with x hx
    rw [hx]
  · congr 1
    exact lintegral_congr_ae (hgrad.mono fun x hx ↦ by simp only [hx])

/-! ### Functions with vanishing gradient -/

/-- A Sobolev function with vanishing weak gradient is almost everywhere constant on every ball
contained in its domain, by the `L¹` Poincaré–Wirtinger inequality on that ball. -/
private theorem W1p.exists_value_ae_eq_const_ball_of_gradient_eq_zero {u : W1p mu Omega p}
    (hu : W1p.gradient u = 0) {x : E} {r : ℝ} (hxr : ball x r ⊆ (Omega : Set E)) :
    ∃ c : ℝ, ∀ᵐ y ∂mu.restrict (ball x r), W1p.value u y = c := by
  have : IsFiniteMeasure (mu.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set m := ⨍ y in ball x r, W1p.value u y ∂mu
  have hP := W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset hxr u
  have hgrad : ∫ y in ball x r, ‖W1p.gradient u y‖ ∂mu = 0 := by
    refine integral_eq_zero_of_ae (ae_restrict_of_ae_restrict_of_subset hxr ?_)
    filter_upwards [(Lp.ext_iff.1 hu).trans (Lp.coeFn_zero _ _ _)] with y hy
    simp [hy]
  rw [hgrad, mul_zero] at hP
  have hint : IntegrableOn (fun y ↦ |W1p.value u y - m|) (ball x r) mu :=
    ((((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hxr le_rfl)).integrable
      Fact.out).sub (integrable_const m)).abs
  have hzero := (integral_eq_zero_iff_of_nonneg (fun _ ↦ abs_nonneg _) hint).1
    (hP.antisymm (integral_nonneg fun _ ↦ abs_nonneg _))
  exact ⟨m, hzero.mono fun y hy ↦ sub_eq_zero.1 (abs_eq_zero.1 hy)⟩

/-- **A Sobolev function with vanishing gradient on a connected domain is constant.** If `Ω` is
preconnected and the weak gradient of `u ∈ W^{1,p}(Ω)` vanishes, then `u` agrees almost everywhere
on `Ω` with a constant. -/
theorem W1p.exists_value_ae_eq_const_of_gradient_eq_zero
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} (hu : W1p.gradient u = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = c := by
  refine hconn.exists_ae_eq_const_of_forall_nhds (HereditarilyLindelofSpace.isLindelof _)
    fun x hx => ?_
  obtain ⟨r, hr, hxr⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_ball_of_gradient_eq_zero hu hxr
  exact ⟨c, ball x r, ball_mem_nhds x hr, hc⟩

/-- **A Sobolev function with vanishing gradient on a connected domain is a constant.** If `Ω` is
preconnected and of finite measure and the weak gradient of `u ∈ W^{1,p}(Ω)` vanishes, then `u` is
the constant Sobolev function `TauCeti.W1p.const c` for some `c`. -/
theorem W1p.exists_eq_const_of_gradient_eq_zero [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} (hu : W1p.gradient u = 0) :
    ∃ c : ℝ, u = W1p.const c := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hconn hu
  refine ⟨c, W1p.ext_value (Lp.ext ?_)⟩
  filter_upwards [hc, Lp.coeFn_const p (mu.restrict (Omega : Set E)) c] with x h1 h2
  rw [h1, W1p.value_const, h2, Function.const_apply]

/-- On a preconnected domain, a Sobolev function with vanishing gradient and vanishing integral
over a set of positive measure is zero. -/
theorem W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero
    (hconn : IsPreconnected (Omega : Set E)) (hS : S ⊆ (Omega : Set E)) (hS0 : mu.real S ≠ 0)
    {u : W1p mu Omega p} (hu : W1p.gradient u = 0) (hint : ∫ y in S, W1p.value u y ∂mu = 0) :
    u = 0 := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hconn hu
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hS hc), setIntegral_const,
    smul_eq_mul] at hint
  obtain rfl : c = 0 := (mul_eq_zero.1 hint).resolve_left hS0
  exact W1p.ext_value (by rw [W1p.value_zero]; exact Lp.eq_zero_iff_ae_eq_zero.2 hc)

section IntegralL

variable [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- The integral `∫_Ω u` as a continuous linear functional on `W^{1,p}(Ω)`, for `Ω` of finite
measure. -/
def W1p.integralL : W1p mu Omega p →L[ℝ] ℝ :=
  (setIntegralLp (μ := mu.restrict (Omega : Set E)) (𝕜 := ℝ) univ (measure_lt_top _ _)).comp
    W1p.valueL

omit [FiniteDimensional ℝ E] in
/-- `TauCeti.W1p.integralL` is the integral of the value over `Ω`. -/
@[simp]
theorem W1p.integralL_apply (u : W1p mu Omega p) :
    W1p.integralL u = ∫ x in Omega, W1p.value u x ∂mu := by
  rw [W1p.integralL, ContinuousLinearMap.comp_apply, setIntegralLp_apply, Measure.restrict_univ,
    W1p.valueL_apply]

/-- The integral of a constant `c` over `Ω` is `|Ω| c`. -/
theorem W1p.integralL_const (c : ℝ) :
    W1p.integralL (W1p.const c : W1p mu Omega p) = mu.real Omega * c := by
  rw [W1p.integralL_apply, ← smul_eq_mul, ← setIntegral_const]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const p (mu.restrict (Omega : Set E)) c] with x hx
  rw [W1p.value_const, hx, Function.const_apply]

/-- **A Sobolev function with vanishing gradient and mean is zero.** On a preconnected domain of
finite measure, if the weak gradient of `u ∈ W^{1,p}(Ω)` and its integral over `Ω` both vanish,
then `u = 0`. If `Ω` is a null set this holds because `W^{1,p}(Ω)` is trivial. -/
theorem W1p.eq_zero_of_gradient_eq_zero_of_integralL_eq_zero
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} (hu : W1p.gradient u = 0)
    (hint : W1p.integralL u = 0) : u = 0 := by
  by_cases h0 : mu.real Omega = 0
  · have hae : ae (mu.restrict (Omega : Set E)) = ⊥ := ae_restrict_eq_bot.2
      ((measureReal_eq_zero_iff (isFiniteMeasure_restrict.1 inferInstance)).1 h0)
    exact W1p.ext_value (Lp.ext (hae.le Filter.eventually_bot))
  · rw [W1p.integralL_apply] at hint
    exact W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero hconn subset_rfl h0 hu hint

end IntegralL

/-- **A Sobolev function on the whole space with vanishing gradient is zero.** For `p < ∞` and a
nontrivial space `E`, if the weak gradient of `u ∈ W^{1,p}(E)` vanishes, then `u = 0`: it is
almost everywhere constant, and the only constant in `Lᵖ(E)` is zero, since `E` has infinite
measure. -/
theorem W1p.eq_zero_of_gradient_eq_zero [Nontrivial E] (hp : p ≠ ∞) {u : W1p mu ⊤ p}
    (hu : W1p.gradient u = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero
    (by simpa using isPreconnected_univ) hu
  simp only [Opens.coe_top, Measure.restrict_univ] at hc
  have hc0 : c = 0 := by
    refine ((memLp_const_iff (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp).1
      ((W1p.memLp_value u).ae_eq hc)).resolve_right ?_
    rw [measure_univ_of_isAddLeftInvariant]
    exact lt_irrefl _
  subst hc0
  refine W1p.ext_value (Lp.ext ?_)
  simp only [Opens.coe_top, Measure.restrict_univ]
  filter_upwards [hc] with x hx
  simp [hx]

/-- **Integration up to a constant on a preconnected domain.** If `Ω` is preconnected and the weak
gradient of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with the classical gradient `∇ q` of
a function `q` that is `C¹` on `Ω`, then `u` agrees almost everywhere on `Ω` with `q + c` for some
constant `c : ℝ`. Neither boundedness of `Ω` nor global `Lᵖ` integrability of `q` is needed. -/
theorem W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq
    (hconn : IsPreconnected (Omega : Set E)) {u : W1p mu Omega p} {q : E → ℝ}
    (hq : ContDiffOn ℝ 1 q Omega)
    (hgrad : (W1p.gradient u : E → E) =ᵐ[mu.restrict Omega] ∇ q) :
    ∃ c : ℝ, (W1p.value u : E → ℝ) =ᵐ[mu.restrict Omega] fun x ↦ q x + c := by
  have hloc : ∃ c : ℝ, ∀ᵐ y ∂mu.restrict Omega, W1p.value u y - q y = c := by
    refine hconn.exists_ae_eq_const_of_forall_nhds (HereditarilyLindelofSpace.isLindelof _)
      fun x hx ↦ ?_
    obtain ⟨R, hR, hxR⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
    set r := R / 2
    have hr : 0 < r := half_pos hR
    let B : Opens E := ⟨ball x r, isOpen_ball⟩
    have hKsub : closedBall x r ⊆ (Omega : Set E) :=
      (closedBall_subset_ball (half_lt_self hR)).trans hxR
    have hBO : B ≤ Omega := ball_subset_closedBall.trans hKsub
    obtain ⟨v, hvval, hvgrad⟩ :=
      W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (Omega := B) (p := p)
        Omega.isOpen hq (isCompact_closedBall x r) ball_subset_closedBall hKsub
    have hdiff_grad : W1p.gradient (W1p.restrictL hBO u - v) = 0 := by
      rw [W1p.gradient_sub, sub_eq_zero]
      apply Lp.ext
      exact (W1p.gradient_restrictL_ae hBO u).trans <|
        Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hBO hgrad) hvgrad.symm
    obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero
      (Omega := B) (convex_ball x r).isPreconnected hdiff_grad
    refine ⟨c, ball x r, ball_mem_nhds x hr, ?_⟩
    filter_upwards [hc, W1p.value_sub_ae (W1p.restrictL hBO u) v,
      W1p.value_restrictL_ae hBO u, hvval] with y hy hsub huB hvB
    rw [← hy, hsub, Pi.sub_apply, huB, hvB]
  obtain ⟨c, hc⟩ := hloc
  refine ⟨c, hc.mono fun x hx ↦ ?_⟩
  linarith

end TauCeti
