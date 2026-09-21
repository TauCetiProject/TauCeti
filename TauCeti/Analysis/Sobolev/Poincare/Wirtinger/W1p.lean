/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Exhaustion
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.W1p.LocalApproximation
import TauCeti.MeasureTheory.Function.Lp.SetIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure.  This
file proves, for `1 ≤ p < ∞` and every `u ∈ W^{1,p}(Ω)`,

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * ‖∇u‖_{Lᵖ(Ω)}`,

the inequality that `TauCeti.eLpNorm_sub_setAverage_le_of_convex` proves, with the same constant,
for `C¹` functions.  A weakly differentiable function is not `C¹`, so the two are genuinely
different statements, and it is the Sobolev one that an existence or regularity argument can use.

Subtracting the mean is not a normalisation that could be dropped: no inequality of this shape
holds for the deviation from an arbitrary constant, since the nonzero constants themselves lie in
`W^{1,p}(Ω)` with vanishing gradient.

## The approximation

Test functions on `Ω` are dense in `W^{1,p}(Ω)` only after `Ω` is shrunk:
`TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ` approximates `u` on a subdomain `U`
whose closure is a compact subset of `Ω`.  Two limits are therefore taken.

* On a fixed such `U`, convex so that the `C¹` inequality applies to it, the Sobolev functions
  satisfying the inequality form a closed set — the mean over `S` is a continuous functional, by
  `TauCeti.lipschitzWith_setIntegral` — which contains every test function, hence their closure.
* The convex subdomains are then increased to `Ω`, along the exhaustion
  `TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`.  The means over `S ∩ U`
  converge to the mean over `S`, and Fatou's lemma for the `Lᵖ` seminorm,
  `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`, passes the inequality to the limit.  Only the
  measure of `S ∩ U` needs to be tracked, since `diam U ≤ diam Ω` already bounds the numerator of
  the constant.

## Main declarations

* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`: the inequality on `W^{1,p}(Ω)`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball`: the constant on a ball of radius `R`
  is `2 ^ (n + 1) * R`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16.
* L. C. Evans, *Partial Differential Equations*, Section 5.8.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

/-! ### The mean over a subset is a continuous functional -/

omit [FiniteDimensional ℝ E] in
/-- The mean of the value of a first-order Sobolev function over a fixed subset of finite
measure depends continuously on the function. -/
private theorem continuous_setAverage_value (hp : p ≠ ∞) (hSU : S ⊆ (U : Set E))
    (hUfin : mu (U : Set E) ≠ ∞) :
    Continuous fun v : W1p mu U p => ⨍ y in S, W1p.value v y ∂mu := by
  have hrs : (mu.restrict (U : Set E)).restrict S = mu.restrict S :=
    Measure.restrict_restrict_of_subset hSU
  have hmeas : (mu.restrict (U : Set E)) S = mu S := by
    rw [← Measure.restrict_apply_univ, hrs, Measure.restrict_apply_univ]
  have hEq : ∀ v : W1p mu U p, (⨍ y in S, W1p.value v y ∂mu) =
      (mu.real S)⁻¹ * ∫ y in S, W1p.valueL v y ∂(mu.restrict (U : Set E)) := fun v => by
    rw [setAverage_eq, smul_eq_mul, W1p.valueL_apply, hrs]
  have hF : Continuous fun f : Lp ℝ p (mu.restrict (U : Set E)) =>
      ∫ y in S, f y ∂(mu.restrict (U : Set E)) :=
    (lipschitzWith_setIntegral (F := ℝ) (μ := mu.restrict (U : Set E)) (s := S) hp
      (by rw [hmeas]; exact ne_top_of_le_ne_top hUfin (measure_mono hSU))).continuous
  simp only [hEq]
  exact continuous_const.mul
    (hF.comp' (W1p.valueL (mu := mu) (Omega := U) (p := p)).continuous)

/-! ### The inequality on a relatively compact convex subdomain -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Rewriting the deviation from a constant as a distance in `Lᵖ`. -/
private theorem eLpNorm_sub_const_eq_enorm (a : ℝ)
    [IsFiniteMeasure (mu.restrict (U : Set E))] (f : Lp ℝ p (mu.restrict U)) :
    eLpNorm (fun x => f x - a) p (mu.restrict U) =
      ‖f - Lp.const p (mu.restrict (U : Set E)) a‖ₑ := by
  rw [Lp.enorm_def]
  refine (eLpNorm_congr_ae ?_).symm
  filter_upwards [Lp.coeFn_sub f (Lp.const p (mu.restrict (U : Set E)) a),
    Lp.coeFn_const (p := p) (μ := mu.restrict (U : Set E)) (c := a)] with x h1 h2
  rw [h1, Pi.sub_apply, h2]
  rfl

/-- **The Poincaré–Wirtinger inequality for a limit of test functions.**  It holds for every
Sobolev function on `U` that is an `Lᵖ`-limit of restrictions of test functions on a larger
domain. -/
private theorem eLpNorm_value_sub_setAverage_le_of_mem_closure (hp : p ≠ ∞) (hU : U ≤ Omega)
    (hUc : Convex ℝ (U : Set E)) (hUb : Bornology.IsBounded (U : Set E))
    (hSU : S ⊆ (U : Set E)) (hS0 : mu S ≠ 0) {v : W1p mu U p}
    (hv : v ∈ closure (Set.range fun (phi : 𝓓(Omega, ℝ)) =>
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi))) :
    eLpNorm (fun x => W1p.value v x - ⨍ y in S, W1p.value v y ∂mu) p (mu.restrict U) ≤
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
    have h1 : Continuous fun w : W1p mu U p =>
        ‖W1p.value w - Lp.const p (mu.restrict (U : Set E)) (⨍ y in S, W1p.value w y ∂mu)‖ := by
      refine Continuous.norm (Continuous.sub ?_ ?_)
      · have hcont : Continuous fun w : W1p mu U p => W1p.valueL w :=
          (W1p.valueL (mu := mu) (Omega := U) (p := p)).continuous
        simpa only [W1p.valueL_apply] using hcont
      · exact (Lp.constL p (mu.restrict (U : Set E)) ℝ).continuous.comp
          (continuous_setAverage_value hp hSU hUfin)
    have h2 : Continuous fun w : W1p mu U p => C * ‖W1p.gradient w‖ := by
      refine continuous_const.mul (Continuous.norm ?_)
      have hcont : Continuous fun w : W1p mu U p => W1p.gradientL w :=
        (W1p.gradientL (mu := mu) (Omega := U) (p := p)).continuous
      simpa only [W1p.gradientL_apply] using hcont
    exact isClosed_le h1 h2
  -- Every test function satisfies it, by the `C¹` inequality on the convex set `U`.
  have hrange : (Set.range fun (phi : 𝓓(Omega, ℝ)) =>
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)) ⊆ {w : W1p mu U p |
      ‖W1p.value w - Lp.const p (mu.restrict (U : Set E))
        (⨍ y in S, W1p.value w y ∂mu)‖ ≤ C * ‖W1p.gradient w‖} := by
    rintro w ⟨phi, rfl⟩
    set w := W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)
    have haeU : W1p.value w =ᵐ[mu.restrict (U : Set E)] fun x => phi x := by
      refine (W1p.value_restrictL_ae hU _).trans ?_
      rw [W1p.value_ofTestFunctionₗ]
      exact (testFunctionLp_apply_ae (mu := mu) p phi).filter_mono
        (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
    have hgradU : W1p.gradient w =ᵐ[mu.restrict (U : Set E)] fun x => ∇ (phi : E → ℝ) x := by
      refine (W1p.gradient_restrictL_ae hU _).trans ?_
      rw [W1p.gradient_ofTestFunctionₗ]
      exact (gradientTestFunctionLp_apply_ae (mu := mu) p phi).filter_mono
        (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
    have havg : (⨍ y in S, W1p.value w y ∂mu) = ⨍ y in S, phi y ∂mu :=
      average_congr (haeU.filter_mono (ae_mono (Measure.restrict_mono hSU le_rfl)))
    have hmain := eLpNorm_sub_setAverage_le_of_convex (μ := mu) (u := fun x => (phi : E → ℝ) x)
      U.isOpen hUc hUb (phi.contDiff.of_le (by simp)).contDiffOn hSU hS0
      (Fact.out : (1 : ℝ≥0∞) ≤ p) hp
    have hkey : ‖W1p.value w - Lp.const p (mu.restrict (U : Set E))
        (⨍ y in S, W1p.value w y ∂mu)‖ₑ ≤ ENNReal.ofReal C * ‖W1p.gradient w‖ₑ := by
      rw [← eLpNorm_sub_const_eq_enorm, Lp.enorm_def]
      calc eLpNorm (fun x => W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) p (mu.restrict U)
          = eLpNorm (fun x => (phi : E → ℝ) x - ⨍ y in S, (phi : E → ℝ) y ∂mu) p
              (mu.restrict U) := by
            rw [havg]
            exact eLpNorm_congr_ae (haeU.mono fun x hx => by simp only [hx])
        _ ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ (phi : E → ℝ)) p (mu.restrict U) := hmain
        _ = ENNReal.ofReal C * eLpNorm (W1p.gradient w) p (mu.restrict U) := by
            congr 1
            refine eLpNorm_congr_norm_ae ?_
            filter_upwards [hgradU] with x hx
            rw [hx, norm_gradient_eq_norm_fderiv]
    rw [← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul hC0] at hkey
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hkey
  have hv' := closure_minimal hrange hclosed hv
  rw [eLpNorm_sub_const_eq_enorm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal hv'

/-! ### The inequality on the whole domain -/

/-- **The Poincaré–Wirtinger inequality on `W^{1,p}(Ω)`.**  Let `Ω` be a bounded convex open set
in a finite-dimensional real inner product space of dimension `n`, and let `S ⊆ Ω` be measurable
of positive measure.  For `1 ≤ p < ∞`, every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by
at most `μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times the `Lᵖ` norm of its weak gradient. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_convex (hp : p ≠ ∞)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hSm : NullMeasurableSet S mu) (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0)
    (u : W1p mu Omega p) :
    eLpNorm (fun x => W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict Omega) ≤
      ENNReal.ofReal (mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) / mu.real S) *
        ‖W1p.gradient u‖ₑ := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Omega.isOpen hconv hb
  have hVsub : ∀ n, V n ⊆ (Omega : Set E) := fun n => subset_closure.trans (hVclosure n)
  have hWle : ∀ n, (⟨V n, hVopen n⟩ : Opens E) ≤ Omega := fun n =>
    SetLike.coe_subset_coe.mp (hVsub n)
  have hOfin : mu (Omega : Set E) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hb.isCompact_closure.measure_lt_top).ne
  have hSfin : mu S ≠ ∞ := ne_top_of_le_ne_top hOfin (measure_mono hS)
  have hSRpos : 0 < mu.real S := ENNReal.toReal_pos hS0 hSfin
  have hSR0 : mu.real S ≠ 0 := hSRpos.ne'
  -- The means over `S ∩ V n` converge to the mean over `S`.
  have hSVmono : Monotone fun n => S ∩ V n := fun m n hmn =>
    inter_subset_inter_right _ (hVmono hmn)
  have hSVunion : ⋃ n, S ∩ V n = S := by
    rw [← inter_iUnion, hVunion, inter_eq_left.2 hS]
  have hSVmeas : ∀ n, NullMeasurableSet (S ∩ V n) mu := fun n =>
    hSm.inter (hVopen n).measurableSet.nullMeasurableSet
  have hmeasR : Tendsto (fun n => mu.real (S ∩ V n)) atTop (𝓝 (mu.real S)) := by
    refine (ENNReal.tendsto_toReal hSfin).comp ?_
    simpa [hSVunion, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := mu) hSVmono
  have hint : IntegrableOn (W1p.value u) S mu := by
    have : IsFiniteMeasure (mu.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
    exact ((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hS le_rfl)).integrable Fact.out
  have ha : Tendsto (fun n => ⨍ y in S ∩ V n, W1p.value u y ∂mu) atTop
      (𝓝 (⨍ y in S, W1p.value u y ∂mu)) := by
    simp only [setAverage_eq, smul_eq_mul]
    refine (hmeasR.inv₀ hSR0).mul ?_
    simpa [hSVunion] using
      tendsto_setIntegral_of_monotone₀ hSVmeas hSVmono (by rwa [hSVunion])
  -- The inequality on each piece, with the constant of the whole domain in the numerator.
  set K : ℝ := mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) with hKdef
  have hpiece : ∀ n, mu (S ∩ V n) ≠ 0 →
      eLpNorm (fun x => W1p.value u x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) p
          (mu.restrict (V n)) ≤
        ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ := by
    intro n hn
    set W : Opens E := ⟨V n, hVopen n⟩
    set v : W1p mu W p := W1p.restrictL (hWle n) u
    have hval : W1p.value v =ᵐ[mu.restrict (V n)] W1p.value u := W1p.value_restrictL_ae _ u
    have hgrad : W1p.gradient v =ᵐ[mu.restrict (V n)] W1p.gradient u :=
      W1p.gradient_restrictL_ae _ u
    have havg : (⨍ y in S ∩ V n, W1p.value v y ∂mu) = ⨍ y in S ∩ V n, W1p.value u y ∂mu :=
      average_congr (hval.filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_right le_rfl)))
    have hbase := eLpNorm_value_sub_setAverage_le_of_mem_closure (S := S ∩ V n) hp (hWle n)
      (hVconv n) (hb.subset (hVsub n)) inter_subset_right hn
      (W1p.restrictL_mem_closure_range_ofTestFunctionₗ hp (hVcompact n) (hVclosure n) u)
    rw [havg] at hbase
    have hpos : 0 < mu.real (S ∩ V n) :=
      ENNReal.toReal_pos hn (ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
    have hcongr : eLpNorm (fun x => W1p.value v x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) p
          (mu.restrict (V n)) =
        eLpNorm (fun x => W1p.value u x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) p
          (mu.restrict (V n)) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hval] with x hx
      show W1p.value v x - _ = W1p.value u x - _
      rw [hx]
    have hconst : mu.real (ball (0 : E) 1) * diam (V n) ^ (finrank ℝ E + 1) /
        mu.real (S ∩ V n) ≤ K / mu.real (S ∩ V n) := by
      rw [hKdef]
      gcongr
      exact Metric.diam_mono (hVsub n) hb
    have hgradle : ‖W1p.gradient v‖ₑ ≤ ‖W1p.gradient u‖ₑ :=
      calc ‖W1p.gradient v‖ₑ
          = eLpNorm (W1p.gradient u) p (mu.restrict (V n)) := by
            rw [Lp.enorm_def]; exact eLpNorm_congr_ae hgrad
        _ ≤ eLpNorm (W1p.gradient u) p (mu.restrict (Omega : Set E)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono (hVsub n) le_rfl)
        _ = ‖W1p.gradient u‖ₑ := (Lp.enorm_def _).symm
    exact hcongr ▸ hbase.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) hgradle)
  -- Fatou along the exhaustion.
  set a : ℕ → ℝ := fun n => ⨍ y in S ∩ V n, W1p.value u y ∂mu
  set b : ℝ := ⨍ y in S, W1p.value u y ∂mu
  set g : ℕ → E → ℝ := fun n => (V n).indicator fun x => W1p.value u x - a n with hgdef
  have hsm : StronglyMeasurable (W1p.value u) :=
    (W1p.value u : E →ₘ[mu.restrict (Omega : Set E)] ℝ).stronglyMeasurable
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) mu := fun n =>
    ((hsm.sub stronglyMeasurable_const).indicator (hVopen n).measurableSet).aestronglyMeasurable
  have hgval : ∀ n x, x ∈ V n → g n x = W1p.value u x - a n := fun n x hx => by
    simp only [hgdef]
    exact Set.indicator_of_mem hx _
  have hgzero : ∀ n x, x ∉ V n → g n x = 0 := fun n x hx => by
    simp only [hgdef]
    exact Set.indicator_of_notMem hx _
  have hptw : ∀ x, Tendsto (fun n => g n x) atTop
      (𝓝 ((Omega : Set E).indicator (fun x => W1p.value u x - b) x)) := by
    intro x
    by_cases hx : x ∈ (Omega : Set E)
    · obtain ⟨n₀, hn₀⟩ := mem_iUnion.1 (hVunion ▸ hx)
      rw [Set.indicator_of_mem hx]
      refine Tendsto.congr' (Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
        (tendsto_const_nhds.sub ha)
      exact (hgval n x (hVmono hn hn₀)).symm
    · rw [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun n => (hgzero n x fun hmem => hx (hVsub n hmem)).symm
  have hlim : eLpNorm (fun x => W1p.value u x - b) p (mu.restrict Omega) ≤
      atTop.liminf fun n => eLpNorm (g n) p mu := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict Omega.isOpen.measurableSet]
    exact Lp.eLpNorm_lim_le_liminf_eLpNorm hgmeas
      ((Omega : Set E).indicator fun x => W1p.value u x - b) (ae_of_all _ hptw)
  have hbound : ∀ᶠ n in atTop, eLpNorm (g n) p mu ≤
      ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ := by
    filter_upwards [hmeasR.eventually (lt_mem_nhds hSRpos)] with n hn
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hVopen n).measurableSet]
    refine hpiece n fun h0 => ?_
    rw [measureReal_def, h0] at hn
    simp at hn
  have htend : Tendsto (fun n => ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ)
      atTop (𝓝 (ENNReal.ofReal (K / mu.real S) * ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeasR hSR0))
      (Or.inr (by simp))
  calc eLpNorm (fun x => W1p.value u x - b) p (mu.restrict Omega)
      ≤ atTop.liminf fun n => eLpNorm (g n) p mu := hlim
    _ ≤ atTop.liminf fun n => ENNReal.ofReal (K / mu.real (S ∩ V n)) * ‖W1p.gradient u‖ₑ :=
        Filter.liminf_le_liminf hbound
    _ = ENNReal.ofReal (K / mu.real S) * ‖W1p.gradient u‖ₑ := htend.liminf_eq


/-- **The Poincaré–Wirtinger inequality on a ball.**  On a ball of radius `R` the constant of
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` is `2 ^ (n + 1) * R`: the deviation of
`u ∈ W^{1,p}(B(c, R))` from its mean over the ball is at most `2 ^ (n + 1) * R` times the `Lᵖ`
norm of its weak gradient.  The constant is proportional to `R`, as the scaling of both sides
forces. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball [Nontrivial E] {c : E} {R : ℝ}
    (hp : p ≠ ∞) (hR : 0 < R) (hOmega : (Omega : Set E) = ball c R) (u : W1p mu Omega p) :
    eLpNorm (fun x => W1p.value u x - ⨍ y in (Omega : Set E), W1p.value u y ∂mu) p
        (mu.restrict Omega) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * R) * ‖W1p.gradient u‖ₑ := by
  have hpos : mu (Omega : Set E) ≠ 0 := by
    rw [hOmega]; exact (measure_ball_pos mu c hR).ne'
  have homega : 0 < mu.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  have hmeas : mu.real (Omega : Set E) = R ^ finrank ℝ E * mu.real (ball (0 : E) 1) := by
    rw [hOmega, measureReal_def, measureReal_def, Measure.addHaar_ball mu c hR.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
  have hconst : mu.real (ball 0 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1) /
      mu.real (Omega : Set E) ≤ 2 ^ (finrank ℝ E + 1) * R := by
    rw [hmeas, div_le_iff₀ (by positivity)]
    calc mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ (finrank ℝ E + 1)
        ≤ mu.real (ball (0 : E) 1) * (2 * R) ^ (finrank ℝ E + 1) := by
          gcongr
          rw [hOmega]
          exact Metric.diam_ball hR.le
      _ = 2 ^ (finrank ℝ E + 1) * R * (R ^ finrank ℝ E * mu.real (ball (0 : E) 1)) := by ring
  refine (W1p.eLpNorm_value_sub_setAverage_le_of_convex hp (hOmega ▸ convex_ball c R)
    (hOmega ▸ Metric.isBounded_ball (x := c) (r := R))
    Omega.isOpen.measurableSet.nullMeasurableSet subset_rfl hpos u).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl)

end TauCeti
