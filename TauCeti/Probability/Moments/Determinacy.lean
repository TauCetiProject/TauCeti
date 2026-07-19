module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Analytic.Order

/-!
# Moment determinacy of finite measures with finite exponential moments

A finite measure on `ℝ` whose exponential moments are finite in a neighbourhood of the origin is
determined by its sequence of polynomial moments `∫ xⁿ dμ`.  This is the analytic engine behind the
completeness step (**B1**) of the `OrthogonalL2Bases` roadmap
(`TauCetiRoadmap/OrthogonalL2Bases/README.md`, *Part B1 — Completeness toolkit (moment
determinacy)*): the roadmap's `ae_eq_zero_of_forall_moment_eq_zero`-style lemmas rest on the fact
that "vanishing moments" pins a distribution down, which for finite measures is exactly the
determinacy result proved here.

The mechanism is the one the roadmap describes — the (complex) moment-generating function is
analytic on a strip around the imaginary axis, and its Taylor coefficients at `0` are the moments,
so matching moments force the two functions to agree, hence the characteristic functions agree and
the measures coincide.  The proof stays inside Mathlib's `ProbabilityTheory.complexMGF` /
`MeasureTheory.charFun` API:

* `ProbabilityTheory.analyticAt_complexMGF` and `analyticOnNhd_complexMGF` supply the analyticity
  on the strip `{z | z.re ∈ interior (integrableExpSet id μ)}`;
* `ProbabilityTheory.iteratedDeriv_complexMGF` identifies the `n`-th derivative at `0` with the
  `n`-th complex moment;
* the identity principle (`analyticOrderAt_eq_top`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates equality from `0` to the whole
  strip, in particular to the imaginary axis;
* `ProbabilityTheory.complexMGF_id_mul_I` turns the imaginary-axis values into `charFun`, and
  `MeasureTheory.Measure.ext_of_charFun` concludes.

## Main declarations

* `TauCeti.charFun_eq_of_forall_integral_pow_eq`: matching moments (and finite exponential moments
  near `0`) give equal characteristic functions.
* `TauCeti.measure_eq_of_forall_integral_pow_eq`: matching moments determine a finite measure on
  `ℝ`.
* `TauCeti.measure_eq_of_forall_integral_pow_eq_of_forall_integrable_exp`: the same conclusion from
  the roadmap's exponential-moment hypothesis `∀ a ≥ 0, Integrable (fun x => exp (a * |x|)) μ`,
  which forces every exponential moment finite (hence the strip is the whole plane).
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

variable {μ ν : Measure ℝ}

/-- The `n`-th derivative at `0` of the complex moment-generating function of `μ` is the `n`-th
complex moment `↑(∫ xⁿ dμ)`.  Immediate from `iteratedDeriv_complexMGF` at `z = 0`, where the
exponential factor is `1`. -/
private lemma iteratedDeriv_complexMGF_id_zero
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF id μ) 0 = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
  have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
  rw [iteratedDeriv_complexMGF (z := 0) hz n]
  have hpow : ∀ x : ℝ, ((x : ℂ)) ^ n * Complex.exp (0 * (x : ℂ)) = (((x ^ n : ℝ)) : ℂ) := by
    intro x
    rw [zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  simp only [id_eq, hpow]
  exact integral_ofReal

/-- **Moment determinacy at the level of characteristic functions.** If two measures on `ℝ` have
finite exponential moments near `0` (so their complex moment-generating functions are analytic on a
strip about the imaginary axis) and agree on every polynomial moment `∫ xⁿ`, then their
characteristic functions coincide. -/
theorem charFun_eq_of_forall_integral_pow_eq
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    charFun μ = charFun ν := by
  have hμ0 : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
  have hν0 : (0 : ℂ).re ∈ interior (integrableExpSet id ν) := by simpa using hν
  have hAμ : AnalyticAt ℂ (complexMGF id μ) 0 := analyticAt_complexMGF hμ0
  have hAν : AnalyticAt ℂ (complexMGF id ν) 0 := analyticAt_complexMGF hν0
  -- The difference of the two moment-generating functions has all derivatives zero at `0`.
  have hiter : ∀ i, iteratedDeriv i (fun z => complexMGF id μ z - complexMGF id ν z) 0 = 0 := by
    intro i
    rw [iteratedDeriv_fun_sub hAμ.contDiffAt hAν.contDiffAt,
      iteratedDeriv_complexMGF_id_zero hμ i, iteratedDeriv_complexMGF_id_zero hν i, hmom i,
      sub_self]
  have hsub : AnalyticAt ℂ (fun z => complexMGF id μ z - complexMGF id ν z) 0 := hAμ.sub hAν
  have hord : analyticOrderAt (fun z => complexMGF id μ z - complexMGF id ν z) 0 = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun m =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).mpr fun i _ => hiter i
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), complexMGF id μ z - complexMGF id ν z = 0 :=
    analyticOrderAt_eq_top.mp hord
  have hEqNear : complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν := by
    filter_upwards [hnear] with z hz using sub_eq_zero.mp hz
  -- Propagate the equality across the common analyticity strip by the identity principle.
  set U : Set ℂ :=
    Complex.reLm ⁻¹' (interior (integrableExpSet id μ) ∩ interior (integrableExpSet id ν))
    with hUdef
  have hUconn : IsPreconnected U :=
    ((convex_integrableExpSet.interior.inter
      convex_integrableExpSet.interior).linear_preimage Complex.reLm).isPreconnected
  have hsubμ : U ⊆ {z | z.re ∈ interior (integrableExpSet id μ)} := fun z hz => hz.1
  have hsubν : U ⊆ {z | z.re ∈ interior (integrableExpSet id ν)} := fun z hz => hz.2
  have hAμU : AnalyticOnNhd ℂ (complexMGF id μ) U := analyticOnNhd_complexMGF.mono hsubμ
  have hAνU : AnalyticOnNhd ℂ (complexMGF id ν) U := analyticOnNhd_complexMGF.mono hsubν
  have h0U : (0 : ℂ) ∈ U := ⟨hμ0, hν0⟩
  have hEqU : Set.EqOn (complexMGF id μ) (complexMGF id ν) U :=
    hAμU.eqOn_of_preconnected_of_eventuallyEq hAνU hUconn h0U hEqNear
  -- The imaginary axis lies in the strip, and there the values are the characteristic functions.
  ext t
  have htU : ((t : ℂ) * I) ∈ U := by
    have ht0 : reLm ((t : ℂ) * I) = 0 := by rw [Complex.reLm_coe]; simp
    simp only [hUdef, Set.mem_preimage, Set.mem_inter_iff, ht0]
    exact ⟨hμ, hν⟩
  have := hEqU htU
  rwa [complexMGF_id_mul_I, complexMGF_id_mul_I] at this

/-- **Moment determinacy for finite measures on `ℝ`.** A finite measure on `ℝ` with finite
exponential moments near `0` is determined by its polynomial moments `∫ xⁿ`.  Combines
`charFun_eq_of_forall_integral_pow_eq` with `MeasureTheory.Measure.ext_of_charFun`. -/
theorem measure_eq_of_forall_integral_pow_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  Measure.ext_of_charFun (charFun_eq_of_forall_integral_pow_eq hμ hν hmom)

/-- If every exponential moment `∫ e^{a|x|} dμ` is finite, then `0` lies in the interior of the
integrability set `integrableExpSet id μ` (indeed the set is all of `ℝ`): the exponential
`e^{tx}` is dominated by `e^{|t| · |x|}`. -/
lemma zero_mem_interior_integrableExpSet_id_of_forall_integrable_exp
    (h : ∀ a : ℝ, 0 ≤ a → Integrable (fun x => Real.exp (a * |x|)) μ) :
    (0 : ℝ) ∈ interior (integrableExpSet id μ) := by
  have huniv : integrableExpSet id μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true, integrableExpSet, Set.mem_setOf_eq, id_eq]
    refine (h |t| (abs_nonneg t)).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans_eq (abs_mul t x))
  rw [huniv, interior_univ]
  exact Set.mem_univ _

/-- **Moment determinacy, exponential-moment form (the roadmap's B1 hypothesis).** A finite measure
on `ℝ` all of whose exponential moments `∫ e^{a|x|} dμ` are finite is determined by its polynomial
moments.  This is the form the completeness argument consumes: the hypothesis holds for Gaussian
decay and automatically for compactly supported measures. -/
theorem measure_eq_of_forall_integral_pow_eq_of_forall_integrable_exp
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ a : ℝ, 0 ≤ a → Integrable (fun x => Real.exp (a * |x|)) μ)
    (hν : ∀ a : ℝ, 0 ≤ a → Integrable (fun x => Real.exp (a * |x|)) ν)
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  measure_eq_of_forall_integral_pow_eq
    (zero_mem_interior_integrableExpSet_id_of_forall_integrable_exp hμ)
    (zero_mem_interior_integrableExpSet_id_of_forall_integrable_exp hν) hmom

end TauCeti
