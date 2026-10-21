/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.PDE.HopfLax
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Endpoint
import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.PlanInterpolation
import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Subsolution
import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# The Benamou–Brenier formula

Let `E` be a finite-dimensional real normed space, let `1 < p < ∞`, and let `t ↦ νₜ` be a curve of
finite measures on `E`, narrowly continuous on `[a, b]`, solving the continuity equation
`∂ₜ νₜ + div (vₜ νₜ) = 0` on `(a, b)`, with `ν_a` a probability measure. This file proves that the
`p`-action of the velocity field bounds the Wasserstein distance between the endpoint laws:

`W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`.

On `[0, 1]` this reads `W_p (ν₀, ν₁) ^ p ≤ ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`, the lower bound in the
Benamou–Brenier formula. The displacement interpolation of an optimal coupling solves the
continuity equation with action at most `W_p (μ, μ') ^ p`
(`TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le`), and it
is a narrowly continuous curve. Together these give the **Benamou–Brenier formula**: for
probability measures `μ`, `μ'` at finite `W_p` distance,

`W_p (μ, μ') ^ p = min ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`,

the minimum running over the narrowly continuous curves of finite measures from `μ` to `μ'` that
solve the continuity equation on `(0, 1)`, and being attained by the displacement interpolation
of an optimal coupling.

The proof is by duality. By Kantorovich duality,
`W_p (ν_a, ν_b) ^ p` is the supremum of `∫ φ dν_a + ∫ ψ dν_b` over pairs of bounded upper
semicontinuous potentials with `φ x + ψ y ≤ ‖x - y‖ ^ p`
(`TauCeti.isLUB_ofReal_kantorovichDualValue_upperSemicontinuous_of_lowerSemicontinuous`). For such
a pair the Hopf–Lax function

`u (t, x) = inf_y (-φ y + (b - a) ^ (p - 1) ‖x - y‖ ^ p / (t - a) ^ (p - 1))`

tends to `-φ` as `t → a⁺`, lies above `ψ` at time `b`, and satisfies the subsolution inequality
`u (t + h, x + h w) ≤ u (t, x) + h (b - a) ^ (p - 1) ‖w‖ ^ p`. Testing the continuity equation
against `u`
(`TauCeti.IsContinuityEquation.ofReal_integral_sub_integral_le_lintegral_of_add_smul_le`) bounds
`∫ ψ dν_b + ∫ φ dν_a` by `(b - a) ^ (p - 1)` times the action. Since `u` is only controlled
at times after `a`, the test is carried out for `u` delayed by a small time `δ > 0`, and `δ → 0`
is handled by the continuity of Hopf–Lax functions at positive times and their convergence to the
initial datum (`TauCeti.continuousOn_hopfLax_norm_rpow` and
`TauCeti.tendsto_hopfLax_norm_rpow_nhdsGT_zero`). The latter is where `1 < p` and the upper
semicontinuity of `φ` are used.

## Main results

* `TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le_mul_lintegral`: the action bounds the
  Wasserstein distance, `W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`.
* `TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le_lintegral`: the Benamou–Brenier lower
  bound `W_p (ν₀, ν₁) ^ p ≤ ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`.
* `TauCeti.isLeast_wassersteinEDist_rpow_lintegral`: the Benamou–Brenier formula, `W_p (μ, μ') ^ p`
  is the least action of a solution of the continuity equation joining `μ` to `μ'`, attained by
  the displacement interpolation of an optimal coupling.

## References

* J.-D. Benamou and Y. Brenier, *A computational fluid mechanics solution to the
  Monge–Kantorovich mass transfer problem*, Numer. Math. 84 (2000), 375--393.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 7, on the
  Hopf–Lax formula as the dual side of the action-minimization problem.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {v : ℝ → E → E} {a b : ℝ} {ν : ℝ → FiniteMeasure E}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- For a bounded initial datum `f` and `k ≥ 0`, `k` times the Hopf–Lax value of `f` for the cost
`‖w‖ ^ p` is bounded uniformly over all times `t ≥ 0` and positions. -/
private theorem exists_norm_mul_hopfLax_norm_rpow_le {p k : ℝ} (hp : 0 < p) {f : E → ℝ}
    (hf : Bornology.IsBounded (range f)) (hk : 0 ≤ k) :
    ∃ M, ∀ t, 0 ≤ t → ∀ x, ‖k * hopfLax (‖·‖ ^ p) f t x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  refine ⟨k * C, fun t ht x ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left (abs_hopfLax_norm_rpow_le hp
    (fun y ↦ by simpa [Real.norm_eq_abs] using hC _ ⟨y, rfl⟩) ht x) hk

namespace IsContinuityEquation

/-- One delayed Hopf–Lax test. For a bounded initial datum `f`, `k ≥ 0`, `1 ≤ p` and a delay
`δ > 0`, the function `k * u (t - a + δ, x)`, with `u` the Hopf–Lax function of `f` for the cost
`‖w‖ ^ p`, is a subsolution for the Lagrangian `k ‖w‖ ^ p` near `[a, b]`. Testing the continuity
equation against it bounds its boundary terms by `k` times the `p`-action. -/
private theorem ofReal_integral_hopfLax_sub_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a ≤ b) {p k δ : ℝ} (hp : 1 ≤ p) (hk : 0 ≤ k) (hδ : 0 < δ) {f : E → ℝ}
    (hf : Bornology.IsBounded (range f)) :
    ENNReal.ofReal (∫ x, k * hopfLax (‖·‖ ^ p) f (b - a + δ) x ∂(ν b : Measure E) -
        ∫ x, k * hopfLax (‖·‖ ^ p) f δ x ∂(ν a : Measure E)) ≤
      ENNReal.ofReal k *
        ∫⁻ t in Ioo a b, ∫⁻ x, ENNReal.ofReal (‖v t x‖ ^ p) ∂(ν t : Measure E) := by
  obtain ⟨M, hM⟩ := exists_norm_mul_hopfLax_norm_rpow_le (p := p) (by linarith) hf hk
  -- The delayed Hopf–Lax function, defined on all of `ℝ × E` by freezing times below `a - δ / 2`.
  let u : ℝ × E → ℝ := fun q ↦ k * hopfLax (‖·‖ ^ p) f (max (q.1 - a + δ) (δ / 2)) q.2
  have hu : Continuous u := by
    refine continuous_const.mul ((continuousOn_hopfLax_norm_rpow hp hf).comp_continuous
      (f := fun q : ℝ × E ↦ (max (q.1 - a + δ) (δ / 2), q.2)) (by fun_prop) fun q ↦ ?_)
    exact lt_max_of_lt_right (half_pos hδ)
  have hub (x : E) : u (b, x) = k * hopfLax (‖·‖ ^ p) f (b - a + δ) x := by
    simp only [u, max_eq_left (show δ / 2 ≤ b - a + δ by linarith)]
  have hua (x : E) : u (a, x) = k * hopfLax (‖·‖ ^ p) f δ x := by
    simp only [u, sub_self, zero_add, max_eq_left (half_le_self hδ.le)]
  have key := h.ofReal_integral_sub_integral_le_lintegral_of_add_smul_le
    (L := fun w ↦ k * ‖w‖ ^ p) (M := M) hν hab hu.measurable (fun q ↦ ?_)
    (ae_of_all _ fun x ↦ hu.continuousAt.upperSemicontinuousAt)
    (ae_of_all _ fun x ↦ hu.continuousAt.lowerSemicontinuousAt) (half_pos hδ) (fun w ↦ ?_)
  · simp only [hub, hua] at key
    refine key.trans_eq ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp_rw [ENNReal.ofReal_mul hk]
  · exact hM _ (le_max_of_le_right (half_pos hδ).le) _
  · -- The subsolution inequality holds on the strip, where the delay keeps times positive.
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s) q hq
    have hτ : δ / 2 ≤ q.1 - a + δ := by linarith [hq.1]
    have hτs : δ / 2 ≤ q.1 + s - a + δ := by linarith
    simp only [u, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      max_eq_left hτ, max_eq_left hτs]
    have hsub := hopfLax_norm_rpow_add_add_smul_le hp hf.bddBelow
      (show 0 < q.1 - a + δ by linarith) hs.le q.2 w
    rw [show q.1 - a + δ + s = q.1 + s - a + δ by ring] at hsub
    linarith [mul_le_mul_of_nonneg_left hsub hk]

/-- **The Hopf–Lax test.** For a bounded initial datum `f` that is lower semicontinuous, `k ≥ 0`
and `1 < p`, the Hopf–Lax function `u` of `f` for the cost `‖w‖ ^ p`, run for the time `b - a`,
satisfies `∫ k u (b - a, ·) dν_b - ∫ k f dν_a ≤ k ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`. -/
private theorem ofReal_integral_hopfLax_sub_integral_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a < b) {p k : ℝ} (hp : 1 < p) (hk : 0 ≤ k) {f : E → ℝ}
    (hf : Bornology.IsBounded (range f)) (hfl : LowerSemicontinuous f) :
    ENNReal.ofReal (∫ x, k * hopfLax (‖·‖ ^ p) f (b - a) x ∂(ν b : Measure E) -
        ∫ x, k * f x ∂(ν a : Measure E)) ≤
      ENNReal.ofReal k *
        ∫⁻ t in Ioo a b, ∫⁻ x, ENNReal.ofReal (‖v t x‖ ^ p) ∂(ν t : Measure E) := by
  obtain ⟨M, hM⟩ := exists_norm_mul_hopfLax_norm_rpow_le (p := p) (by linarith) hf hk
  have hT : 0 < b - a := sub_pos.2 hab
  have hH := continuousOn_hopfLax_norm_rpow hp.le hf
  have hmeas {t : ℝ} (ht : 0 < t) : Measurable fun x ↦ k * hopfLax (‖·‖ ^ p) f t x :=
    (continuous_const.mul (continuous_hopfLax_norm_rpow hp.le hf ht)).measurable
  -- Let the delay `δₙ = 1 / (n + 1)` tend to `0`.
  let δ : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hδ0 (n : ℕ) : 0 < δ n := Nat.one_div_pos_of_nat
  have hδ : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall hδ0⟩
  -- At time `b`, the delayed Hopf–Lax functions converge by continuity at the time `b - a > 0`.
  have hconv (x : E) : Tendsto (fun n ↦ k * hopfLax (‖·‖ ^ p) f (b - a + δ n) x) atTop
      (𝓝 (k * hopfLax (‖·‖ ^ p) f (b - a) x)) := by
    have ht : Tendsto (fun n ↦ b - a + δ n) atTop (𝓝 (b - a)) := by
      simpa using (tendsto_nhdsWithin_iff.1 hδ).1.const_add (b - a)
    have hq : Tendsto (fun n ↦ ((b - a + δ n, x) : ℝ × E)) atTop (𝓝[{q | 0 < q.1}] (b - a, x)) :=
      tendsto_nhdsWithin_iff.2 ⟨ht.prodMk_nhds tendsto_const_nhds,
        .of_forall fun n ↦ show 0 < b - a + δ n by linarith [hδ0 n]⟩
    exact ((hH (b - a, x) hT).tendsto.comp hq).const_mul k
  have hlimb := tendsto_integral_of_dominated_convergence (μ := (ν b : Measure E))
    (fun _ ↦ M) (fun n ↦ (hmeas (by linarith [hδ0 n])).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ ae_of_all _ (hM _ (by linarith [hδ0 n]))) (ae_of_all _ hconv)
  -- At time `a`, they converge to the initial datum, which is lower semicontinuous.
  have hlima := tendsto_integral_of_dominated_convergence (μ := (ν a : Measure E))
    (fun _ ↦ M) (fun n ↦ (hmeas (hδ0 n)).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ ae_of_all _ (hM _ (hδ0 n).le))
    (ae_of_all _ fun x ↦ ((tendsto_hopfLax_norm_rpow_nhdsGT_zero hp hf.bddBelow
      (hfl x)).comp hδ).const_mul k)
  exact le_of_tendsto (ENNReal.tendsto_ofReal (hlimb.sub hlima))
    (.of_forall fun n ↦ h.ofReal_integral_hopfLax_sub_le hν hab.le hp.le hk (hδ0 n) hf)

/-- **The action bounds the Wasserstein distance.** Let `t ↦ νₜ` be a curve of finite measures on
a finite-dimensional real normed space, narrowly continuous on `[a, b]` with `a < b`, solving the
continuity equation with velocity `v` on `(a, b)`, and with `ν_a` a probability measure. Then for
`1 < p < ∞`,
`W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`. -/
theorem wassersteinEDist_rpow_le_mul_lintegral
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a < b) [IsProbabilityMeasure (ν a : Measure E)] {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    wassersteinEDist p (ν a : Measure E) (ν b) ^ p.toReal ≤
      ENNReal.ofReal ((b - a) ^ (p.toReal - 1)) *
        ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) := by
  have hr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have : IsProbabilityMeasure (ν b : Measure E) := ⟨by
    rw [h.measure_univ_eq hν (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le), measure_univ]⟩
  have hT : 0 < b - a := sub_pos.2 hab
  set k := (b - a) ^ (p.toReal - 1) with hk_def
  have hk : 0 < k := Real.rpow_pos_of_pos hT _
  have hpow (w : E) : ‖w‖ₑ ^ p.toReal = ENNReal.ofReal (‖w‖ ^ p.toReal) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
  simp_rw [hpow]
  rw [wassersteinEDist_rpow_eq_transportCost measurable_edist (zero_lt_one.trans hp).ne' hp_top]
  refine (isLUB_ofReal_kantorovichDualValue_upperSemicontinuous_of_lowerSemicontinuous
    (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous).2 ?_
  rintro _ ⟨φ, ψ, hφ, hψ, hφb, hψb, hfeas, rfl⟩
  have hfeas' (x y : E) : φ x + ψ y ≤ ‖x - y‖ ^ p.toReal := by
    have := dualFeasible_iff_ofReal_add_le.1 hfeas x y
    rwa [Function.comp_apply, edist_dist, dist_eq_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  -- The Hopf–Lax test with initial datum `-φ / k`.
  let f : E → ℝ := fun x ↦ -φ x / k
  have hf : Bornology.IsBounded (range f) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hφb
    refine isBounded_iff_forall_norm_le.2 ⟨C / k, forall_mem_range.2 fun x ↦ ?_⟩
    rw [norm_div, norm_neg, Real.norm_of_nonneg hk.le]
    exact div_le_div_of_nonneg_right (hC _ ⟨x, rfl⟩) hk.le
  have hkf (x : E) : k * f x = -φ x := by simp only [f]; field_simp
  have htest := h.ofReal_integral_hopfLax_sub_integral_le hν hab hr hk.le hf
    ((continuous_neg.div_const k).comp_upperSemicontinuous_antitone hφ
      fun _ _ hst ↦ div_le_div_of_nonneg_right (neg_le_neg hst) hk.le)
  simp only [hkf] at htest
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) htest
  -- At time `b - a` the Hopf–Lax function dominates `ψ`, by dual feasibility.
  have hψle (y : E) : ψ y ≤ k * hopfLax (‖·‖ ^ p.toReal) f (b - a) y := by
    rw [hopfLax_norm_rpow f hT, Real.mul_iInf_of_nonneg hk.le]
    refine le_ciInf fun x ↦ ?_
    rw [mul_add, hkf, ← hk_def, mul_div_cancel₀ _ hk.ne', norm_sub_rev]
    linarith [hfeas' x y]
  obtain ⟨M, hM⟩ := exists_norm_mul_hopfLax_norm_rpow_le (p := p.toReal) (by linarith) hf hk.le
  have hHint : Integrable (fun y ↦ k * hopfLax (‖·‖ ^ p.toReal) f (b - a) y) (ν b : Measure E) :=
    .of_bound (C := M) (continuous_const.mul
      (continuous_hopfLax_norm_rpow hr.le hf hT)).aestronglyMeasurable
      (ae_of_all _ (hM _ hT.le))
  have hint := integral_mono
    (MeasureTheory.integrable_of_isBounded_range hψ.measurable.aestronglyMeasurable hψb) hHint hψle
  rw [kantorovichDualValue_def, integral_neg]
  linarith

/-- **The lower bound in the Benamou–Brenier formula.** Let `t ↦ νₜ` be a curve of finite measures
on a finite-dimensional real normed space, narrowly continuous on `[0, 1]`, solving the continuity
equation with velocity `v` on `(0, 1)`, and with `ν₀` a probability measure. Then for `1 < p < ∞`,
`W_p (ν₀, ν₁) ^ p ≤ ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`. -/
theorem wassersteinEDist_rpow_le_lintegral
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1) (hν : ContinuousOn ν (Icc 0 1))
    [IsProbabilityMeasure (ν 0 : Measure E)] {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    wassersteinEDist p (ν 0 : Measure E) (ν 1) ^ p.toReal ≤
      ∫⁻ t in Ioo 0 1, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) := by
  simpa using h.wassersteinEDist_rpow_le_mul_lintegral hν zero_lt_one hp hp_top

end IsContinuityEquation

/-- **The Benamou–Brenier formula.** Let `μ` and `μ'` be probability measures on a
finite-dimensional real normed space at finite Wasserstein distance `W_p (μ, μ')`, with
`1 < p < ∞`. Then `W_p (μ, μ') ^ p` is the least `p`-action `∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt` of a curve of
finite measures `t ↦ νₜ`, narrowly continuous on `[0, 1]`, from `ν₀ = μ` to `ν₁ = μ'`, solving the
continuity equation with velocity `v` on `(0, 1)`. The minimum is attained by the displacement
interpolation of an optimal coupling. -/
theorem isLeast_wassersteinEDist_rpow_lintegral {μ μ' : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hfin : wassersteinEDist p μ μ' ≠ ∞) :
    IsLeast {A | ∃ (ν : ℝ → FiniteMeasure E) (v : ℝ → E → E),
        IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 ∧ ContinuousOn ν (Icc 0 1) ∧
        (ν 0 : Measure E) = μ ∧ (ν 1 : Measure E) = μ' ∧
        ∫⁻ t in Ioo 0 1, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) = A}
      (wassersteinEDist p μ μ' ^ p.toReal) := by
  refine ⟨?_, ?_⟩
  · -- The displacement interpolation of an optimal coupling attains the bound.
    obtain ⟨π, hπ⟩ := exists_isOptimalCoupling (c := fun z : E × E ↦ edist z.1 z.2 ^ p.toReal) μ μ'
      (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous
    obtain ⟨v, hce, hact⟩ :=
      exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le hp.le hp_top
        hπ hfin
    have : IsProbabilityMeasure π := hπ.toIsCoupling.isProbabilityMeasure
    let P : FiniteMeasure (E × E) := ⟨π, inferInstance⟩
    let ν : ℝ → FiniteMeasure E := fun t ↦ P.map fun z ↦ (1 - t) • z.1 + t • z.2
    have hν (t : ℝ) : (ν t : Measure E) = π.map fun z ↦ (1 - t) • z.1 + t • z.2 := rfl
    have hνc : Continuous ν := P.continuous_map_smul_fst_add_smul_snd
    have h0 : (ν 0 : Measure E) = μ := by
      simpa [hν, Measure.fst] using hπ.toIsCoupling.fst_eq
    have h1 : (ν 1 : Measure E) = μ' := by
      simpa [hν, Measure.snd] using hπ.toIsCoupling.snd_eq
    have hce' : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 := by
      simpa only [hν] using hce
    refine ⟨ν, v, hce', hνc.continuousOn, h0, h1, le_antisymm hact ?_⟩
    have : IsProbabilityMeasure (ν 0 : Measure E) := h0 ▸ inferInstance
    simpa only [h0, h1] using hce'.wassersteinEDist_rpow_le_lintegral hνc.continuousOn hp hp_top
  · -- Every competitor has at least this action.
    rintro _ ⟨ν, v, hce, hν, rfl, rfl, rfl⟩
    exact hce.wassersteinEDist_rpow_le_lintegral hν hp hp_top

end TauCeti
