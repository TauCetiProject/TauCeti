/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.PlanInterpolation
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Subsolution
import TauCeti.Analysis.PDE.HopfLax
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# The Benamou–Brenier formula

Let `E` be a finite-dimensional real normed space and `1 ≤ p < ∞`. The *Benamou–Brenier formula*
identifies the `p`-th power of the Wasserstein distance between two probability measures `μ₀`
and `μ₁` on `E` with the infimal kinetic action needed to move `μ₀` to `μ₁`:

`W_p (μ₀, μ₁) ^ p = inf ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`,

the infimum being over the curves `t ↦ νₜ` of finite measures, narrowly continuous on `[0, 1]`
with `ν₀ = μ₀` and `ν₁ = μ₁`, that solve the continuity equation `∂ₜ νₜ + div (vₜ νₜ) = 0` on
`(0, 1)` with velocity `v`. Both sides may be `∞`; when `W_p (μ₀, μ₁)` is finite, the infimum is
attained, so it is a minimum. It is the Eulerian description of optimal transport: the static
problem over couplings becomes a dynamic problem over flows of mass.

The upper bound and the minimiser come from the displacement interpolation of an optimal
coupling, whose barycentric velocity has action at most `W_p (μ₀, μ₁) ^ p`
(`TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le`).

The lower bound holds on every interval `[a, b]`:
`W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) * ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`. By Kantorovich duality with
bounded continuous potentials, it suffices to bound `∫ φ dν_a + ∫ ψ dν_b` for a feasible pair
`φ x + ψ y ≤ ‖x - y‖ ^ p`. The Hopf–Lax formula with Lagrangian `‖·‖ ^ p` propagates `-φ` to a
function `u (t, x)` with `u (a, ·) ≤ -φ` and `u (b, ·) ≥ ψ` (up to the factor
`(b - a) ^ (p - 1)`), which is a subsolution of the Hamilton–Jacobi equation
`∂ₜ u + ⟨∇ₓ u, w⟩ ≤ ‖w‖ ^ p`; testing the continuity equation against `u` bounds
`∫ u (b, ·) dν_b - ∫ u (a, ·) dν_a` by the action
(`TauCeti.IsContinuityEquation.ofReal_integral_sub_integral_le_lintegral_of_add_smul_le`). To make
`u` continuous up to the time `a`, the Hopf–Lax evolution is started slightly before `a`, and the
endpoint is recovered by narrow continuity of `ν` at `b`.

## Main results

* `TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le`: the Benamou–Brenier lower bound
  `W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) * ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt` for a narrowly continuous
  solution of the continuity equation.
* `TauCeti.isLeast_lintegral_isContinuityEquation`: **the Benamou–Brenier formula** at finite
  Wasserstein distance, with the minimum attained.
* `TauCeti.wassersteinEDist_rpow_eq_sInf_lintegral_isContinuityEquation`: the formula as an
  infimum, with both sides possibly infinite.

## References

* J.-D. Benamou and Y. Brenier, *A computational fluid mechanics solution to the
  Monge–Kantorovich mass transfer problem*, Numer. Math. 84 (2000), 375--393.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1 and §8.3.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 7.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ν : ℝ → FiniteMeasure E} {v : ℝ → E → E} {a b : ℝ}

namespace IsContinuityEquation

/-- Testing the continuity equation against a Hopf–Lax evolution. Let `g` be a continuous
function with `|g| ≤ C` and `H s x` its Hopf–Lax value for the Lagrangian `‖·‖ ^ p`. For
`0 < δ < b - a`, the function `(t, x) ↦ H (t - a + δ) x`, started at time `a - δ`, is a bounded
continuous subsolution on a strip around `[a, b - δ]`, so the action of a narrowly continuous
solution of the continuity equation on `(a, b)` bounds
`∫ H (b - a) dν_(b - δ) - ∫ H δ dν_a`. -/
private theorem ofReal_integral_hopfLax_sub_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ} (hg : Continuous g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) {δ : ℝ}
    (hδ : 0 < δ) (hδT : δ < b - a) :
    ENNReal.ofReal (∫ x, hopfLax (‖·‖ ^ p) g (b - a) x ∂(ν (b - δ) : Measure E) -
        ∫ x, hopfLax (‖·‖ ^ p) g δ x ∂(ν a : Measure E)) ≤
      ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p ∂(ν t : Measure E) := by
  set H : ℝ → E → ℝ := hopfLax (‖·‖ ^ p) g
  have hgb : BddBelow (range g) := ⟨-C, forall_mem_range.2 fun x ↦ (abs_le.1 (hgC x)).1⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set U : ℝ × E → ℝ := fun q ↦ H (max (q.1 - a + δ) (δ / 2)) q.2
  have hUc : Continuous U :=
    (continuousOn_hopfLax_norm_rpow hp hg hgb).comp_continuous
      (f := fun q : ℝ × E ↦ (max (q.1 - a + δ) (δ / 2), q.2)) (by fun_prop)
      fun q ↦ lt_max_of_lt_right (half_pos hδ)
  have hUC (q : ℝ × E) : ‖U q‖ ≤ C :=
    (Real.norm_eq_abs _).trans_le
      (abs_hopfLax_norm_rpow_le hp0 hgC (le_max_of_le_right (half_pos hδ).le) _)
  have hU := ofReal_integral_sub_integral_le_lintegral_of_add_smul_le
    (h.mono le_rfl (by linarith : b - δ ≤ b)) (hν.mono (Icc_subset_Icc_right (by linarith)))
    (by linarith : a ≤ b - δ) hUc.measurable hUC
    (ae_of_all _ fun x ↦ hUc.continuousAt.upperSemicontinuousAt)
    (ae_of_all _ fun x ↦ hUc.continuousAt.lowerSemicontinuousAt) (half_pos hδ)
    (L := (‖·‖ ^ p)) fun w ↦ by
      -- On the strip the time `t - a + δ` exceeds `δ / 2`, so the subsolution inequality applies.
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s) q hq
      have h1 : max (q.1 - a + δ) (δ / 2) = q.1 - a + δ := max_eq_left (by linarith [hq.1])
      have h2 : max (q.1 + s * 1 - a + δ) (δ / 2) = q.1 - a + δ + s :=
        (max_eq_left (by linarith [hq.1])).trans (by ring)
      simp only [U, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, h1, h2]
      exact hopfLax_norm_rpow_add_add_smul_le hp hgb (by linarith [hq.1]) hs.le q.2 w
  have hb : b - δ - a + δ = b - a := by ring
  simp only [U, hb, max_eq_left (by linarith : δ / 2 ≤ b - a), sub_self, zero_add,
    max_eq_left (half_le_self hδ.le)] at hU
  refine hU.trans
    ((lintegral_mono_set (Ioo_subset_Ioo_right (by linarith : b - δ ≤ b))).trans_eq ?_)
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hp), ofReal_norm]

/-- The dual step of the Benamou–Brenier lower bound: a pair of bounded continuous potentials
feasible for the cost `‖x - y‖ ^ p` has dual value at most `(b - a) ^ (p - 1)` times the
`p`-action of a narrowly continuous solution of the continuity equation on `(a, b)`. The Hopf–Lax
evolution of `-φ / (b - a) ^ (p - 1)` lies below it at time `0` and above
`ψ / (b - a) ^ (p - 1)` at time `b - a`; it is started slightly before `a`, and the endpoint `b`
is recovered by narrow continuity. -/
private theorem ofReal_kantorovichDualValue_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a < b) {p : ℝ} (hp : 1 ≤ p) (φ ψ : E →ᵇ ℝ) (hφψ : ∀ x y, φ x + ψ y ≤ ‖x - y‖ ^ p) :
    ENNReal.ofReal (kantorovichDualValue (ν a : Measure E) (ν b) φ ψ) ≤
      ENNReal.ofReal ((b - a) ^ (p - 1)) *
        ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p ∂(ν t : Measure E) := by
  have hT : 0 < b - a := sub_pos.2 hab
  set κ := (b - a) ^ (p - 1)
  have hκ : 0 < κ := Real.rpow_pos_of_pos hT _
  set g : E → ℝ := fun x ↦ -φ x / κ
  have hgC (x : E) : |g x| ≤ ‖φ‖ / κ := by
    simpa [g, abs_div, abs_of_pos hκ] using div_le_div_of_nonneg_right (φ.norm_coe_le_norm x)
      hκ.le
  have hgb : BddBelow (range g) := ⟨-(‖φ‖ / κ), forall_mem_range.2 fun x ↦ (abs_le.1 (hgC x)).1⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  -- At time `0` the Hopf–Lax value lies below `g`, at time `T` above `ψ / κ`.
  have hHle {s : ℝ} (hs : 0 ≤ s) (x : E) : hopfLax (‖·‖ ^ p) g s x ≤ g x := by
    simpa [Real.zero_rpow hp0] using hopfLax_le_add_mul hgb
      ⟨0, forall_mem_range.2 fun w ↦ Real.rpow_nonneg (norm_nonneg w) p⟩ hs x
  have hHT (y : E) : ψ y / κ ≤ hopfLax (‖·‖ ^ p) g (b - a) y := by
    rw [hopfLax_norm_rpow g hT]
    refine le_ciInf fun x ↦ ?_
    calc ψ y / κ = (-φ x + (φ x + ψ y)) / κ := by ring
      _ ≤ (-φ x + ‖y - x‖ ^ p) / κ := by
          gcongr
          rw [norm_sub_rev]
          exact hφψ x y
      _ = g x + ‖y - x‖ ^ p / (b - a) ^ (p - 1) := by simp only [g, κ]; ring
  have hHi (t s : ℝ) (hs : 0 < s) :
      Integrable (fun x ↦ hopfLax (‖·‖ ^ p) g s x) (ν t : Measure E) :=
    .of_bound (((continuousOn_hopfLax_norm_rpow hp (by fun_prop) hgb).comp_continuous
      (f := fun x : E ↦ (s, x)) (by fun_prop) fun _ ↦ hs).aestronglyMeasurable) (‖φ‖ / κ)
      (ae_of_all _ fun x ↦ (abs_hopfLax_norm_rpow_le hp0 hgC hs.le x))
  -- For `0 < δ < T`, the dual value with `ν (b - δ)` in place of `ν b` is bounded by the action.
  have hstep {δ : ℝ} (hδ : 0 < δ) (hδT : δ < b - a) :
      ENNReal.ofReal ((∫ y, ψ y ∂(ν (b - δ) : Measure E) + ∫ x, φ x ∂(ν a : Measure E)) / κ) ≤
        ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p ∂(ν t : Measure E) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (ofReal_integral_hopfLax_sub_le h hν hp (by fun_prop) hgC hδ hδT)
    have hψ := integral_mono ((ψ.integrable _).div_const κ) (hHi (b - δ) (b - a) hT) hHT
    have hgi : Integrable g (ν a : Measure E) := (φ.integrable _).neg.div_const κ
    have hφ := integral_mono (hHi a δ hδ) hgi (hHle hδ.le)
    have hg : ∫ x, g x ∂(ν a : Measure E) = -((∫ x, φ x ∂(ν a : Measure E)) / κ) := by
      simp only [g, integral_div, integral_neg, neg_div]
    rw [integral_div] at hψ
    rw [hg] at hφ
    rw [add_div]
    linarith
  -- Letting `δ → 0`, narrow continuity of `ν` at `b` recovers the dual value.
  have hb' : Tendsto (fun δ : ℝ ↦ b - δ) (𝓝[>] 0) (𝓝[Icc a b] b) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun δ : ℝ ↦ b - δ) (𝓝 0) (𝓝 (b - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hT] with δ hδ using ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
  have hψlim := FiniteMeasure.tendsto_iff_forall_integral_tendsto.1
    ((hν b (right_mem_Icc.2 hab.le)).tendsto.comp hb') ψ
  have hle := le_of_tendsto (ENNReal.tendsto_ofReal ((hψlim.add_const _).div_const κ))
    (by filter_upwards [Ioo_mem_nhdsGT hT] with δ hδ using hstep hδ.1 hδ.2)
  rw [kantorovichDualValue_def]
  calc ENNReal.ofReal (∫ x, φ x ∂(ν a : Measure E) + ∫ y, ψ y ∂(ν b : Measure E))
      = ENNReal.ofReal κ *
          ENNReal.ofReal ((∫ y, ψ y ∂(ν b : Measure E) + ∫ x, φ x ∂(ν a : Measure E)) / κ) := by
        rw [← ENNReal.ofReal_mul hκ.le, mul_div_cancel₀ _ hκ.ne', add_comm]
    _ ≤ _ := by gcongr

/-- **The Benamou–Brenier lower bound.** Let `t ↦ νₜ` be a curve of finite measures, narrowly
continuous on `[a, b]` with `a < b`, solving the continuity equation with velocity `v` on
`(a, b)`, whose endpoint laws `ν_a` and `ν_b` are probability measures. Then for `1 ≤ p < ∞` the
`p`-Wasserstein distance between the endpoint laws is controlled by the `p`-action of `v`:
`W_p (ν_a, ν_b) ^ p ≤ (b - a) ^ (p - 1) * ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt`.

On `[0, 1]` the factor is `1`, and this is the inequality `W_p (ν₀, ν₁) ^ p ≤ ∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt`
of the Benamou–Brenier formula. -/
theorem wassersteinEDist_rpow_le (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b)
    (hν : ContinuousOn ν (Icc a b)) (hab : a < b) [IsProbabilityMeasure (ν a : Measure E)]
    [IsProbabilityMeasure (ν b : Measure E)] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    wassersteinEDist p (ν a : Measure E) (ν b) ^ p.toReal ≤
      ENNReal.ofReal ((b - a) ^ (p.toReal - 1)) *
        ∫⁻ t in Ioo a b, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp₁ : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  rw [wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp_top]
  refine (isLUB_ofReal_kantorovichDualValue_boundedContinuous_of_lowerSemicontinuous
    (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous
    (c := fun z : E × E ↦ edist z.1 z.2 ^ p.toReal)).2 ?_
  rintro r ⟨φ, ψ, hfeas, rfl⟩
  refine ofReal_kantorovichDualValue_le h hν hab hp₁ φ ψ fun x y ↦ ?_
  have hxy := hfeas.ofReal_add_le x y
  rwa [edist_eq_enorm_sub, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hp₁),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hxy

end IsContinuityEquation

/-- **The Benamou–Brenier formula.** For `1 ≤ p < ∞` and probability measures `μ₀`, `μ₁` on a
finite-dimensional real normed space at finite Wasserstein distance, `W_p (μ₀, μ₁) ^ p` is the
least `p`-action `∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt` of a curve `t ↦ νₜ` of finite measures, narrowly
continuous on `[0, 1]` and joining `μ₀` to `μ₁`, solving the continuity equation with velocity `v`
on `(0, 1)`. The minimum is attained by the displacement interpolation of an optimal coupling. -/
theorem isLeast_lintegral_isContinuityEquation {μ₀ μ₁ : Measure E} [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hfin : wassersteinEDist p μ₀ μ₁ ≠ ∞) :
    IsLeast {A | ∃ (ν : ℝ → FiniteMeasure E) (v : ℝ → E → E),
        IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 ∧ ContinuousOn ν (Icc 0 1) ∧
          (ν 0 : Measure E) = μ₀ ∧ (ν 1 : Measure E) = μ₁ ∧
          ∫⁻ t in Ioo 0 1, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) = A}
      (wassersteinEDist p μ₀ μ₁ ^ p.toReal) := by
  have hlow : wassersteinEDist p μ₀ μ₁ ^ p.toReal ∈ lowerBounds {A | ∃ (ν : ℝ → FiniteMeasure E)
      (v : ℝ → E → E), IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 ∧
        ContinuousOn ν (Icc 0 1) ∧ (ν 0 : Measure E) = μ₀ ∧ (ν 1 : Measure E) = μ₁ ∧
        ∫⁻ t in Ioo 0 1, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) = A} := by
    rintro A ⟨ν, v, hce, hν, rfl, rfl, rfl⟩
    simpa using hce.wassersteinEDist_rpow_le hν zero_lt_one hp hp_top
  refine ⟨?_, hlow⟩
  -- The displacement interpolation of an optimal coupling attains the bound.
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ₀ μ₁
    (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous
    (c := fun z : E × E ↦ edist z.1 z.2 ^ p.toReal)
  obtain ⟨v, hce, hact⟩ :=
    exists_isContinuityEquation_map_smul_fst_add_smul_snd_of_isOptimalCoupling_le hp hp_top hπ hfin
  have : IsProbabilityMeasure π := hπ.toIsCoupling.isProbabilityMeasure
  let P : ProbabilityMeasure (E × E) := ⟨π, inferInstance⟩
  let ν : ℝ → FiniteMeasure E := fun t ↦
    (P.map fun z ↦ (1 - t) • z.1 + t • z.2).toFiniteMeasure
  have hν (t : ℝ) : (ν t : Measure E) = π.map fun z ↦ (1 - t) • z.1 + t • z.2 := by
    rw [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
  have hνc : Continuous ν := ProbabilityMeasure.toFiniteMeasure_continuous.comp
    (P.continuous_map_of_forall_continuous (fun _ ↦ by fun_prop) fun _ ↦ by fun_prop)
  have h0 : (ν 0 : Measure E) = μ₀ := by
    rw [hν, ← hπ.toIsCoupling.fst_eq, Measure.fst]
    simp
  have h1 : (ν 1 : Measure E) = μ₁ := by
    rw [hν, ← hπ.toIsCoupling.snd_eq, Measure.snd]
    simp
  have hce' : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 := by
    simpa only [hν] using hce
  refine ⟨ν, v, hce', hνc.continuousOn, h0, h1, le_antisymm ?_
    (hlow ⟨ν, v, hce', hνc.continuousOn, h0, h1, rfl⟩)⟩
  simpa only [hν] using hact

/-- **The Benamou–Brenier formula, as an infimum.** For `1 ≤ p < ∞` and probability measures `μ₀`,
`μ₁` on a finite-dimensional real normed space, `W_p (μ₀, μ₁) ^ p` is the infimum of the
`p`-actions `∫₀¹ ∫ ‖vₜ‖ ^ p dνₜ dt` of the curves `t ↦ νₜ` of finite measures, narrowly continuous
on `[0, 1]` and joining `μ₀` to `μ₁`, solving the continuity equation with velocity `v` on
`(0, 1)`. Both sides may be infinite. -/
theorem wassersteinEDist_rpow_eq_sInf_lintegral_isContinuityEquation {μ₀ μ₁ : Measure E}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    wassersteinEDist p μ₀ μ₁ ^ p.toReal = sInf {A | ∃ (ν : ℝ → FiniteMeasure E) (v : ℝ → E → E),
        IsContinuityEquation (fun t ↦ (ν t : Measure E)) v 0 1 ∧ ContinuousOn ν (Icc 0 1) ∧
          (ν 0 : Measure E) = μ₀ ∧ (ν 1 : Measure E) = μ₁ ∧
          ∫⁻ t in Ioo 0 1, ∫⁻ x, ‖v t x‖ₑ ^ p.toReal ∂(ν t : Measure E) = A} := by
  by_cases hfin : wassersteinEDist p μ₀ μ₁ = ∞
  · refine le_antisymm (le_sInf ?_) ?_
    · rintro A ⟨ν, v, hce, hν, rfl, rfl, rfl⟩
      simpa using hce.wassersteinEDist_rpow_le hν zero_lt_one hp hp_top
    · rw [hfin, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top)]
      exact le_top
  · exact (isLeast_lintegral_isContinuityEquation hp hp_top hfin).csInf_eq.symm

end TauCeti
