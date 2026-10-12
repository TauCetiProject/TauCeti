/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.PointSampling
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Rounding

/-!
# The second sampling lemma

The `W`-random graph `G(n, W)` converges to `W` in cut distance in probability:

`P(ε ≤ δ□(G(n, W), W)) → 0` as `n → ∞`, for every `ε > 0`,

where `G(n, W)` is read as a graphon on the unit interval through `finiteGraphGraphon`. The
carrier of `W` is an arbitrary probability space.

The statement is about the finite sampling laws `sampleGraph W n` alone. It is proved through the
padded exposure of `G(n, W)` (`TauCeti.DenseGraphLimits.map_exposedSample`), whose first
coordinates are the sample points `y`, by passing through the weighted graph `H(y, W)`, the
pullback of `W` to the uniform carrier on `Fin n`:

* the edge coins move `G(n, W)` only a little away from `H(y, W)`
  (`TauCeti.DenseGraphLimits.exposedSample_cutDist_comap_concentration`, a union bound over cuts
  whose tail `2 · 4ⁿ · exp (-(εn/2 - 1)² / 2)` vanishes);
* `H(y, W)` converges to `W` in probability
  (`TauCeti.DenseGraphLimits.cutDist_comap_tendsto_inProbability`).

## Main result

* `TauCeti.DenseGraphLimits.sampleGraph_cutDist_tendsto_inProbability` — the second sampling lemma
  in probability.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Lemma 10.16.
* C. Borgs, J. Chayes, L. Lovász, V. Sós, K. Vesztergombi, *Convergent sequences of dense graphs
  I: Subgraph frequencies, metric properties and testing*, Adv. Math. 219 (2008), 1801–1851.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The tail of the rounding estimate vanishes: `2 · 4ⁿ · exp (-(an - 1)² / 2) → 0` for `a > 0`,
since the quadratic exponent beats the linear one. -/
private theorem tendsto_two_mul_four_pow_mul_exp {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => 2 * 4 ^ n * Real.exp (-(a * n - 1) ^ 2 / 2)) atTop (𝓝 0) := by
  have hexp : ∀ n : ℕ, 2 * 4 ^ n * Real.exp (-(a * n - 1) ^ 2 / 2) =
      2 * Real.exp (n * (Real.log 4 + a - a ^ 2 / 2 * n) + -(1 / 2)) := fun n => by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul, mul_assoc,
      ← Real.exp_add, Real.log_exp]
    ring_nf
  simp_rw [hexp]
  have hlin : Tendsto (fun n : ℕ => Real.log 4 + a - a ^ 2 / 2 * n) atTop atBot := by
    have h := tendsto_atBot_add_const_left atTop (Real.log 4 + a)
      (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < a ^ 2 / 2)))
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    ring
  have hexpo := tendsto_atBot_add_const_right atTop (-(1 / 2))
    (tendsto_natCast_atTop_atTop.atTop_mul_atBot₀ hlin)
  simpa using (Real.tendsto_exp_atBot.comp hexpo).const_mul 2

/-- **The two-stage estimate.** Once `1 ≤ εn / 2`, the sampled graph `G(n, W)` is at cut distance
at least `ε` from `W` only if the edge coins move it by `ε / 2` from the weighted graph `H(y, W)`
of its sample points, or `H(y, W)` is at cut distance at least `ε / 2` from `W`. -/
private theorem measureReal_le_cutDist_sampleGraph_le {n : ℕ} [NeZero n] (W : Graphon Ω μ)
    {ε : ℝ} (hε : 1 ≤ ε / 2 * n) :
    (sampleGraph W n).real {G | ε ≤ cutDist (finiteGraphGraphon G) W} ≤
      2 * 4 ^ n * Real.exp (-(ε / 2 * n - 1) ^ 2 / 2) +
        (Measure.pi fun _ : Fin n => μ).real
          {y | ε / 2 ≤ cutDist (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) W} := by
  rw [← map_exposedSample W n,
    map_measureReal_apply (measurable_exposedSample W) MeasurableSet.of_discrete]
  have hincl : exposedSample W ⁻¹' {G | ε ≤ cutDist (finiteGraphGraphon G) W} ⊆
      {x | ε / 2 ≤ cutDist (finiteGraphGraphon (exposedSample W x))
        (W.comap (fun i => (x i).1) (measurable_of_finite _) (uniformOn Set.univ))} ∪
      (fun x i => (x i).1) ⁻¹'
        {y : Fin n → Ω |
          ε / 2 ≤ cutDist (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) W} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_le] at hx hnot
    have := cutDist_triangle (finiteGraphGraphon (exposedSample W x))
      (W.comap (fun i => (x i).1) (measurable_of_finite _) (uniformOn Set.univ)) W
    linarith
  have hpos : Measurable fun (x : Fin n → Ω × (Fin n → ℝ)) (i : Fin n) => (x i).1 :=
    measurable_pi_iff.2 fun i => measurable_fst.comp (measurable_pi_apply i)
  refine (measureReal_mono hincl).trans ((measureReal_union_le _ _).trans
    (add_le_add (exposedSample_cutDist_comap_concentration W hε) ?_))
  rw [measureReal_def, measureReal_def, ← map_fst_exposureMeasure μ n]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hpos.aemeasurable _)

/-- **The second sampling lemma, in probability.** The `W`-random graph `G(n, W)`, read as a graphon
on the unit interval, is at cut distance at least `ε` from `W` with probability tending to zero as
`n → ∞`, for every `ε > 0`. The carrier of `W` is an arbitrary probability space. -/
theorem sampleGraph_cutDist_tendsto_inProbability (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleGraph W n).real {G | ε ≤ cutDist (finiteGraphGraphon G) W})
      atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hround := (tendsto_add_atTop_iff_nat 1).2
    (tendsto_two_mul_four_pow_mul_exp (half_pos hε))
  have hpoint := cutDist_comap_tendsto_inProbability W (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hround.add hpoint) (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop ⌈2 / ε⌉₊] with n hn
  have hn' : 2 / ε ≤ ((n + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn.trans (Nat.le_succ n))
  have h1 : 1 ≤ ε / 2 * ((n + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hε] at hn'
    linarith
  exact_mod_cast measureReal_le_cutDist_sampleGraph_le W h1

end DenseGraphLimits

end TauCeti
