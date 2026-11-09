/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Strong continuity of coordinatewise operators on `lp`

A uniformly bounded family of coordinatewise operators is strongly continuous on `lp`, for
finite exponent, whenever it is strongly continuous on each coordinate. Finite coordinate
truncations approximate each orbit uniformly. This allows strongly continuous representations
to be assembled on infinite direct sums, without countability assumptions on the index set.

The operator itself is Mathlib's `lp.mapCLM`.
-/

public section

open Filter Topology
open scoped ENNReal

namespace lp

variable {ι 𝕜 X : Type*} {E F : ι → Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A uniformly bounded coordinatewise operator family is strongly continuous on `lp` at finite
exponent if each coordinate family is strongly continuous. -/
theorem continuous_mapCLM_apply (hp : p ≠ ∞) (T : X → ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hT : ∀ t i, ‖T t i‖ ≤ K)
    (hcont : ∀ i v, Continuous fun t => T t i v) (x : lp E p) :
    Continuous fun t => mapCLM p (T t) hK (hT t) x := by
  classical
  let S (s : Finset ι) (t : X) := ∑ i ∈ s, lp.single p i (T t i (x i))
  have hS (s : Finset ι) : Continuous (S s) :=
    continuous_finsetSum s fun i _ =>
      (singleContinuousLinearMap 𝕜 F p i).continuous.comp (hcont i (x i))
  have happrox : TendstoUniformly S (fun t => mapCLM p (T t) hK (hT t) x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hx := lp.hasSum_single hp x
    have hdist := (tendsto_iff_dist_tendsto_zero.mp hx).mul_const K
    have hevent := (tendsto_order.mp hdist).2 ε (by simpa using hε)
    filter_upwards [hevent] with s hs t
    have heq : S s t = mapCLM p (T t) hK (hT t) (∑ i ∈ s, lp.single p i (x i)) := by
      simp only [S, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      ext j
      by_cases h : j = i
      · subst j; simp
      · simp [lp.single_apply, h]
    rw [heq]
    calc
      dist (mapCLM p (T t) hK (hT t) x)
          (mapCLM p (T t) hK (hT t) (∑ i ∈ s, lp.single p i (x i)))
          ≤ K * dist x (∑ i ∈ s, lp.single p i (x i)) := by
        simpa only [dist_eq_norm, ← map_sub] using
          (mapCLM p (T t) hK (hT t)).le_of_opNorm_le (norm_mapCLM_le _ _ _ _) _
      _ < ε := by simpa only [dist_comm, mul_comm] using hs
  exact happrox.continuous (Eventually.of_forall hS).frequently

end lp
