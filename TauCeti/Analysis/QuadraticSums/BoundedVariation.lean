/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded variation and quadratic increment sums

Mixed increment sums of a uniformly continuous path and a bounded-variation path tend to
zero on grids of vanishing mesh. In particular, adding a continuous bounded-variation real
path does not change the limit of squared-increment sums. These pathwise estimates separate
the finite-variation terms from the quadratic terms in change-of-variables formulas.

The grids may have repeated points or no intervals, and need not be nested or share endpoints.
The metric-valued estimate uses only uniform continuity of one path, not continuity of the
bounded-variation path. On a compact interval, continuous paths are uniformly continuous.
The real quadratic-sum comparison requires both paths to be uniformly continuous.

The variation bound is Mathlib's `eVariationOn.sum_le_of_monotoneOn_Iic`, converted to real
values only after finiteness has been established.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Filter Set
open scoped Topology

namespace BoundedVariationOn

variable {α E F : Type*} [LinearOrder α] [PseudoMetricSpace E] [PseudoMetricSpace F]
  {f : α → E} {g : α → F} {s : Set α}

/-- If every increment of `f` has size at most `ε`, the sum of the products of increment
sizes is at most `ε` times the total variation of `g`. -/
theorem sum_dist_mul_dist_le (hg : BoundedVariationOn g s) {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (hus : ∀ i ≤ n, u i ∈ s) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ i < n, dist (f (u (i + 1))) (f (u i)) ≤ ε) :
    ∑ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i)) *
      dist (g (u (i + 1))) (g (u i)) ≤ ε * (eVariationOn g s).toReal := by
  have hvar := ENNReal.toReal_mono hg
    (eVariationOn.sum_le_of_monotoneOn_Iic (f := g) hu hus)
  rw [ENNReal.toReal_sum (fun _ _ ↦ edist_ne_top _ _)] at hvar
  simp only [← dist_edist] at hvar
  calc
    _ ≤ ∑ i ∈ Finset.range n, ε * dist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_right (hf i (Finset.mem_range.mp hi)) dist_nonneg
    _ = ε * ∑ i ∈ Finset.range n, dist (g (u (i + 1))) (g (u i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hvar hε

end BoundedVariationOn

namespace UniformContinuousOn

variable {α E F ι : Type*} [LinearOrder α] [PseudoMetricSpace α]
  [PseudoMetricSpace E] [PseudoMetricSpace F]
  {f : α → E} {g : α → F} {s : Set α} {l : Filter ι}
  {n : ι → ℕ} {u : ι → ℕ → α} {mesh : ι → ℝ}

/-- Mixed increment sizes of a uniformly continuous path and a bounded-variation path
have sum tending to zero along any family of monotone grids with vanishing mesh. -/
theorem tendsto_sum_dist_mul_dist_of_boundedVariationOn (hf : UniformContinuousOn f s)
    (hg : BoundedVariationOn g s)
    (hu : ∀ k, MonotoneOn (u k) (Iic (n k))) (hus : ∀ k i, i ≤ n k → u k i ∈ s)
    (hmesh : ∀ k i, i < n k → dist (u k (i + 1)) (u k i) ≤ mesh k)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k), dist (f (u k (i + 1))) (f (u k i)) *
      dist (g (u k (i + 1))) (g (u k i))) l (𝓝 0) := by
  -- Uniform continuity gives an arbitrarily small increment bound; total variation is fixed.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hV : 0 < (eVariationOn g s).toReal + 1 := by positivity
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp hf
    (ε / ((eVariationOn g s).toReal + 1)) (div_pos hε hV)
  filter_upwards [(tendsto_order.mp hlim).2 δ hδ] with k hk
  have hbound := hg.sum_dist_mul_dist_le (hu k) (hus k) (div_pos hε hV).le
    (fun i hi ↦ (hcont _ (hus k _ (by omega)) _ (hus k _ (by omega))
      ((hmesh k i hi).trans_lt hk)).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦
    mul_nonneg dist_nonneg dist_nonneg)]
  exact hbound.trans_lt (by
    have := (div_pos hε hV)
    nlinarith [div_mul_cancel₀ ε hV.ne'])

section Real

variable {f g : α → ℝ}

/-- The signed mixed increment sum vanishes when one real path is uniformly continuous
and the other has bounded variation. -/
theorem tendsto_sum_sub_mul_sub_of_boundedVariationOn (hf : UniformContinuousOn f s)
    (hg : BoundedVariationOn g s)
    (hu : ∀ k, MonotoneOn (u k) (Iic (n k))) (hus : ∀ k i, i ≤ n k → u k i ∈ s)
    (hmesh : ∀ k i, i < n k → dist (u k (i + 1)) (u k i) ≤ mesh k)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      (f (u k (i + 1)) - f (u k i)) * (g (u k (i + 1)) - g (u k i))) l (𝓝 0) := by
  apply squeeze_zero_norm' (Eventually.of_forall fun k ↦ ?_)
    (hf.tendsto_sum_dist_mul_dist_of_boundedVariationOn hg hu hus hmesh hlim)
  calc
    _ ≤ ∑ i ∈ Finset.range (n k),
        ‖(f (u k (i + 1)) - f (u k i)) * (g (u k (i + 1)) - g (u k i))‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [Real.norm_eq_abs, abs_mul, Real.dist_eq]

/-- Adding a uniformly continuous bounded-variation path changes squared-increment sums
by a quantity tending to zero. Neither path's squared-increment sums need converge. -/
theorem tendsto_sum_sq_add_sub_of_boundedVariationOn (hf : UniformContinuousOn f s)
    (hg : UniformContinuousOn g s) (hgv : BoundedVariationOn g s)
    (hu : ∀ k, MonotoneOn (u k) (Iic (n k))) (hus : ∀ k i, i ≤ n k → u k i ∈ s)
    (hmesh : ∀ k i, i < n k → dist (u k (i + 1)) (u k i) ≤ mesh k)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun k ↦
      (∑ i ∈ Finset.range (n k),
        ((f + g) (u k (i + 1)) - (f + g) (u k i)) ^ 2) -
      ∑ i ∈ Finset.range (n k), (f (u k (i + 1)) - f (u k i)) ^ 2) l (𝓝 0) := by
  have hfg := hf.tendsto_sum_sub_mul_sub_of_boundedVariationOn hgv hu hus hmesh hlim
  have hgg := hg.tendsto_sum_sub_mul_sub_of_boundedVariationOn hgv hu hus hmesh hlim
  convert (hfg.const_mul 2).add hgg using 1
  · ext k
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      Pi.add_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp

end Real

end UniformContinuousOn
