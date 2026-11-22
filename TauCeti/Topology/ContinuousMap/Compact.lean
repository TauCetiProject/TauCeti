/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Uniform positivity of continuous functions

Let `𝕜` be a linearly ordered semiring (`IsOrderedRing 𝕜`) with a topology in which addition and
multiplication by a constant are continuous, so that `C(X, 𝕜)` is a `𝕜`-module. The continuous
functions into `𝕜` that are bounded below by a positive constant (the uniformly positive functions)
form a convex set. On a compact domain this set is open for the compact-open topology (the uniform
topology when `𝕜 = ℝ`). Openness needs only a linear order with a zero on `𝕜` whose lower rays
`Set.Iic a` are closed: the pointwise positive functions form an open set, and on a nonempty
compact domain each of them attains a positive minimum.
These facts apply, for example, to separating positive continuous functions in the proof of
Pietsch domination.

Now let `𝕜` be a linearly ordered semifield in which `a ≤ b` gives `b = a + c` for some `c`
(`ExistsAddOfLE 𝕜`), such as `ℝ≥0` or any linearly ordered field, again with continuous addition
and continuous multiplication by a constant. A linear functional `L` on `C(X, 𝕜)` that is bounded
above on the uniformly positive functions is nonpositive on them, since they form a cone. It is
then nonpositive on every nonnegative function `h`: if `0 < L h`, then a suitable nonnegative
multiple of `h` plus the constant function `1` is uniformly positive and has positive value under
`L`. In the real-valued proof of Pietsch domination this gives the sign of the functional produced
by separating the uniformly positive functions from a cone: it is nonpositive on the nonnegative
functions, so its negation is a positive functional.

A continuous map from a compact space into a metric space (or normed additive group) stays at a
uniform positive distance from every point outside its range.

## Main results

* `ContinuousMap.convex_uniformlyPositive`: the uniformly positive functions form a convex set.
* `ContinuousMap.isOpen_uniformlyPositive`: for a linear order `𝕜` with a zero whose lower rays
  `Set.Iic a` are closed, the uniformly positive functions on a compact space form an open set for
  the compact-open topology.
* `ContinuousMap.exists_pos_le_dist_of_notMem_range`: a continuous map from a compact space into a
  metric space has `dist (f x) y` bounded below by a positive constant when `y ∉ Set.range f`.
* `ContinuousMap.exists_pos_le_norm_sub_of_notMem_range`: the normed-group form `δ ≤ ‖f x - y‖`.
* `ContinuousMap.norm_evalCLM_le_one`, `ContinuousMap.norm_evalCLM`: point evaluation on `C(K, E)`
  for compact `K` has operator norm at most `1`, and exactly `1` when `E` has nontrivial topology.
* `LinearMap.apply_nonpos_of_forall_uniformlyPositive_lt`: a linear functional on `C(X, 𝕜)` that is
  bounded above on the uniformly positive functions is nonpositive on the nonnegative functions.
-/

public section

open Metric

variable {X : Type*} [TopologicalSpace X]

namespace ContinuousMap

/-- Let `𝕜` be a linearly ordered semiring (`IsOrderedRing 𝕜`) with a topology in which addition
and multiplication by a constant are continuous. The continuous functions into `𝕜` that are
uniformly bounded below by a positive constant form a convex set. -/
theorem convex_uniformlyPositive {𝕜 : Type*} [Semiring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] :
    Convex 𝕜 {h : C(X, 𝕜) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  rintro h₁ ⟨δ₁, hδ₁, h₁δ⟩ h₂ ⟨δ₂, hδ₂, h₂δ⟩ a b ha hb hab
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun f ↦ ?_⟩
  have e₁ := (min_le_left δ₁ δ₂).trans (h₁δ f)
  have e₂ := (min_le_right δ₁ δ₂).trans (h₂δ f)
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    min δ₁ δ₂ = a * min δ₁ δ₂ + b * min δ₁ δ₂ := by rw [← add_mul, hab, one_mul]
    _ ≤ a * h₁ f + b * h₂ f := by gcongr

/-- Let `𝕜` be a linear order with zero whose topology makes every lower ray `Set.Iic a` closed
(`ClosedIicTopology 𝕜`). On a compact space, the continuous functions into `𝕜` that are uniformly
bounded below by a positive constant form an open set for the compact-open topology. For
real-valued functions this is the uniform topology. -/
theorem isOpen_uniformlyPositive {𝕜 : Type*} [Zero 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
    [ClosedIicTopology 𝕜] [CompactSpace X] :
    IsOpen {h : C(X, 𝕜) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  refine isOpen_iff_mem_nhds.2 fun h ⟨δ, hδ, hhδ⟩ ↦ Filter.mem_of_superset
    ((isOpen_setOfPred_mapsTo isCompact_univ isOpen_Ioi).mem_nhds
      fun x _ ↦ hδ.trans_le (hhδ x)) fun g hg ↦ ?_
  -- On an empty `X` any `δ > 0` is a lower bound. On a nonempty compact `X`, the pointwise
  -- positive `g` attains a positive minimum.
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨δ, hδ, isEmptyElim⟩
  · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty g.continuous.continuousOn
    exact ⟨g x₀, hg (Set.mem_univ x₀), fun x ↦ hx₀ (Set.mem_univ x)⟩

/-- A continuous map from a compact space into a metric space stays at a uniform positive distance
from every point outside its range. -/
theorem exists_pos_le_dist_of_notMem_range {Y : Type*} [CompactSpace X] [MetricSpace Y]
    (f : C(X, Y)) {y : Y} (hy : y ∉ Set.range f) :
    ∃ δ > 0, ∀ x, δ ≤ dist (f x) y := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (f.continuous.dist continuous_const).continuousOn
    exact ⟨dist (f x₀) y, dist_pos.2 fun h ↦ hy ⟨x₀, h⟩, fun x ↦ hx₀ trivial⟩

/-- A continuous map from a compact space into a normed additive group has `‖f x - y‖` uniformly
bounded below by a positive constant whenever `y ∉ Set.range f`. -/
theorem exists_pos_le_norm_sub_of_notMem_range {E : Type*} [CompactSpace X] [NormedAddCommGroup E]
    (f : C(X, E)) {y : E} (hy : y ∉ Set.range f) :
    ∃ δ > 0, ∀ x, δ ≤ ‖f x - y‖ := by
  simpa only [dist_eq_norm] using f.exists_pos_le_dist_of_notMem_range hy

/-- Point evaluation on `C(K, E)` has operator norm at most `1`. -/
theorem norm_evalCLM_le_one {K 𝕜 E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : K) :
    ‖evalCLM 𝕜 (M := E) x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [evalCLM_apply, one_mul] using f.norm_coe_le_norm x

/-- Point evaluation on `C(K, E)` has operator norm `1` when `E` has nontrivial topology. -/
@[simp]
theorem norm_evalCLM {K 𝕜 E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NontrivialTopology E] (x : K) :
    ‖evalCLM 𝕜 (M := E) x‖ = 1 := by
  refine le_antisymm (norm_evalCLM_le_one x) ?_
  obtain ⟨v, hv⟩ := exists_norm_ne_zero E
  -- The constant function `v` has the same norm as `v`, and evaluates to `v` at `x`.
  have hc : ‖const K v‖ = ‖v‖ :=
    ((norm_le _ (norm_nonneg v)).2 fun _ ↦ le_rfl).antisymm ((const K v).norm_coe_le_norm x)
  simpa only [evalCLM_apply, const_apply, hc, div_self hv] using
    (evalCLM 𝕜 (M := E) x).ratio_le_opNorm (const K v)

end ContinuousMap

namespace LinearMap

/-- A linear functional on `C(X, 𝕜)` that is bounded above on the functions bounded below by a
positive constant is nonpositive on the nonnegative functions. Here `𝕜` is a linearly ordered
semifield in which `a ≤ b` gives `b = a + c` for some `c` (`ExistsAddOfLE 𝕜`), such as `ℝ≥0` or any
linearly ordered field, with a topology in which addition and multiplication by a constant are
continuous. -/
theorem apply_nonpos_of_forall_uniformlyPositive_lt {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] (L : C(X, 𝕜) →ₗ[𝕜] 𝕜) {u : 𝕜}
    (hL : ∀ h ∈ {h : C(X, 𝕜) | ∃ δ > 0, ∀ x, δ ≤ h x}, L h < u) {h : C(X, 𝕜)} (hh : 0 ≤ h) :
    L h ≤ 0 := by
  -- The uniformly positive functions form a cone, so `L` is nonpositive on them: if `L g > 0`,
  -- then `t • g` with `t = (max u 0 + 1) / L g` is uniformly positive and
  -- `L (t • g) = max u 0 + 1 > u`.
  have hL' (g : C(X, 𝕜)) (hg : g ∈ {h : C(X, 𝕜) | ∃ δ > 0, ∀ x, δ ≤ h x}) : L g ≤ 0 := by
    obtain ⟨δ, hδ, hgδ⟩ := hg
    by_contra! hpos
    have ht : 0 < (max u 0 + 1) / L g :=
      div_pos (add_pos_of_nonneg_of_pos (le_max_right u 0) one_pos) hpos
    have hlt := hL (((max u 0 + 1) / L g) • g) ⟨_, mul_pos ht hδ, fun x ↦ by
      simpa using mul_le_mul_of_nonneg_left (hgδ x) ht.le⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at hlt
    exact (le_max_left u 0).not_gt ((lt_add_one _).trans hlt)
  -- As `L 1 ≤ 0`, write `L 1 + c = 0` with `0 ≤ c`. If `0 < L h`, then `t • h + 1` with
  -- `t = (c + 1) / L h` is uniformly positive and `L (t • h + 1) = c + 1 + L 1 = 1` is positive.
  obtain ⟨c, hc0, hc⟩ := le_iff_exists_nonneg_add.1 (hL' 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩)
  by_contra! hpos
  have ht : 0 ≤ (c + 1) / L h := div_nonneg (add_nonneg hc0 zero_le_one) hpos.le
  have hle := hL' (((c + 1) / L h) • h + 1) ⟨1, one_pos, fun x ↦
    le_add_of_nonneg_left (mul_nonneg ht (hh x))⟩
  rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne', add_right_comm, add_comm c,
    hc, zero_add] at hle
  exact hle.not_gt one_pos

end LinearMap
