/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Bounded perturbations of proper maps

A continuous map at uniformly bounded distance from a proper map into a proper metric space
is proper. For example, a uniformly small smooth perturbation of a proper real-valued
exhaustion function remains proper. The source needs no metric or separation assumptions.

The proof uses Mathlib's compactness of closed thickenings in proper metric spaces: the
inverse image of a compact set under the perturbed map is a closed subset of the original
map's inverse image of a compact thickening.

In a proper normed group the squared distance `v ↦ ‖v - a‖ ^ 2` from a point tends to infinity
along the cocompact filter, so it is proper, and so is its composition with any closed embedding.
These are the squared-distance exhaustions of closed subsets of Euclidean space used in Morse
theory.
-/

public section

open Set

namespace TauCeti

/-- A continuous map at uniformly bounded distance from a proper map into a proper metric
space is proper. The bound need not be positive; this includes maps from an empty space. -/
theorem _root_.IsProperMap.of_dist_le {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [ProperSpace Y] {f g : X → Y} (hf : IsProperMap f) (hg : Continuous g)
    {C : ℝ} (hfg : ∀ x, dist (f x) (g x) ≤ C) : IsProperMap g := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨hg, fun K hK ↦ ?_⟩
  refine (hf.isCompact_preimage (hK.cthickening (r := C))).of_isClosed_subset
    (hK.isClosed.preimage hg) ?_
  intro x hx
  exact Metric.mem_cthickening_of_dist_le (f x) (g x) C K hx (hfg x)

/-- In a proper normed group, the squared distance from a point is a proper map. -/
theorem isProperMap_norm_sq_sub {E : Type*} [NormedAddCommGroup E] [ProperSpace E] (a : E) :
    IsProperMap fun v : E ↦ ‖v - a‖ ^ 2 := by
  refine isProperMap_iff_tendsto_cocompact.2 ⟨by fun_prop, ?_⟩
  simp_rw [← dist_eq_norm]
  exact ((Filter.tendsto_pow_atTop two_ne_zero).comp
    (tendsto_dist_right_cocompact_atTop a)).mono_right atTop_le_cocompact

/-- The squared distance from a point along a closed embedding into a proper normed group is a
proper map. -/
theorem isProperMap_norm_sq_sub_comp {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [ProperSpace E] {i : X → E} (hi : Topology.IsClosedEmbedding i) (a : E) :
    IsProperMap fun x ↦ ‖i x - a‖ ^ 2 :=
  (isProperMap_norm_sq_sub a).comp hi.isProperMap

end TauCeti
