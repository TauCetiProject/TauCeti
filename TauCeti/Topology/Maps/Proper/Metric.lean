/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.Order.Sublevel

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
theory. Conversely, along a continuous map the squared distance is proper only if the map is
proper, so along the inclusion of a subset only if the subset is closed
(`TauCeti.isProperMap_norm_sq_sub_comp_iff`, `TauCeti.isProperMap_norm_sq_sub_subtypeVal_iff`).
For example, in a normed group punctured at a non-isolated point `y`, the bounded sublevel
`{v | ‖v - a‖² ≤ r}` accumulates at the puncture and is not compact when `‖y - a‖² < r`
(`TauCeti.not_isCompact_compl_singleton_inter_preimage_Iic`), so the squared distance is not
proper (`TauCeti.not_isProperMap_norm_sq_sub_compl_singleton`).
-/

public section

open Set
open scoped Topology

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

/-- Along a continuous map into a proper normed group, the squared distance from a point is a
proper map exactly when the map itself is proper. -/
theorem isProperMap_norm_sq_sub_comp_iff {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [ProperSpace E] {i : X → E} (hi : Continuous i) (a : E) :
    IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) ↔ IsProperMap i :=
  ⟨isProperMap_of_comp_of_t2 (g := fun v : E ↦ ‖v - a‖ ^ 2) hi (by fun_prop),
    fun h ↦ (isProperMap_norm_sq_sub a).comp h⟩

/-- The squared distance from a point, restricted to a subset of a proper normed group, is a
proper map exactly when the subset is closed. -/
theorem isProperMap_norm_sq_sub_subtypeVal_iff {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {S : Set E} (a : E) :
    IsProperMap (fun x : S ↦ ‖(x : E) - a‖ ^ 2) ↔ IsClosed S := by
  rw [isProperMap_norm_sq_sub_comp_iff continuous_subtype_val]
  exact ⟨fun h ↦ Subtype.range_coe (s := S) ▸ h.isClosed_range,
    IsClosed.isProperMap_subtypeVal⟩


section Punctured

variable {F : Type*} [NormedAddCommGroup F]

/-- In a normed group punctured at a non-isolated point `y`, the bounded sublevel `{ρ_a ≤ r}` of
the squared distance from `a` is not compact when `‖y - a‖² < r`: it accumulates at the
puncture. -/
theorem not_isCompact_compl_singleton_inter_preimage_Iic {y a : F} [(𝓝[≠] y).NeBot] {r : ℝ}
    (hr : ‖y - a‖ ^ 2 < r) :
    ¬IsCompact (({y}ᶜ : Set F) ∩ (fun v ↦ ‖v - a‖ ^ 2) ⁻¹' Iic r) :=
  not_isCompact_inter_preimage_Iic (by simp) (by simp)
    (by fun_prop) hr

/-- On a normed group punctured at a non-isolated point `y`, the squared distance from any point
is not a proper map. -/
theorem not_isProperMap_norm_sq_sub_compl_singleton (y a : F) [(𝓝[≠] y).NeBot] :
    ¬IsProperMap fun x : ({y}ᶜ : Set F) ↦ ‖(x : F) - a‖ ^ 2 := by
  intro h
  refine not_isCompact_compl_singleton_inter_preimage_Iic (lt_add_one (‖y - a‖ ^ 2)) ?_
  have hK := (h.isCompact_preimage (isCompact_Icc (a := 0) (b := ‖y - a‖ ^ 2 + 1))).image
    continuous_subtype_val
  convert hK using 1
  ext v
  simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_Iic, mem_image, mem_Icc,
    Subtype.exists, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨hv, hle⟩ ↦ ⟨⟨hv, by positivity⟩, hle⟩, fun ⟨⟨hv, _⟩, hle⟩ ↦ ⟨hv, hle⟩⟩

end Punctured

end TauCeti
