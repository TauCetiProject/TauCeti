/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Bounded perturbations of proper maps

A continuous map at uniformly bounded distance from a proper map into a proper metric space
is proper. For example, a uniformly small smooth perturbation of a proper real-valued
exhaustion function remains proper. The source needs no metric or separation assumptions.

The proof uses Mathlib's compactness of closed thickenings in proper metric spaces: the
inverse image of a compact set under the perturbed map is a closed subset of the original
map's inverse image of a compact thickening.
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

end TauCeti
