/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.SeparatedMap

/-!
# Compactness and local injectivity

For a map continuous on a compact set with Hausdorff target, local injectivity in the
relative topology makes the distinct equal-image pairs compact. This supplies the compact
collision set used to attain a first collision radius.

## Main results

* `IsCompact.isCompact_setOf_apply_eq_and_ne`: compactness of distinct equal-image pairs
  after restriction to a compact set.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology

namespace IsCompact

/-- For a map continuous on a compact set and locally injective in its relative topology,
the distinct equal-image pairs in that set form a compact set. The target is Hausdorff. -/
theorem isCompact_setOf_apply_eq_and_ne
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {f : E → X} (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, InjOn f U) :
    IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  have hc : Continuous (K.domRestrict f) := continuousOn_iff_continuous_domRestrict.mp hf
  have hi : IsLocallyInjective (K.domRestrict f) := by
    rw [isLocallyInjective_iff_nhds]
    intro x
    obtain ⟨U, hU, hUi⟩ := hinj x x.property
    exact ⟨Subtype.val ⁻¹' U, preimage_coe_mem_nhds_subtype.mpr hU,
      fun _ hv _ hw he ↦ Subtype.ext (hUi hv hw he)⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcompact := (hi.isClosed_setOf_apply_eq_and_ne hc).isCompact.image
    (continuous_subtypeVal.prodMap continuous_subtypeVal)
  convert hcompact using 1
  ext z
  constructor
  · rintro ⟨hv, hw, he, hne⟩
    exact ⟨(⟨z.1, hv⟩, ⟨z.2, hw⟩),
      ⟨he, fun h ↦ hne (congrArg Subtype.val h)⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.1.property, w.2.property, hw.1,
      fun h ↦ hw.2 (Subtype.ext h)⟩

end IsCompact
