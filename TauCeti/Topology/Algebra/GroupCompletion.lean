/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import TauCeti.Topology.UniformSpace.Completion

/-!
# Neighbourhoods of zero in the separated completion of a uniform group

The zero-point form of `UniformSpace.Completion.isCountablyGenerated_nhds_coe`, registered as an
instance. Only a zero and a uniformity are needed; no group structure, no separation, no
completeness.

It exists because results in the Huber development carry `[(𝓝 (0 : A)).IsCountablyGenerated]` and
are applied with `A` a completion — in particular to `A⟨X₁,…,Xₖ⟩`, the completion of the
restricted-series subring, where
`TauCeti.Huber.isCountablyGenerated_nhds_zero_weightedRestrictedSubring` supplies the property
downstairs and this carries it up.

The separated completion of a uniform additive group is discrete exactly when the separation
quotient of the group is, that is, when the closure of zero is open. The points of the group
mapping to zero in the completion are those inseparable from zero, so an open zero of the
completion pulls back to an open zero of the separation quotient. Conversely the closure of the
image of a neighbourhood of zero is a neighbourhood of zero in the completion, and the image of
the points inseparable from zero is `{0}`, which is closed.

## Main results

* `UniformSpace.Completion.isCountablyGenerated_nhds_zero`.
* `UniformSpace.Completion.discreteTopology_iff_separationQuotient`.
-/

public section

open Filter
open scoped Topology

namespace UniformSpace.Completion

/-- **Countable generation of `𝓝 0` passes to the separated completion.**

An instance rather than a theorem because it is consumed by typeclass resolution, whereas the
general statement it specialises is about an arbitrary point and cannot be. -/
instance isCountablyGenerated_nhds_zero {G : Type*} [Zero G] [UniformSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] : (𝓝 (0 : Completion G)).IsCountablyGenerated := by
  have h := isCountablyGenerated_nhds_coe (x := (0 : G))
  rwa [coe_zero] at h

/-- The separated completion of a uniform additive group is discrete exactly when the separation
quotient of the group is discrete. -/
theorem discreteTopology_iff_separationQuotient {G : Type*} [AddGroup G] [UniformSpace G]
    [IsUniformAddGroup G] :
    DiscreteTopology (Completion G) ↔ DiscreteTopology (SeparationQuotient G) := by
  have hpre : ((↑) : G → Completion G) ⁻¹' {0} = SeparationQuotient.mk ⁻¹' {0} := by
    ext x
    simp [← coe_zero, coe_eq_coe_iff_inseparable, ← SeparationQuotient.mk_zero,
      SeparationQuotient.mk_eq_mk]
  rw [discreteTopology_iff_isOpen_singleton_zero, discreteTopology_iff_isOpen_singleton_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← SeparationQuotient.isQuotientMap_mk.isOpen_preimage, ← hpre]
    exact h.preimage (continuous_coe G)
  · have hU : ((↑) : G → Completion G) ⁻¹' {0} ∈ 𝓝 (0 : G) := by
      rw [hpre]
      exact (h.preimage SeparationQuotient.continuous_mk).mem_nhds rfl
    have hcl := isDenseInducing_coe.closure_image_mem_nhds hU
    rw [coe_zero] at hcl
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    rw [Set.mem_singleton_iff.mp hx]
    exact mem_of_superset hcl
      (closure_minimal (Set.image_preimage_subset _ _) isClosed_singleton)

end UniformSpace.Completion

end
