/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import TauCeti.Topology.UniformSpace.Completion

/-!
# Neighbourhoods of zero and completions of homomorphisms of uniform groups

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

Completion of continuous additive homomorphisms is functorial, and the completion of an inducing
homomorphism is a uniform embedding onto the closure of the image of its range. Factoring a
homomorphism through its range reduces the completion of a strict homomorphism to these facts and
to the completion of an open surjection.

## Main results

* `UniformSpace.Completion.isCountablyGenerated_nhds_zero`.
* `UniformSpace.Completion.discreteTopology_iff_separationQuotient`.
* `AddMonoidHom.completion_comp`: completion of continuous additive homomorphisms is functorial.
* `AddMonoidHom.isUniformEmbedding_completion`: the completion of an inducing homomorphism is a
  uniform embedding.
* `AddMonoidHom.range_completion`: the image of the completion of an inducing homomorphism is the
  closure of the image of its range.
* `AddMonoidHom.completion_eq_comp_rangeRestrict`: the completion of a homomorphism factors
  through the completion of its range.
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

namespace AddMonoidHom

open UniformSpace UniformSpace.Completion Topology

variable {G H K : Type*}
  [AddGroup G] [UniformSpace G] [IsUniformAddGroup G]
  [AddGroup H] [UniformSpace H] [IsUniformAddGroup H]
  [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]

/-- Completion of continuous additive homomorphisms is functorial. -/
theorem completion_comp (f : G →+ H) (g : H →+ K) (hf : Continuous f) (hg : Continuous g) :
    (g.completion hg).comp (f.completion hf) = (g.comp f).completion (hg.comp hf) := by
  ext x
  refine Completion.induction_on x (isClosed_eq ?_ ?_) fun a ↦ by simp
  · exact (g.continuous_completion hg).comp (f.continuous_completion hf)
  · exact (g.comp f).continuous_completion (hg.comp hf)

/-- The completion of an inducing additive homomorphism is a uniform embedding. -/
theorem isUniformEmbedding_completion (f : G →+ H) (hf : IsInducing f) :
    IsUniformEmbedding (f.completion hf.continuous) :=
  (Completion.isUniformInducing_extension
    ((Completion.isUniformInducing_coe H).comp
      (isUniformInducing_of_isInducing hf))).isUniformEmbedding

/-- The image of the completion of an inducing additive homomorphism is the closure of the image
of its range in the completion of the target. -/
theorem range_completion (f : G →+ H) (hf : IsInducing f) :
    (f.completion hf.continuous).range =
      (f.range.map (toCompl : H →+ Completion H)).topologicalClosure := by
  have h := (f.isUniformEmbedding_completion hf).isClosedEmbedding.closure_image_eq
    (Set.range ((↑) : G → Completion G))
  rw [Completion.denseRange_coe.closure_range, Set.image_univ, ← Set.range_comp] at h
  have heq : f.completion hf.continuous ∘ ((↑) : G → Completion G) = fun b ↦ ((f b : H) :
      Completion H) := funext (completion_coe f hf.continuous)
  apply SetLike.coe_injective
  rw [coe_range, ← h, heq, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map]
  congr 1
  ext
  simp

/-- The completion of a continuous additive homomorphism is the completion of its corestriction
to the range, followed by the completed inclusion of the range. -/
theorem completion_eq_comp_rangeRestrict (f : G →+ H) (hf : Continuous f) :
    f.completion hf = (f.range.subtype.completion continuous_subtype_val).comp
      (f.rangeRestrict.completion (hf.subtype_mk _)) := by
  refine ((completion_comp f.rangeRestrict f.range.subtype (hf.subtype_mk _)
    continuous_subtype_val).trans ?_).symm
  simp only [subtype_comp_rangeRestrict]

end AddMonoidHom

end
