/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Maps.Strict.Group
public import TauCeti.Topology.Algebra.GroupCompletion
public import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Surjective

/-!
# Completion of strict exact sequences of nonarchimedean groups

A homomorphism of topological groups is *strict* (`Topology.IsStrictMap`) if it is continuous and
open onto its image with the subspace topology. For first-countable nonarchimedean abelian groups,
strictness and exactness survive passage to the separated completions: if `G → H → K` is exact
with strict maps, then so is `Completion G → Completion H → Completion K`. No Hausdorff hypothesis
is made on the original groups; an indiscrete group completes to zero.

This is how exactness of an algebraic complex of topological modules (for instance a Čech complex
of localizations with adic topologies) becomes exactness of the complex of completions, which is
the form used in sheafiness arguments for Huber rings. Applied at each degree, it shows that the
completion of a strict exact complex of such groups is again strict and exact.

The proof factors a strict map `f` as the open surjection onto its range followed by the inclusion
of the range (`AddMonoidHom.completion_eq_comp_rangeRestrict`). Completion keeps the first an open
surjection (`AddMonoidHom.surjective_completion`) and turns the second into a uniform embedding
whose image is the closure of the range (`AddMonoidHom.range_completion`). At the left end of a
complex, an injective strict map is an embedding, and its completion is a uniform embedding by
`AddMonoidHom.isUniformEmbedding_completion`.

## Main results

* `AddMonoidHom.range_completion_of_isStrictMap`: the image of the completion of a strict map is
  the closure of the image of its range.
* `AddMonoidHom.ker_completion_of_isStrictMap`: the kernel of the completion of a strict map is
  the closure of the image of its kernel.
* `AddMonoidHom.isStrictMap_completion`: completion preserves strict maps.
* `AddMonoidHom.exact_completion`: completion preserves strict exact sequences.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 12, Lemma 2.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of (1.3).
-/

public section

open Topology UniformSpace UniformSpace.Completion

namespace AddMonoidHom

variable {G H : Type*}
  [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [NonarchimedeanAddGroup G]
  [AddGroup H] [UniformSpace H] [IsUniformAddGroup H]

section FirstCountable

variable [(𝓝 (0 : G)).IsCountablyGenerated]

/-- The completion of the corestriction of a strict homomorphism to its range is an open
surjection. -/
private theorem isOpenQuotientMap_completion_rangeRestrict (f : G →+ H) (hf : IsStrictMap f) :
    IsOpenQuotientMap (f.rangeRestrict.completion (hf.continuous.subtype_mk _)) := by
  have hq := f.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hf
  exact ⟨surjective_completion _ hq.continuous hq.surjective hq.isOpenMap,
    continuous_completion _ hq.continuous, isOpenMap_completion _ hq.continuous hq.isOpenMap⟩

/-- **The image of the completion of a strict homomorphism is the closure of the image of its
range.** Without strictness the image can be strictly smaller than this closure: the identity of
`ℤ`, from the discrete to the `p`-adic topology, completes to the inclusion `ℤ → ℤ_[p]`. -/
theorem range_completion_of_isStrictMap (f : G →+ H) (hf : IsStrictMap f) :
    (f.completion hf.continuous).range =
      (f.range.map (toCompl : H →+ Completion H)).topologicalClosure := by
  rw [completion_eq_comp_rangeRestrict, range_comp,
    range_eq_top.mpr (f.isOpenQuotientMap_completion_rangeRestrict hf).surjective,
    ← range_eq_map, range_completion _ IsInducing.subtypeVal, AddSubgroup.range_subtype]

/-- **Completion preserves strict homomorphisms** out of a first-countable nonarchimedean
group. -/
theorem isStrictMap_completion (f : G →+ H) (hf : IsStrictMap f) :
    IsStrictMap (f.completion hf.continuous) := by
  rw [completion_eq_comp_rangeRestrict, coe_comp,
    ← (isUniformEmbedding_completion _ IsInducing.subtypeVal).isEmbedding.isStrictMap_iff]
  exact (f.isOpenQuotientMap_completion_rangeRestrict hf).isQuotientMap.isStrictMap

end FirstCountable

/-- **The kernel of the completion of a strict homomorphism is the closure of the image of its
kernel.** This extends `AddMonoidHom.ker_completion` from open maps to strict maps. -/
theorem ker_completion_of_isStrictMap (f : G →+ H) (hf : IsStrictMap f) :
    (f.completion hf.continuous).ker =
      (f.ker.map (toCompl : G →+ Completion G)).topologicalClosure := by
  have hq := f.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hf
  rw [completion_eq_comp_rangeRestrict,
    ker_comp_of_injective _ _ (isUniformEmbedding_completion _ IsInducing.subtypeVal).injective,
    ker_completion _ hq.continuous hq.isOpenMap, ker_rangeRestrict]

/-- **Completion preserves strict exact sequences.** If `M → N → P` is exact with strict maps,
where `M` is a first-countable nonarchimedean group and `N` is a nonarchimedean group, then the
sequence of separated completions is exact. Its maps are again strict by
`AddMonoidHom.isStrictMap_completion` when `M` and `N` are first countable. No Hausdorff
hypothesis is needed. -/
theorem exact_completion {M N P : Type*}
    [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [NonarchimedeanAddGroup M]
    [(𝓝 (0 : M)).IsCountablyGenerated]
    [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [NonarchimedeanAddGroup N]
    [AddGroup P] [UniformSpace P] [IsUniformAddGroup P]
    {f : M →+ N} {g : N →+ P} (hf : IsStrictMap f) (hg : IsStrictMap g)
    (hfg : Function.Exact f g) :
    Function.Exact (f.completion hf.continuous) (g.completion hg.continuous) := by
  intro y
  rw [← mem_ker, ker_completion_of_isStrictMap g hg, hfg.addMonoidHom_ker_eq,
    ← range_completion_of_isStrictMap f hf, mem_range, Set.mem_range]

end AddMonoidHom
