/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
import TauCeti.GroupTheory.QuotientGroup.Map

/-!
# Subgroups containing the pro-`p` kernel

Let `G` be a profinite group with pro-`p` kernel `N`, so that `G(p) = G ⧸ N` is the maximal pro-`p`
quotient. A subgroup `H` of `G` containing `N` has the same maximal pro-`p` quotient as `G`, cut
down to `H`: its pro-`p` kernel is `N` itself. One inclusion is functoriality of the pro-`p`
kernel. The other holds because `N` has no nontrivial `p`-group quotient
(`TauCeti.proPKernel_proPKernel_eq_top`), so `N` lies in every open normal subgroup `U` of `H` with
`p`-group quotient, as `N ⧸ (N ⊓ U)` embeds in the `p`-group `H ⧸ U`.

Consequently the map `H(p) → G(p)` induced by the inclusion is injective, with image `H ⧸ N`, of
the same index in `G(p)` as `H` in `G`. This is the group-theoretic form of the statement that for
a finite extension `L/K` inside the maximal pro-`p` extension of `K`, the maximal pro-`p` Galois
group of `L` is the open subgroup of that of `K` fixing `L`. The results are stated for a
topological embedding `f : H → G`, which is how such subgroups arise in practice.

## Main results

* `TauCeti.proPKernel_eq_comap_of_le_range`: if `f : H → G` is an embedding whose image contains
  the pro-`p` kernel of `G`, the pro-`p` kernel of `H` is the preimage of that of `G`.
* `TauCeti.proPKernel_eq_subgroupOf`: the same for a subgroup containing the pro-`p` kernel.
* `TauCeti.maximalProPQuotient.map_injective_of_le_range`: such an embedding induces an injective
  map of maximal pro-`p` quotients.
* `TauCeti.maximalProPQuotient.index_range_map_of_le_range`: its image has the same index in `G(p)`
  as the image of `f` in `G`.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- **The index of a subgroup containing the pro-`p` kernel.** If the image of `f : H → G`
contains the pro-`p` kernel of `G`, the image of the induced map `H(p) → G(p)` has the same index
in `G(p)` as the image of `f` in `G`. -/
theorem maximalProPQuotient.index_range_map_of_le_range (f : H →* G) (hf : Continuous f)
    (hle : proPKernel p G ≤ f.range) :
    (maximalProPQuotient.map (p := p) f hf).range.index = f.range.index := by
  rw [maximalProPQuotient.range_map]
  exact Subgroup.index_map_eq _ (maximalProPQuotient.mk_surjective p G)
    ((QuotientGroup.ker_mk' _).trans_le hle)

/-! ### Subgroups containing the pro-`p` kernel -/

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The pro-`p` kernel of a subgroup containing the pro-`p` kernel.** Let `f : H → G` be a
topological embedding of groups into a profinite group whose image contains the pro-`p` kernel
`N` of `G`. Then the pro-`p` kernel of `H` is the preimage of `N`. -/
theorem proPKernel_eq_comap_of_le_range (f : H →* G) (hf : Topology.IsEmbedding f)
    (hle : proPKernel p G ≤ f.range) : proPKernel p H = (proPKernel p G).comap f := by
  refine le_antisymm (proPKernel_le_comap f hf.continuous) fun x hx ↦ ?_
  -- The inverse of `f` on the pro-`p` kernel of `G` is a continuous homomorphism `g`.
  let g : proPKernel p G →* H :=
    (MonoidHom.ofInjective hf.injective).symm.toMonoidHom.comp (Subgroup.inclusion hle)
  have hfg : ∀ n, f (g n) = n := fun n ↦ MonoidHom.apply_ofInjective_symm hf.injective _
  have hg : Continuous g := hf.continuous_iff.mpr <| by
    simpa only [Function.comp_def, hfg] using continuous_subtype_val
  -- Every open normal subgroup of `H` with `p`-group quotient pulls back to all of `N`.
  refine mem_proPKernel_iff.mpr fun U hU ↦ ?_
  have hN : proPKernel p (proPKernel p G) ≤ (U.comap g hg).toSubgroup :=
    proPKernel_le (hU.quotient_comap g)
  rw [proPKernel_proPKernel_eq_top] at hN
  have hgx : g ⟨f x, hx⟩ = x := hf.injective (hfg _)
  rw [← hgx]
  exact hN (Subgroup.mem_top _)

/-- **The pro-`p` kernel of a subgroup containing the pro-`p` kernel** of a profinite group is the
pro-`p` kernel of the ambient group. -/
theorem proPKernel_eq_subgroupOf {S : Subgroup G} (hS : proPKernel p G ≤ S) :
    proPKernel p S = (proPKernel p G).subgroupOf S :=
  proPKernel_eq_comap_of_le_range S.subtype Topology.IsEmbedding.subtypeVal
    (S.range_subtype.symm ▸ hS)

/-- **The induced map of maximal pro-`p` quotients is injective** for a subgroup containing the
pro-`p` kernel. If `f : H → G` is a topological embedding into a profinite group whose image
contains the pro-`p` kernel of `G`, the induced map `H(p) → G(p)` is injective. -/
theorem maximalProPQuotient.map_injective_of_le_range (f : H →* G) (hf : Topology.IsEmbedding f)
    (hle : proPKernel p G ≤ f.range) :
    Function.Injective (maximalProPQuotient.map (p := p) f hf.continuous) := by
  have hker := proPKernel_eq_comap_of_le_range f hf hle
  -- The induced map is `QuotientGroup.map` for the kernels, as both agree on classes.
  have hmap : maximalProPQuotient.map (p := p) f hf.continuous =
      QuotientGroup.map _ _ f hker.le :=
    QuotientGroup.monoidHom_ext _ <| MonoidHom.ext <| maximalProPQuotient.map_mk f hf.continuous
  rw [hmap]
  exact QuotientGroup.map_injective_of_eq_comap f (proPKernel p G) hker

end TauCeti
