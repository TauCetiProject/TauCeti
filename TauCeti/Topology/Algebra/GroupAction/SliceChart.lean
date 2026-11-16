/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Orbit-space charts from slices

Let a group `G` act on a topological space `X`, and let `σ : S → X` be a map from a topological
space `S`, thought of as a slice. The **slice map** `(g, s) ↦ g • σ s : G × S → X` sweeps the
slice along the orbits of the action. If the slice map is injective on `G × U`, then distinct points
of `U` lie in distinct orbits (`TauCeti.MulAction.injOn_quotientMk_slice`). Suppose moreover that
`U ⊆ S` is open and that the slice map is a local homeomorphism on `G × U`. Then:

* its restriction to `G × U` is an open embedding into `X`, so it identifies `G × U` with an open
  invariant neighbourhood of the orbits through `σ '' U`
  (`TauCeti.MulAction.isOpenEmbedding_smul_slice`);
* `s ↦ [σ s]` is an open embedding of `U` into the orbit space `X ⧸ G`
  (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`).

These are the charts of the orbit space of a free proper action of a Lie group: the inverse
function theorem makes the slice map of a transverse slice a local diffeomorphism near `(1, s₀)`
(`TauCeti.isLocalDiffeomorphAt_smul_slice_iff`), properness makes it injective on `G × U` after
shrinking the slice, and the smoothness of the transitions between these charts is
`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`. No properness, separation or smoothness is
used in this file.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, proof of
  Theorem 1.21.
-/

public section

open Function Set Topology

variable {G X : Type*} [Group G] [MulAction G X]

namespace TauCeti.MulAction

variable {S : Type*} {σ : S → X} {U : Set S}

variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace S]

/-- **Slice maps parametrize open invariant neighbourhoods of orbits.** If the slice map
`(g, s) ↦ g • σ s` is injective on `G × U` and a local homeomorphism there, for an open set `U`,
then its restriction to `G × U` is an open embedding into `X`. -/
theorem isOpenEmbedding_smul_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun p : G × U ↦ p.1 • σ p.2 := by
  -- The restriction is the slice map composed with the inclusion `G × U → G × S`.
  have hmaps : ∀ p : G × U, (p.1, (p.2 : S)) ∈ univ ×ˢ U := fun p ↦ ⟨mem_univ _, p.2.2⟩
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, fun W hW ↦ ?_⟩
  · exact hloc.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) hmaps
  · intro p q hpq
    have h1 := hinj (hmaps p) (hmaps q) hpq
    exact Prod.ext (Prod.ext_iff.1 h1).1 (Subtype.ext (Prod.ext_iff.1 h1).2)
  · -- An open subset of `G × U` is open in `G × S`, and the slice map is open on `univ ×ˢ U`.
    have hW' : IsOpen (Prod.map id ((↑) : U → S) '' W) :=
      (IsOpenMap.id.prodMap hU.isOpenMap_subtype_val) W hW
    have h1 := (hloc.mono (image_subset_iff.2 fun p _ ↦ hmaps p)).isOpen_image hW'
    rwa [image_image] at h1

/-- **Quotient charts from slices.** If the slice map `(g, s) ↦ g • σ s` is injective on `G × U`
and a local homeomorphism there, for an open set `U`, then `s ↦ [σ s]` is an open embedding of `U`
into the orbit space `X ⧸ G`: distinct points of `U` lie in distinct orbits, and the orbits
through an open subset of `U` form an open subset of `X ⧸ G`. -/
theorem isOpenEmbedding_quotientMk_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s) := by
  -- On `U`, the slice `σ` is the restriction of the slice map to `{1} × U`.
  have hσ : ContinuousOn σ U := by
    have h1 : ContinuousOn (fun s : S ↦ (1 : G) • σ s) U :=
      hloc.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        fun s hs ↦ ⟨mem_univ _, hs⟩
    simpa only [one_smul] using h1
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, fun W hW ↦ ?_⟩
  · exact continuous_quot_mk.comp hσ.domRestrict
  · exact fun s s' hss' ↦ Subtype.ext (injOn_quotientMk_slice hinj s.2 s'.2 hss')
  · -- The orbits through the image of `W` pull back to the image of the open set `G × W` under
    -- the slice map.
    have hT : IsOpen (((↑) : U → S) '' W) := hU.isOpenMap_subtype_val W hW
    have hpre : Quotient.mk (MulAction.orbitRel G X) ⁻¹'
        ((fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s)) '' W) =
        (fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ (((↑) : U → S) '' W)) := by
      convert MulAction.quotient_preimage_image_eq_union_mul (G := G) (σ '' (((↑) : U → S) '' W))
        using 1
      · simp only [image_image]; rfl
      · rw [image_prod (fun (g : G) (s : S) ↦ g • σ s), ← iUnion_image_left, biUnion_univ]
        simp only [image_image]
    -- The quotient topology is coinduced; `hpre` computes the preimage.
    rw [isOpen_coinduced]
    convert (hloc.mono (prod_mono_right (Subtype.coe_image_subset U W))).isOpen_image
      (isOpen_univ.prod hT) using 1
    exact hpre

end TauCeti.MulAction
