/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.CompactOpen

/-!
# Coherent covers: gluing maps, products and compact subsets

A space `X` carries the topology coherent with a family of subsets `S i`
(`Topology.IsCoherentWith (Set.range S)`) when a set is open as soon as its trace on each `S i` is
open in `S i`. The union of the skeleta of a CW complex carries such a topology, and so does any
space covered by a family of subsets each point has a neighbourhood in.

When the `S i` cover `X`, this file records three consequences.

* Continuous maps on the `S i` which agree on overlaps glue to a continuous map on `X`
  (`ContinuousMap.liftCoherent`). This is the coherent analogue of Mathlib's
  `ContinuousMap.liftCover`, which asks instead that every point have a neighbourhood in some
  `S i`.
* If `Z` is locally compact, then `Z × X` carries the topology coherent with the products
  `Z × S i` (`Topology.IsCoherentWith.univ_prod`). In particular, with `Z` the unit interval,
  homotopies defined on the `S i` and agreeing on overlaps glue to a homotopy on `X`.
* If `X` is `T1` and the cover is an increasing sequence `A 0 ⊆ A 1 ⊆ ⋯`, every compact subset
  of `X` lies in some `A n` (`Topology.IsCoherentWith.exists_subset_of_isCompact`), so maps from
  compact spaces factor through a finite stage.

The covering hypothesis cannot be dropped in the second statement: points outside every `S i`
form an open discrete subspace of `X`, while their products with `Z` need not be discrete.

Finally, a set is closed as soon as it meets every member of the family in a closed subset of `X`
(`Topology.IsCoherentWith.isClosed_of_forall_isClosed_inter`), a restatement of
`Topology.IsCoherentWith.isClosed_iff` with intersections in place of preimages in the subtypes.
-/

public section

open Set

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {ι : Type*} {S : ι → Set X}

namespace Topology.IsCoherentWith

/-- **Products with a locally compact space.** If `X` carries the topology coherent with a cover
`S i` and `Z` is locally compact, then `Z × X` carries the topology coherent with the products
`Z × S i`. -/
theorem univ_prod [LocallyCompactSpace Z] (hS : IsCoherentWith (range S)) (hSX : ⋃ i, S i = univ) :
    IsCoherentWith (range fun i ↦ (univ : Set Z) ×ˢ S i) := by
  refine .of_continuous_prop fun g hg ↦ ?_
  have hg' (i : ι) : ContinuousOn g (univ ×ˢ S i) := hg _ (mem_range_self i)
  -- Curry `g` to a map `G` from `X` into `C(Z, Prop)`; it is continuous on each `S i`, hence
  -- continuous, and `g` is recovered by evaluation, which is continuous as `Z` is locally compact.
  have hslice (x : X) : Continuous fun z ↦ g (z, x) := by
    obtain ⟨i, hx⟩ := mem_iUnion.1 (hSX ▸ mem_univ x)
    exact (hg' i).comp_continuous (continuous_id.prodMk continuous_const)
      fun z ↦ ⟨mem_univ z, hx⟩
  let G : X → C(Z, Prop) := fun x ↦ ⟨fun z ↦ g (z, x), hslice x⟩
  have hG : Continuous G := by
    refine hS.continuous_iff.2 <| forall_mem_range.2 fun i ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun p : S i × Z ↦ g (p.2, p.1) :=
      (hg' i).comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        fun p ↦ ⟨mem_univ _, p.1.2⟩
    exact (ContinuousMap.curry ⟨_, hc⟩).continuous
  exact continuous_eval.comp ((hG.comp continuous_snd).prodMk continuous_fst)

/-- **Compact subsets of an increasing union lie in a finite stage.** If a `T1` space `X` is the
union of an increasing sequence `A n` and carries the topology coherent with it, then every compact
subset of `X` lies in some `A n`. -/
theorem exists_subset_of_isCompact [T1Space X] {A : ℕ → Set X} (hA : Monotone A)
    (hAc : IsCoherentWith (range A)) (hAX : ⋃ n, A n = univ) {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ A n := by
  by_contra! h
  -- Otherwise choose `x n ∈ K` outside `A n`. Only finitely many `x k` lie in a given `A m`, so
  -- every subset of the range `D` of `x` is closed: `D` is closed and discrete in `K`, hence
  -- finite, and then it lies in some `A m`, which `x m` does not.
  choose x hxK hxA using fun n ↦ not_subset.1 (h n)
  have hcl (E : Set X) (hE : E ⊆ range x) : IsClosed E := by
    refine hAc.isClosed_iff.2 <| forall_mem_range.2 fun m ↦ Finite.isClosed ?_
    refine ((finite_Iio m).image x).preimage Subtype.val_injective.injOn |>.subset fun y hy ↦ ?_
    obtain ⟨k, hk⟩ := hE hy
    exact ⟨k, lt_of_not_ge fun hmk ↦ hxA k (hk ▸ hA hmk y.2), hk⟩
  have hfin : (range x).Finite :=
    (hK.of_isClosed_subset (hcl _ Subset.rfl) (range_subset_iff.2 hxK)).finite <|
      isDiscrete_iff_forall_mem_exists_isClosed.2 fun E hE ↦ ⟨E, hcl E hE, inter_eq_left.2 hE⟩
  choose n hn using fun y ↦ mem_iUnion.1 (hAX ▸ mem_univ y)
  obtain ⟨m, hm⟩ := (hfin.image n).bddAbove
  exact hxA m (hA (hm (mem_image_of_mem n (mem_range_self m))) (hn (x m)))

end Topology.IsCoherentWith

namespace ContinuousMap

variable (S) (φ : ∀ i, C(S i, Z))
  (hφ : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : Topology.IsCoherentWith (range S)) (hSX : ⋃ i, S i = univ)

/-- Continuous maps `φ i` on the members of a cover `S i` of `X` which agree on overlaps glue to a
continuous map on `X`, provided `X` carries the topology coherent with the cover. -/
noncomputable def liftCoherent : C(X, Z) :=
  mk (Set.liftCover S (fun i ↦ φ i) hφ hSX) <| hS.continuous_iff.2 <| forall_mem_range.2 fun i ↦ by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe] using map_continuous (φ i)

variable {S φ hφ hS hSX}

@[simp]
theorem liftCoherent_coe {i : ι} (x : S i) : liftCoherent S φ hφ hS hSX x = φ i x := by
  rw [liftCoherent, coe_mk, Set.liftCover_coe _]

@[simp]
theorem liftCoherent_restrict {i : ι} : (liftCoherent S φ hφ hS hSX).restrict (S i) = φ i := by
  ext
  simp only [restrict_apply, liftCoherent_coe]

end ContinuousMap

/-- If `X` carries the topology coherent with a family `S` of subsets, then a set which meets every
member of `S` in a closed set is closed. -/
theorem Topology.IsCoherentWith.isClosed_of_forall_isClosed_inter {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (hS : IsCoherentWith S) {t : Set X} (ht : ∀ s ∈ S, IsClosed (t ∩ s)) :
    IsClosed t := by
  refine hS.isClosed_iff.2 fun s hs ↦ ?_
  have := (ht s hs).preimage (continuous_subtype_val (p := (· ∈ s)))
  rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at this
