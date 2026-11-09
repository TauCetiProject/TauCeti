/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Preconnected sets in a product with preconnected fibres

A subset of `X × Y` need not be preconnected even when every vertical fibre is: the fibres may
fail to be linked to one another. They are linked as soon as the set contains a preconnected set
meeting every nonempty fibre, for instance the graph of a continuous map over a preconnected
base. This is how one shows that the regions between continuous graphs over a connected base,
such as the sectors of a cylindrical stack, are connected.

## Main declarations

* `TauCeti.isPreconnected_of_isPreconnected_preimage_prodMk`: a set with preconnected fibres
  containing a preconnected set that meets each of its nonempty fibres is preconnected.
* `TauCeti.isPreconnected_of_isPreconnected_preimage_prodMk_of_continuous`: a set with
  preconnected fibres containing the graph of a continuous map over a preconnected base is
  preconnected.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A set `s ⊆ X × Y` is preconnected if each of its fibres `{y | (x, y) ∈ s}` is preconnected
and it contains a preconnected set `t` meeting every nonempty fibre of `s`. -/
theorem isPreconnected_of_isPreconnected_preimage_prodMk {s t : Set (X × Y)}
    (ht : IsPreconnected t) (hts : t ⊆ s) (hst : Prod.fst '' s ⊆ Prod.fst '' t)
    (hs : ∀ x, IsPreconnected (Prod.mk x ⁻¹' s)) : IsPreconnected s := by
  rcases t.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp_all
  -- Every point is joined to `p` through its fibre, which meets `t`.
  refine isPreconnected_of_forall p fun z hz ↦ ?_
  obtain ⟨q, hq, hqz⟩ := hst ⟨z, hz, rfl⟩
  refine ⟨Prod.mk z.1 '' (Prod.mk z.1 ⁻¹' s) ∪ t, union_subset (image_preimage_subset _ _) hts,
    Or.inr hp, Or.inl ⟨z.2, hz, rfl⟩, ?_⟩
  exact ((hs z.1).image _ (Continuous.prodMk_right z.1).continuousOn).union q
    ⟨q.2, by simpa [← hqz] using hts hq, by simp [← hqz]⟩ hq ht

/-- Over a preconnected base, a set `s ⊆ X × Y` is preconnected if each of its fibres
`{y | (x, y) ∈ s}` is preconnected and it contains the graph of a continuous map `f : X → Y`. -/
theorem isPreconnected_of_isPreconnected_preimage_prodMk_of_continuous [PreconnectedSpace X]
    {s : Set (X × Y)} {f : X → Y} (hf : Continuous f) (hfs : ∀ x, (x, f x) ∈ s)
    (hs : ∀ x, IsPreconnected (Prod.mk x ⁻¹' s)) : IsPreconnected s :=
  isPreconnected_of_isPreconnected_preimage_prodMk (isPreconnected_range (by fun_prop))
    (range_subset_iff.2 hfs) (fun x _ ↦ ⟨(x, f x), mem_range_self x, rfl⟩) hs

end TauCeti
