/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Transporting a nonarchimedean topology to a quotient or a subobject

`NonarchimedeanGroup G` asks that every neighbourhood of `1` contain an *open subgroup*. That
property passes to the target of any open homomorphism that is continuous at `1`: the image of an
open subgroup inside `f ⁻¹' U` is an open subgroup inside `U`.

Mathlib has the embedding case, `NonarchimedeanGroup.nonarchimedean_of_emb`. Injectivity plays no
part in the argument, so the statement below drops it and keeps only openness; the embedding case
is recovered from it.

The transport is given in two steps, because the two halves have different hypotheses.
`exists_openSubgroup_subset_of_isOpenMap` is the argument itself, and needs nothing of `H` beyond
a group structure and a topology. `nonarchimedean_of_isOpenMap` packages it as the bundled class,
which additionally requires `[IsTopologicalGroup H]` — not for the argument, but because
`NonarchimedeanGroup` *extends* `IsTopologicalGroup`, so the parent structure is part of the
conclusion. Consumers wanting the instance use the second; consumers wanting the property under
minimal hypotheses use the first.

The file also records the *sub*object direction, which is the opposite transport and needs no
openness at all: a subgroup or subring carries the subspace topology, and an open subgroup of the
ambient group meets it in an open subgroup. Mathlib has neither of these two instances, and its
`NonarchimedeanGroup.nonarchimedean_of_emb` does not give them, since it asks the inclusion to be
an *open* embedding, which a subgroup's need not be.

## Main results

* `NonarchimedeanGroup.exists_openSubgroup_subset_of_isOpenMap`, and its additive form
  `NonarchimedeanAddGroup.exists_openAddSubgroup_subset_of_isOpenMap`.
* `Subgroup.instNonarchimedeanGroup` and `Subring.instNonarchimedeanRing`: a subgroup of a
  nonarchimedean group, and a subring of a nonarchimedean ring, are nonarchimedean in the subspace
  topology. These are what put a nonarchimedean structure on the ring of definition of a rational
  localisation.
* `NonarchimedeanGroup.nonarchimedean_of_isOpenMap`, and its additive form
  `NonarchimedeanAddGroup.nonarchimedean_of_isOpenMap`.
-/

public section

open Topology

namespace NonarchimedeanGroup

-- This generalization was proposed in the review of TauCetiProject/TauCeti#4930, on the
-- observation that the quotient instance proved there used nothing about quotients beyond
-- continuity and openness of the quotient map.

/-- **The nonarchimedean property transports along an open homomorphism.** If `f : G →* H` is open
and continuous at `1` and `G` is nonarchimedean, then every neighbourhood of `1` in `H` contains an
open subgroup.

This is the whole of the transport argument, and it asks nothing of `H` beyond a group structure
and a topology. The bundled form is `nonarchimedean_of_isOpenMap`, which needs
`[IsTopologicalGroup H]` in addition — see the module docstring. -/
@[to_additive /-- **The nonarchimedean property transports along an open homomorphism.** If
`f : G →+ H` is open and continuous at `0` and `G` is nonarchimedean, then every neighbourhood of
`0` in `H` contains an open additive subgroup. -/]
theorem exists_openSubgroup_subset_of_isOpenMap {G H : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [Group H] [TopologicalSpace H] (f : G →* H) (hf : ContinuousAt f 1)
    (hopen : IsOpenMap f) {U : Set H} (hU : U ∈ 𝓝 (1 : H)) :
    ∃ V : OpenSubgroup H, (V : Set H) ⊆ U := by
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (G := G) _ (hf (by simpa using hU))
  -- `Subgroup.coe_map` rewrites the carrier of `V.toSubgroup.map f` to the image `f '' V`,
  -- which is the form both `hopen` and `hV` are stated in. It holds by `rfl`, but is named
  -- here rather than left to unfolding.
  refine ⟨⟨V.toSubgroup.map f, ?_⟩, ?_⟩
  · -- `OpenSubgroup`'s field is stated about `.carrier`; naming it as the subgroup's coercion
    -- is what lets `Subgroup.coe_map` rewrite it to the image `f '' V`.
    change IsOpen ((V.toSubgroup.map f : Subgroup H) : Set H)
    simpa only [Subgroup.coe_map, OpenSubgroup.coe_toSubgroup] using hopen _ V.isOpen
  · -- likewise the subset goal is stated through the `OpenSubgroup` constructor, so its
    -- carrier is named as a `Subgroup` coercion before `Subgroup.coe_map` can rewrite it.
    change ((V.toSubgroup.map f : Subgroup H) : Set H) ⊆ U
    simpa only [Subgroup.coe_map, OpenSubgroup.coe_toSubgroup] using Set.image_subset_iff.2 hV

/-- **Transport along an open homomorphism.** If `f : G →* H` is open and continuous at `1`, and
`G` is nonarchimedean, then so is `H`. This generalizes Mathlib's `nonarchimedean_of_emb`, which
is the case of an open *embedding*; injectivity is not used.

`[IsTopologicalGroup H]` is required by the conclusion rather than by the argument:
`NonarchimedeanGroup` extends `IsTopologicalGroup`, so `continuous_mul` and `continuous_inv` are
fields of the structure being built. For the transport without it, use
`exists_openSubgroup_subset_of_isOpenMap`. -/
@[to_additive /-- **Transport along an open homomorphism.** If `f : G →+ H` is open and continuous
at `0`, and `G` is nonarchimedean, then so is `H`. -/]
theorem nonarchimedean_of_isOpenMap {G H : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H)
    (hf : ContinuousAt f 1) (hopen : IsOpenMap f) : NonarchimedeanGroup H where
  is_nonarchimedean _ hU := exists_openSubgroup_subset_of_isOpenMap f hf hopen hU

end NonarchimedeanGroup

/-- **A subgroup of a nonarchimedean group is nonarchimedean** in the subspace topology: the
traces of the ambient open subgroups are open subgroups of it, and they remain a basis. -/
@[to_additive /-- **A subgroup of a nonarchimedean additive group is nonarchimedean** in the
subspace topology: the traces of the ambient open subgroups are open subgroups of it, and they
remain a basis. -/]
instance Subgroup.instNonarchimedeanGroup {G : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] (H : Subgroup G) : NonarchimedeanGroup H where
  is_nonarchimedean U hU := by
    obtain ⟨W, hW, hWU⟩ := (mem_nhds_subtype _ _ _).mp (by simpa using hU)
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
    exact ⟨V.comap H.subtype continuous_subtype_val, fun _ hx ↦ hWU (hV hx)⟩

/-- **A subring of a nonarchimedean ring is nonarchimedean** in the subspace topology.

Nothing is proved here that `AddSubgroup.instNonarchimedeanAddGroup` does not already prove at
`S.toAddSubgroup`: a nonarchimedean ring is a nonarchimedean additive group, the two carriers
agree, and the neighbourhood condition is the additive one verbatim. What the instance adds is
the keying — typeclass search reaching for `NonarchimedeanRing ↥S` does not unfold `Subring` to
`AddSubgroup` on its own. -/
instance Subring.instNonarchimedeanRing {R : Type*} [Ring R] [TopologicalSpace R]
    [NonarchimedeanRing R] (S : Subring R) : NonarchimedeanRing S where
  is_nonarchimedean :=
    (inferInstance : NonarchimedeanAddGroup ↥S.toAddSubgroup).is_nonarchimedean
