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

/-- **The nonarchimedean property transports along an open homomorphism.** If `f : G → H` is a
monoid homomorphism that is open and continuous at `1`, and `G` is nonarchimedean, then every
neighbourhood of `1` in `H` contains an open subgroup.

This asks nothing of `H` beyond a group structure and a topology. The bundled form is
`nonarchimedean_of_isOpenMap`, which needs `[IsTopologicalGroup H]` in addition — see the module
docstring. -/
@[to_additive /-- **The nonarchimedean property transports along an open homomorphism.** If
`f : G → H` is an additive monoid homomorphism that is open and continuous at `0`, and `G` is
nonarchimedean, then every neighbourhood of `0` in `H` contains an open additive subgroup. -/]
theorem exists_openSubgroup_subset_of_isOpenMap {G H F : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [Group H] [TopologicalSpace H] [FunLike F G H] [MonoidHomClass F G H]
    (f : F) (hf : ContinuousAt f 1) (hopen : IsOpenMap f) {U : Set H} (hU : U ∈ 𝓝 (1 : H)) :
    ∃ V : OpenSubgroup H, (V : Set H) ⊆ U := by
  obtain ⟨V, hV⟩ := is_nonarchimedean _ (hf.preimage_mem_nhds (by rwa [map_one]))
  -- The open subgroup is the image `V.toSubgroup.map f`. Both goals are stated through the
  -- `OpenSubgroup` constructor, i.e. about the `.carrier` field; naming that carrier as the
  -- subgroup's coercion is what lets `Subgroup.coe_map` rewrite it to the image `f '' V`, the
  -- form `hopen` and `hV` are stated in.
  refine ⟨⟨V.toSubgroup.map (f : G →* H), ?_⟩, ?_⟩
  · change IsOpen ((V.toSubgroup.map (f : G →* H) : Subgroup H) : Set H)
    simpa only [Subgroup.coe_map, MonoidHom.coe_ofClass, OpenSubgroup.coe_toSubgroup] using
      hopen _ V.isOpen
  · change ((V.toSubgroup.map (f : G →* H) : Subgroup H) : Set H) ⊆ U
    simpa only [Subgroup.coe_map, MonoidHom.coe_ofClass, OpenSubgroup.coe_toSubgroup] using
      Set.image_subset_iff.2 hV

/-- **Transport along an open homomorphism.** If `f : G → H` is a monoid homomorphism that is open
and continuous at `1`, and `G` is nonarchimedean, then so is `H`. This generalizes Mathlib's
`nonarchimedean_of_emb`, which is the case of an open *embedding*; injectivity is not used.

`[IsTopologicalGroup H]` is required by the conclusion rather than by the argument:
`NonarchimedeanGroup` extends `IsTopologicalGroup`, so `continuous_mul` and `continuous_inv` are
fields of the structure being built. For the transport without it, use
`exists_openSubgroup_subset_of_isOpenMap`. -/
@[to_additive /-- **Transport along an open homomorphism.** If `f : G → H` is an additive monoid
homomorphism that is open and continuous at `0`, and `G` is nonarchimedean, then so is `H`. -/]
theorem nonarchimedean_of_isOpenMap {G H F : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [FunLike F G H]
    [MonoidHomClass F G H] (f : F) (hf : ContinuousAt f 1) (hopen : IsOpenMap f) :
    NonarchimedeanGroup H where
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
    obtain ⟨W, hW, hWU⟩ := (mem_nhds_subtype _ _ _).mp hU
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
    exact ⟨V.comap H.subtype continuous_subtype_val, fun _ hx ↦ hWU (hV hx)⟩

/-- **A subring of a nonarchimedean ring is nonarchimedean** in the subspace topology. -/
instance Subring.instNonarchimedeanRing {R : Type*} [Ring R] [TopologicalSpace R]
    [NonarchimedeanRing R] (S : Subring R) : NonarchimedeanRing S where
  -- This is `AddSubgroup.instNonarchimedeanAddGroup` at `S.toAddSubgroup`, whose carrier is that
  -- of `S`; typeclass search for `NonarchimedeanRing ↥S` does not unfold `Subring` to
  -- `AddSubgroup` on its own, so the instance is keyed here.
  is_nonarchimedean :=
    (inferInstance : NonarchimedeanAddGroup ↥S.toAddSubgroup).is_nonarchimedean
