/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.TwoSided

/-!
# Separating locally bicollared embeddings are two-sided

A locally bicollared map `f : N → M` (`TauCeti.IsLocallyBicollared`) has a bicollar near each
point of `N`, but the two sides of these local bicollars need not fit together: the core circle
of an open Möbius band is locally bicollared and not bicollared. Brown's bicollaring theorem
(`TauCeti.IsLocallyBicollaredWithSides.exists_isBicollar`) assembles the local bicollars once
their sides are chosen consistently, with positive side in a fixed open set `A` and negative side
in a disjoint open set `B`.

This file shows that such a consistent choice exists as soon as the image of `f` separates `M`.
Let `f` be a locally bicollared embedding of a preconnected, locally connected space `N` into a
preconnected space `M`, and write the complement of its image as the union of two disjoint
nonempty open sets `A` and `B`. Then every point of the image lies in the closure of both `A` and
`B` (`TauCeti.IsLocallyBicollared.range_subset_closure`). Near any point, a local bicollar over
a preconnected neighbourhood has preconnected sides that miss the image, so each side lies in `A`
or in `B`; they cannot lie on the same side, because the image is in the closure of both. So `f`
is locally bicollared with sides `A` and `B`
(`TauCeti.IsLocallyBicollared.isLocallyBicollaredWithSides`).

For a compact domain and a Hausdorff target, Brown's theorem then gives a global bicollar
(`TauCeti.IsLocallyBicollared.exists_isBicollar`). In particular a locally bicollared injective
map from a compact, connected, locally connected space into a connected Hausdorff space is
bicollared as soon as the complement of its image is disconnected
(`TauCeti.IsLocallyBicollared.isBicollared_of_not_isPreconnected_compl_range`). This is how
Brown deduces that a locally flat `(n - 1)`-sphere in the `n`-sphere is bicollared, for `n ≥ 2`,
from the Jordan–Brouwer separation theorem.

## Main results

* `TauCeti.IsLocallyBicollared.exists_isPreconnected_isBicollar`: an embedding that is locally
  bicollared has, near every point, a bicollar over a preconnected open set that meets the image
  only along its zero slice.
* `TauCeti.IsLocallyBicollared.isLocallyBicollaredWithSides_of_range_subset_closure`: the local
  bicollars can be given sides `A` and `B` when the image lies in the closure of both.
* `TauCeti.IsLocallyBicollared.range_subset_closure`: if the image of a connected domain
  separates a connected space, every point of the image is in the closure of both sides.
* `TauCeti.IsLocallyBicollared.isLocallyBicollaredWithSides`: a separating locally bicollared
  embedding of a connected domain is two-sided.
* `TauCeti.IsLocallyBicollared.exists_isBicollar` and
  `TauCeti.IsLocallyBicollared.isBicollared_of_not_isPreconnected_compl_range`: for a compact
  domain, it is bicollared.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

namespace TauCeti

open Function Filter Metric Set Topology

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M} {A B : Set M}

namespace IsLocallyBicollared

/-- A locally bicollared embedding of a locally connected space has, near every point, a bicollar
over a preconnected open set whose image meets the image of the map only along the zero slice. -/
theorem exists_isPreconnected_isBicollar [LocallyConnectedSpace N] (h : IsLocallyBicollared f)
    (hf : IsEmbedding f) (x : N) :
    ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsPreconnected U ∧ ∃ b : U × ℝ → M,
      IsBicollar (f ∘ ((↑) : U → N)) b ∧ b ⁻¹' range f = univ ×ˢ ({0} : Set ℝ) := by
  obtain ⟨U, hU, hxU, hb⟩ := isLocallyBicollared_iff.1 h x
  obtain ⟨b, hb⟩ := isBicollared_iff.1 hb
  -- The local bicollar `b` over `U` is shrunk to a box inside an open set `O` of `M` that meets
  -- the image of `f` exactly in `f(U)`; the embedding hypothesis provides `O`.
  obtain ⟨O, hO, hOU⟩ := hf.isInducing.isOpen_iff.1 hU
  have hbO : b ⁻¹' O ∈ 𝓝 ((⟨x, hxU⟩ : U), (0 : ℝ)) := by
    refine (hO.preimage hb.isOpenEmbedding.continuous).mem_nhds ?_
    rw [mem_preimage, hb.apply_zero, comp_apply, ← mem_preimage, hOU]
    exact hxU
  -- A box `u × (-ε, ε)` around `(x, 0)` that `b` maps into `O`.
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hbO
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.1 hv
  -- The new domain: the component of `x` in the interior of `u`, read as a subset of `N`.
  set W : Set N := (↑) '' interior u
  have hW : IsOpen W := hU.isOpenMap_subtype_val _ isOpen_interior
  have hxW : x ∈ W := ⟨⟨x, hxU⟩, mem_interior_iff_mem_nhds.2 hu, rfl⟩
  set V : Set N := connectedComponentIn W x
  have hV : IsOpen V := hW.connectedComponentIn
  have hVW : V ⊆ W := connectedComponentIn_subset _ _
  have hVU : V ⊆ U := fun y hy => by
    obtain ⟨z, -, rfl⟩ := hVW hy
    exact z.2
  have hVu : ∀ y : V, inclusion hVU y ∈ u := fun y => by
    obtain ⟨z, hz, hzy⟩ := hVW y.2
    obtain rfl : z = inclusion hVU y := Subtype.ext hzy
    exact interior_subset hz
  -- The new depth coordinate: `ℝ` reparametrized as `(-ε, ε)`.
  set ρ := OpenPartialHomeomorph.univBall (0 : ℝ) ε
  have hρ : IsOpenEmbedding ρ := ρ.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _)
  have hρv : ∀ t, ρ t ∈ v := fun t => hεv <| by
    rw [← OpenPartialHomeomorph.univBall_target (0 : ℝ) hε]
    exact ρ.map_source (by simp [ρ])
  have hb' : IsBicollar (f ∘ ((↑) : V → N)) (b ∘ Prod.map (inclusion hVU) ρ) :=
    ⟨hb.isOpenEmbedding.comp ((IsOpenEmbedding.inclusion hVU
      (hV.preimage continuous_subtype_val)).prodMap hρ), fun y => by
        simp [ρ, hb.apply_zero]⟩
  refine ⟨V, hV, mem_connectedComponentIn hxW, isPreconnected_connectedComponentIn, _, hb', ?_⟩
  -- The new bicollar maps into `O`, which meets the image of `f` only in `f(U)`, and there the old
  -- bicollar meets the image only along its zero slice.
  ext ⟨y, t⟩
  refine ⟨fun ⟨z, hz⟩ => ⟨mem_univ _, ?_⟩, fun ⟨_, ht⟩ => ?_⟩
  · have hzU : z ∈ U := by
      rw [← hOU, mem_preimage, hz]
      exact huv ⟨hVu y, hρv t⟩
    have hmem : (inclusion hVU y, ρ t) ∈ b ⁻¹' range (f ∘ ((↑) : U → N)) :=
      ⟨⟨z, hzU⟩, hz⟩
    rw [hb.preimage_range] at hmem
    refine hρ.injective ?_
    simpa [ρ] using hmem.2
  · obtain rfl : t = 0 := ht
    exact ⟨y, (hb'.apply_zero y).symm⟩

/-- Let `b` be a local bicollar as in `exists_isPreconnected_isBicollar`, and write the complement
of the image of `f` as the union of disjoint open sets `A` and `B`. A side of `b` at depths in a
preconnected set `s` avoiding `0` is preconnected and misses the image, so if it meets `A` then it
lies in `A`. -/
private theorem image_subset_of_inter_nonempty {U : Set N} (hU : IsPreconnected U)
    {b : U × ℝ → M} (hb : IsBicollar (f ∘ ((↑) : U → N)) b)
    (hbf : b ⁻¹' range f = univ ×ˢ ({0} : Set ℝ)) {s : Set ℝ} (hs : IsPreconnected s)
    (hs0 : (0 : ℝ) ∉ s) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hsA : (b '' (univ ×ˢ s) ∩ A).Nonempty) :
    b '' (univ ×ˢ s) ⊆ A := by
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.1 hU
  refine IsPreconnected.subset_left_of_subset_union hA hB hAB ?_ hsA
    ((isPreconnected_univ.prod hs).image _ hb.isOpenEmbedding.continuous.continuousOn)
  rintro _ ⟨q, hq, rfl⟩
  rw [← hcompl]
  intro hqf
  rw [← mem_preimage, hbf] at hqf
  exact hs0 (hqf.2 ▸ hq.2)

/-- The side of the local bicollar in `image_subset_of_inter_nonempty` lies in `A` or in `B`. -/
private theorem image_subset_or_image_subset {U : Set N} (hU : IsPreconnected U)
    {b : U × ℝ → M} (hb : IsBicollar (f ∘ ((↑) : U → N)) b)
    (hbf : b ⁻¹' range f = univ ×ˢ ({0} : Set ℝ)) {s : Set ℝ} (hs : IsPreconnected s)
    (hs0 : (0 : ℝ) ∉ s) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hs₀ : s.Nonempty) [Nonempty U] :
    b '' (univ ×ˢ s) ⊆ A ∨ b '' (univ ×ˢ s) ⊆ B := by
  obtain ⟨t, ht⟩ := hs₀
  have hmem : b (Classical.arbitrary U, t) ∈ A ∪ B := by
    rw [← hcompl]
    intro hf
    rw [← mem_preimage, hbf] at hf
    exact hs0 (hf.2 ▸ ht)
  have hq : b (Classical.arbitrary U, t) ∈ b '' (univ ×ˢ s) := ⟨_, ⟨mem_univ _, ht⟩, rfl⟩
  rcases hmem with hA' | hB'
  · exact .inl (image_subset_of_inter_nonempty hU hb hbf hs hs0 hA hB hAB hcompl ⟨_, hq, hA'⟩)
  · exact .inr (image_subset_of_inter_nonempty hU hb hbf hs hs0 hB hA hAB.symm
      (hcompl.trans (union_comm _ _)) ⟨_, hq, hB'⟩)

/-- A local bicollar whose two sides both lie in `A` sweeps out a neighbourhood of its zero slice
missing `B`. -/
private theorem notMem_closure_of_image_subset {U : Set N} {b : U × ℝ → M}
    (hb : IsBicollar (f ∘ ((↑) : U → N)) b) (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B)
    (hpos : b '' (univ ×ˢ Ioi 0) ⊆ A) (hneg : b '' (univ ×ˢ Iio 0) ⊆ A) (y : U) :
    f y ∉ closure B := by
  intro hy
  obtain ⟨_, ⟨⟨u, t⟩, rfl⟩, hB'⟩ := mem_closure_iff_nhds.1 hy (range b)
    (hb.isOpenEmbedding.isOpen_range.mem_nhds ⟨(y, 0), hb.apply_zero y⟩)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exact disjoint_left.1 hAB (hneg ⟨(u, t), ⟨mem_univ _, ht⟩, rfl⟩) hB'
  · refine (hcompl ▸ subset_union_right : B ⊆ (range f)ᶜ) hB' ⟨u, ?_⟩
    exact (hb.apply_zero u).symm
  · exact disjoint_left.1 hAB (hpos ⟨(u, t), ⟨mem_univ _, ht⟩, rfl⟩) hB'

/-- **Two-sidedness from the frontier.** Let `f` be a locally bicollared embedding of a locally
connected space, and write the complement of its image as the union of disjoint open sets `A` and
`B`. If every point of the image lies in the closure of both `A` and `B`, then `f` is locally
bicollared with sides `A` and `B`. -/
theorem isLocallyBicollaredWithSides_of_range_subset_closure [LocallyConnectedSpace N]
    (h : IsLocallyBicollared f) (hf : IsEmbedding f) (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B) (hfA : range f ⊆ closure A)
    (hfB : range f ⊆ closure B) : IsLocallyBicollaredWithSides f A B := by
  refine isLocallyBicollaredWithSides_iff.2 fun x => ?_
  obtain ⟨U, hU, hxU, hUc, b, hb, hbf⟩ := h.exists_isPreconnected_isBicollar hf x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hcompl' : (range f)ᶜ = B ∪ A := hcompl.trans (union_comm _ _)
  have hpos := image_subset_or_image_subset hUc hb hbf isPreconnected_Ioi
    (lt_irrefl 0) hA hB hAB hcompl nonempty_Ioi
  have hneg := image_subset_or_image_subset hUc hb hbf isPreconnected_Iio
    (lt_irrefl 0) hA hB hAB hcompl nonempty_Iio
  -- The two sides cannot both lie in `A`, nor both in `B`, since `f x` is in both closures.
  have hx : f ((⟨x, hxU⟩ : U) : N) ∈ range f := mem_range_self _
  refine ⟨U, hU, hxU, ?_⟩
  rcases hpos with hpA | hpB <;> rcases hneg with hnA | hnB
  · exact absurd (hfB hx) (notMem_closure_of_image_subset hb hAB hcompl hpA hnA _)
  · exact ⟨b, hb, fun p hp => hpA ⟨p, hp, rfl⟩, fun p hp => hnB ⟨p, hp, rfl⟩⟩
  · refine ⟨_, hb.comp_prodMap_id_neg, fun p hp => hnA ⟨_, ⟨mem_univ _, ?_⟩, rfl⟩,
      fun p hp => hpB ⟨_, ⟨mem_univ _, ?_⟩, rfl⟩⟩
    · exact neg_neg_of_pos hp.2
    · exact neg_pos.2 hp.2
  · exact absurd (hfA hx)
      (notMem_closure_of_image_subset hb hAB.symm hcompl' hpB hnB _)

/-- **The image of a separating map lies in the closure of each side.** Let `f` be a locally
bicollared embedding of a preconnected, locally connected space into a preconnected space, and
write the complement of its image as the union of disjoint nonempty open sets `A` and `B`. Then
every point of the image lies in the closure of `A`. -/
theorem range_subset_closure [PreconnectedSpace N] [LocallyConnectedSpace N]
    [PreconnectedSpace M] (h : IsLocallyBicollared f) (hf : IsEmbedding f) (hA : IsOpen A)
    (hB : IsOpen B) (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B) (hA₀ : A.Nonempty)
    (hB₀ : B.Nonempty) : range f ⊆ closure A := by
  have hAf : Disjoint A (range f) := by
    rw [disjoint_comm, ← subset_compl_iff_disjoint_left, hcompl]
    exact subset_union_left
  -- The points of `N` sent into the closure of `A` form a clopen set. It is open: near such a
  -- point, some side of a preconnected local bicollar meets `A`, hence lies in `A`, and the image
  -- of the whole neighbourhood lies in the closure of that side.
  have hopen : IsOpen (f ⁻¹' closure A) := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨U, hU, hxU, hUc, b, hb, hbf⟩ := h.exists_isPreconnected_isBicollar hf x
    refine ⟨U, fun y hy => ?_, hU, hxU⟩
    rw [mem_preimage]
    obtain ⟨_, ⟨⟨u, t⟩, rfl⟩, hbA⟩ := mem_closure_iff_nhds.1 hx (range b)
      (hb.isOpenEmbedding.isOpen_range.mem_nhds ⟨(⟨x, hxU⟩, 0), hb.apply_zero _⟩)
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact closure_mono (image_subset_of_inter_nonempty hUc hb hbf isPreconnected_Iio
        (lt_irrefl 0) hA hB hAB hcompl ⟨_, ⟨(u, t), ⟨mem_univ _, ht⟩, rfl⟩, hbA⟩)
        (hb.apply_mem_closure_image (by simp) ⟨y, hy⟩)
    · exact absurd ⟨u, (hb.apply_zero u).symm⟩ (disjoint_left.1 hAf hbA)
    · exact closure_mono (image_subset_of_inter_nonempty hUc hb hbf isPreconnected_Ioi
        (lt_irrefl 0) hA hB hAB hcompl ⟨_, ⟨(u, t), ⟨mem_univ _, ht⟩, rfl⟩, hbA⟩)
        (hb.apply_mem_closure_image (by simp) ⟨y, hy⟩)
  rcases isClopen_iff.1 ⟨isClosed_closure.preimage hf.continuous, hopen⟩ with h0 | h1
  · -- If the set is empty, `A` is closed, as its closure misses `B` and the image of `f`. Then
    -- `A` is clopen in the preconnected space `M`, which `B` rules out.
    have hcl : closure A = A := by
      refine Subset.antisymm (fun p hp => ?_) subset_closure
      have hpB : p ∉ B := disjoint_left.1 (hAB.closure_left hB) hp
      have hpf : p ∉ range f := by
        rintro ⟨y, rfl⟩
        exact (eq_empty_iff_forall_notMem.1 h0 y) hp
      have hp' : p ∈ A ∪ B := hcompl ▸ hpf
      exact hp'.resolve_right hpB
    rcases isClopen_iff.1 ⟨hcl ▸ isClosed_closure, hA⟩ with hA' | hA'
    · exact absurd hA' hA₀.ne_empty
    · obtain ⟨p, hp⟩ := hB₀
      exact absurd (hA' ▸ mem_univ p) (disjoint_right.1 hAB hp)
  · rintro _ ⟨y, rfl⟩
    exact (h1 ▸ mem_univ y : y ∈ f ⁻¹' closure A)

/-- **A separating locally bicollared embedding is two-sided.** Let `f` be a locally bicollared
embedding of a preconnected, locally connected space into a preconnected space, and write the
complement of its image as the union of disjoint nonempty open sets `A` and `B`. Then the local
bicollars of `f` can be chosen with positive side in `A` and negative side in `B`. -/
theorem isLocallyBicollaredWithSides [PreconnectedSpace N] [LocallyConnectedSpace N]
    [PreconnectedSpace M] (h : IsLocallyBicollared f) (hf : IsEmbedding f) (hA : IsOpen A)
    (hB : IsOpen B) (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B) (hA₀ : A.Nonempty)
    (hB₀ : B.Nonempty) : IsLocallyBicollaredWithSides f A B :=
  h.isLocallyBicollaredWithSides_of_range_subset_closure hf hA hB hAB hcompl
    (h.range_subset_closure hf hA hB hAB hcompl hA₀ hB₀)
    (h.range_subset_closure hf hB hA hAB.symm (hcompl.trans (union_comm _ _)) hB₀ hA₀)

/-- **Brown's bicollaring theorem for separating maps.** Let `f` be an injective locally
bicollared map from a compact, preconnected, locally connected space into a preconnected
Hausdorff space, and write the complement of its image as the union of disjoint nonempty open
sets `A` and `B`. Then `f` has a global bicollar with positive side in `A` and negative side in
`B`. -/
theorem exists_isBicollar [CompactSpace N] [PreconnectedSpace N] [LocallyConnectedSpace N]
    [T2Space M] [PreconnectedSpace M] (h : IsLocallyBicollared f) (hf : Injective f)
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B)
    (hA₀ : A.Nonempty) (hB₀ : B.Nonempty) :
    ∃ b : N × ℝ → M, IsBicollar f b ∧ MapsTo b (univ ×ˢ Ioi 0) A ∧
      MapsTo b (univ ×ˢ Iio 0) B :=
  (h.isLocallyBicollaredWithSides (h.continuous.isClosedEmbedding hf).isEmbedding hA hB hAB
    hcompl hA₀ hB₀).exists_isBicollar hf hA hB hAB

/-- **Brown's bicollaring theorem for separating maps**, in terms of connectedness: an injective
locally bicollared map from a compact, preconnected, locally connected space into a preconnected
Hausdorff space is bicollared as soon as the complement of its image is not preconnected. -/
theorem isBicollared_of_not_isPreconnected_compl_range [CompactSpace N] [PreconnectedSpace N]
    [LocallyConnectedSpace N] [T2Space M] [PreconnectedSpace M] (h : IsLocallyBicollared f)
    (hf : Injective f) (hsep : ¬ IsPreconnected (range f)ᶜ) : IsBicollared f := by
  have hopen : IsOpen (range f)ᶜ := (isCompact_range h.continuous).isClosed.isOpen_compl
  simp only [IsPreconnected, not_forall, not_nonempty_iff_eq_empty, exists_prop] at hsep
  obtain ⟨u, v, hu, hv, huv, hsu, hsv, hsuv⟩ := hsep
  obtain ⟨b, hb, -⟩ := h.exists_isBicollar hf (hopen.inter hu) (hopen.inter hv)
    (disjoint_iff_inter_eq_empty.2 (by rw [inter_inter_inter_comm, inter_self, hsuv]))
    (by rw [← inter_union_distrib_left, inter_eq_left.2 huv]) hsu hsv
  exact hb.isBicollared

end IsLocallyBicollared

end TauCeti
