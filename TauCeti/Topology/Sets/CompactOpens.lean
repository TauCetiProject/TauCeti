/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Spectral.Prespectral
public import TauCeti.Topology.LocallyConstant.Compact
public import TauCeti.Topology.LocallyConstant.Fiber

/-!
# Slices of compact open subsets of a product, and compact opens in prespectral spaces

A compact open set `K ⊆ X × Y` has, at each point `x : X`, the slice `K_x = {y | (x, y) ∈ K}`.
When the points of `X` are closed, `K_x` is again compact open
(`TopologicalSpace.CompactOpens.slice`), and when `X` and `Y` are Hausdorff, `x ↦ K_x` is locally
constant (`TopologicalSpace.CompactOpens.isLocallyConstant_slice`). This is how a compact open
subset of a product of locally profinite spaces is cut into finitely many rectangles: `K` is the
union of the rectangles `{x | K_x = T} ×ˢ T` over its finitely many nonempty slices `T`
(`TopologicalSpace.CompactOpens.mem_iff_exists_sliceFiber`), and these have pairwise disjoint
bases. Conversely, any presentation of `K` as such a union determines its slices
(`TopologicalSpace.CompactOpens.slice_eq_of_mem`).

In a prespectral space, whose compact open sets form a basis of the topology, every compact set
`K` inside an open set `V` lies in a compact open set between them (Mathlib's
`PrespectralSpace.exists_isCompact_and_isOpen_between`), and so every compact open subset of a
subspace `Z` contained in an open set `U` is cut out of `Z` by a compact open subset of the whole
space contained in `U` (`TopologicalSpace.CompactOpens.exists_subset_preimage_subtypeVal_eq`).

## Main definitions

* `TopologicalSpace.CompactOpens.slice`: the slice `{y | (x, y) ∈ K}` of a compact open set
  `K ⊆ X × Y` at `x : X`.
* `TopologicalSpace.CompactOpens.slices`: the finitely many slices of `K` over its projection.
* `TopologicalSpace.CompactOpens.sliceFiber`: the compact open set `{x | K_x = T}`, for `T ≠ ⊥`.
* `TopologicalSpace.CompactOpens.swap`: the compact open set `{(y, x) | (x, y) ∈ K}` for
  `K ⊆ X × Y`.

## Main results

* `TopologicalSpace.CompactOpens.isLocallyConstant_slice`: the slices of a compact open subset of
  a product of Hausdorff spaces are locally constant.
* `TopologicalSpace.CompactOpens.slice_prod_of_mem`, `TopologicalSpace.CompactOpens.slice_sup`:
  slices of rectangles and of unions.
* `TopologicalSpace.CompactOpens.mem_iff_exists_sliceFiber`,
  `TopologicalSpace.CompactOpens.pairwiseDisjoint_sliceFiber`,
  `TopologicalSpace.CompactOpens.eq_finsetSup_sliceFiber_prod`: the decomposition of a compact open
  subset of a product into rectangles with pairwise disjoint bases.
* `TopologicalSpace.CompactOpens.exists_subset_preimage_subtypeVal_eq`: in a prespectral space,
  every compact open subset of a subspace contained in an open set `U` is cut out by a compact open
  subset of the whole space contained in `U`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8
  (for `TopologicalSpace.CompactOpens.exists_subset_preimage_subtypeVal_eq`).
-/

public section

open Set

namespace TopologicalSpace.CompactOpens

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The slice `{y | (x, y) ∈ K}` of a compact open subset `K` of `X × Y` at `x : X`, a compact open
subset of `Y` when the points of `X` are closed. -/
def slice [T1Space X] (K : CompactOpens (X × Y)) (x : X) : CompactOpens Y where
  carrier := Prod.mk x ⁻¹' K
  isCompact' := (isInducing_prodMkRight x).isCompact_preimage
    (isClosedMap_prodMk_left x).isClosed_range K.isCompact
  isOpen' := K.isOpen.preimage (Continuous.prodMk_right x)

section T1Space

variable [T1Space X]

@[simp, norm_cast]
theorem coe_slice (K : CompactOpens (X × Y)) (x : X) :
    (K.slice x : Set Y) = Prod.mk x ⁻¹' K :=
  (rfl)

@[simp]
theorem mem_slice {K : CompactOpens (X × Y)} {x : X} {y : Y} :
    y ∈ K.slice x ↔ (x, y) ∈ K :=
  Iff.rfl

@[simp]
theorem slice_bot (x : X) : (⊥ : CompactOpens (X × Y)).slice x = ⊥ :=
  CompactOpens.ext <| by rw [coe_slice, coe_bot, coe_bot, preimage_empty]

@[simp]
theorem slice_sup (K L : CompactOpens (X × Y)) (x : X) :
    (K ⊔ L).slice x = K.slice x ⊔ L.slice x :=
  CompactOpens.ext <| by simp only [coe_slice, coe_sup, preimage_union]

@[simp]
theorem slice_prod_of_mem {U : CompactOpens X} {x : X} (hx : x ∈ U) (V : CompactOpens Y) :
    (U ×ˢ V).slice x = V :=
  CompactOpens.ext <| by rw [coe_slice, coe_prod, mk_preimage_prod_right hx]

@[simp]
theorem slice_prod_of_notMem {U : CompactOpens X} {x : X} (hx : x ∉ U) (V : CompactOpens Y) :
    (U ×ˢ V).slice x = ⊥ :=
  CompactOpens.ext <| by rw [coe_slice, coe_prod, mk_preimage_prod_right_eq_empty hx, coe_bot]

/-- The slice of a compact open subset `K` of `X × Y` at a point outside the projection of `K` is
empty. -/
theorem slice_eq_bot_of_notMem {K : CompactOpens (X × Y)} {x : X}
    (hx : x ∉ Prod.fst '' (K : Set (X × Y))) : K.slice x = ⊥ :=
  CompactOpens.ext <| by
    rw [coe_bot]
    exact eq_empty_of_forall_notMem fun _ hy ↦ hx ⟨_, hy, rfl⟩

/-- If `K` is the union of the rectangles `W i ×ˢ S i` with pairwise disjoint `W i`, then the
slice of `K` at a point of `W i` is `S i`. -/
theorem slice_eq_of_mem {K : CompactOpens (X × Y)} {ι : Type*} {s : Finset ι}
    {W : ι → CompactOpens X} {S : ι → CompactOpens Y}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set X))
    (hK : ∀ x y, (x, y) ∈ K ↔ ∃ i ∈ s, x ∈ W i ∧ y ∈ S i) {i : ι} (hi : i ∈ s) {x : X}
    (hx : x ∈ W i) : K.slice x = S i := by
  refine CompactOpens.ext (Set.ext fun y ↦ ?_)
  simp only [SetLike.mem_coe, mem_slice, hK]
  refine ⟨?_, fun hy ↦ ⟨i, hi, hx, hy⟩⟩
  rintro ⟨j, hj, hxj, hyj⟩
  rwa [hW.elim_set hi hj x hx hxj]

end T1Space

/-- The slices of a compact open subset of a product of Hausdorff spaces are locally constant. -/
theorem isLocallyConstant_slice [T2Space X] [T2Space Y] (K : CompactOpens (X × Y)) :
    IsLocallyConstant K.slice := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  -- A tube around `{x₀} ×ˢ K_{x₀}` inside `K`, and one around the rest of `{x₀} ×ˢ (snd '' K)`
  -- outside `K`.
  obtain ⟨u, v, hu, -, hxu, hv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (K.slice x₀).isCompact K.isOpen fun p hp ↦ by
      obtain ⟨hx, hy⟩ := mem_prod.1 hp
      rw [← Prod.mk.eta (p := p), mem_singleton_iff.1 hx]
      exact hy
  obtain ⟨u', v', hu', -, hxu', hv', huv'⟩ := generalized_tube_lemma isCompact_singleton
    ((K.isCompact.image continuous_snd).diff (K.slice x₀).isOpen)
    K.isCompact.isClosed.isOpen_compl fun p hp ↦ by
      obtain ⟨hx, -, hy⟩ := mem_prod.1 hp
      rw [← Prod.mk.eta (p := p), mem_singleton_iff.1 hx]
      exact hy
  filter_upwards [hu.mem_nhds (hxu (mem_singleton x₀)), hu'.mem_nhds (hxu' (mem_singleton x₀))]
    with x hx hx'
  refine CompactOpens.ext (Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ huv ⟨hx, hv hy⟩⟩)
  by_contra hy₀
  exact huv' ⟨hx', hv' ⟨⟨_, hy, rfl⟩, hy₀⟩⟩ hy

section T2Space

variable [T2Space X] [T2Space Y]

/-- The finitely many slices of a compact open set `K ⊆ X × Y` at the points of its projection
to `X`. -/
noncomputable def slices (K : CompactOpens (X × Y)) : Finset (CompactOpens Y) :=
  (K.isLocallyConstant_slice.finite_image_of_isCompact (K.isCompact.image continuous_fst)).toFinset

@[simp]
theorem mem_slices {K : CompactOpens (X × Y)} {T : CompactOpens Y} :
    T ∈ K.slices ↔ T ∈ K.slice '' (Prod.fst '' (K : Set (X × Y))) :=
  Set.Finite.mem_toFinset _

/-- The compact open set `{x | K_x = T}` of points of `X` at which `K ⊆ X × Y` has slice `T`, for
`T ≠ ⊥`; it is `⊥` for `T = ⊥`. -/
noncomputable def sliceFiber (K : CompactOpens (X × Y)) (T : CompactOpens Y) : CompactOpens X :=
  K.isLocallyConstant_slice.fiberCompactOpens (K.isCompact.image continuous_fst)
    (fun _ ↦ slice_eq_bot_of_notMem) T

@[simp]
theorem mem_sliceFiber {K : CompactOpens (X × Y)} {T : CompactOpens Y} {x : X} :
    x ∈ K.sliceFiber T ↔ K.slice x = T ∧ T ≠ ⊥ :=
  IsLocallyConstant.mem_fiberCompactOpens ..

/-- A compact open set `K ⊆ X × Y` is the union of the rectangles `K.sliceFiber T ×ˢ T` over its
slices `T`. -/
theorem mem_iff_exists_sliceFiber (K : CompactOpens (X × Y)) (x : X) (y : Y) :
    (x, y) ∈ K ↔ ∃ T ∈ K.slices, x ∈ K.sliceFiber T ∧ y ∈ T :=
  K.isLocallyConstant_slice.mem_iff_exists_fiberCompactOpens _ _ id rfl
    (fun _ _ ↦ mem_slice.symm) (fun _ hx ↦ mem_slices.2 (mem_image_of_mem _ hx)) x y

theorem pairwiseDisjoint_sliceFiber (K : CompactOpens (X × Y)) :
    (K.slices : Set (CompactOpens Y)).PairwiseDisjoint fun T ↦ (K.sliceFiber T : Set X) :=
  IsLocallyConstant.pairwiseDisjoint_fiberCompactOpens _ _ _ _

/-- A compact open set `K ⊆ X × Y` is the finite union of the rectangles `K.sliceFiber T ×ˢ T` over
its slices `T`. -/
theorem eq_finsetSup_sliceFiber_prod (K : CompactOpens (X × Y)) :
    K = K.slices.sup fun T ↦ K.sliceFiber T ×ˢ T := by
  refine CompactOpens.ext (Set.ext fun ⟨x, y⟩ ↦ ?_)
  simp only [coe_finsetSup, coe_prod, mem_iUnion, mem_prod, SetLike.mem_coe, exists_prop]
  exact K.mem_iff_exists_sliceFiber x y

end T2Space

section Swap

/-- The compact open set `{(y, x) | (x, y) ∈ K}` obtained from `K ⊆ X × Y` by exchanging the
factors. -/
def swap (K : CompactOpens (X × Y)) : CompactOpens (Y × X) where
  carrier := Prod.swap ⁻¹' K
  isCompact' := by
    rw [← image_swap_eq_preimage_swap]
    exact K.isCompact.image continuous_swap
  isOpen' := K.isOpen.preimage continuous_swap

@[simp, norm_cast]
theorem coe_swap (K : CompactOpens (X × Y)) : (K.swap : Set (Y × X)) = Prod.swap ⁻¹' K :=
  (rfl)

@[simp]
theorem mem_swap {K : CompactOpens (X × Y)} {p : Y × X} : p ∈ K.swap ↔ p.swap ∈ K :=
  Iff.rfl

@[simp]
theorem swap_swap (K : CompactOpens (X × Y)) : K.swap.swap = K :=
  CompactOpens.ext <| by simp only [coe_swap, preimage_preimage, Prod.swap_swap, preimage_id']

@[simp]
theorem swap_bot : (⊥ : CompactOpens (X × Y)).swap = ⊥ :=
  CompactOpens.ext <| by rw [coe_swap, coe_bot, coe_bot, preimage_empty]

@[simp]
theorem swap_sup (K L : CompactOpens (X × Y)) : (K ⊔ L).swap = K.swap ⊔ L.swap :=
  CompactOpens.ext <| by rw [coe_swap, coe_sup, coe_sup, coe_swap, coe_swap, preimage_union]

@[simp]
theorem swap_prod (U : CompactOpens X) (V : CompactOpens Y) : (U ×ˢ V).swap = V ×ˢ U :=
  CompactOpens.ext <| by rw [coe_swap, coe_prod, coe_prod, preimage_swap_prod]

end Swap

section Prespectral

variable [PrespectralSpace X]

/-- In a prespectral space, every compact open subset `K` of a subspace `Z` contained in an open
set `U` is cut out of `Z` by a compact open subset of `X` contained in `U`. For `U = univ`, every
compact open subset of a subspace is cut out by a compact open subset of the whole space. -/
theorem exists_subset_preimage_subtypeVal_eq {Z U : Set X} (hU : IsOpen U) (hZU : Z ⊆ U)
    (K : CompactOpens Z) :
    ∃ W : CompactOpens X, (W : Set X) ⊆ U ∧ Subtype.val ⁻¹' (W : Set X) = (K : Set Z) := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.1 K.isOpen
  have hKV : Subtype.val '' (K : Set Z) ⊆ V ∩ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by rw [← hVK] at hz; exact hz, hZU z.property⟩
  obtain ⟨W, hWc, hWo, hKW, hWV⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (K.isCompact.image continuous_subtypeVal) (hV.inter hU) hKV
  refine ⟨⟨⟨W, hWc⟩, hWo⟩, hWV.trans inter_subset_right,
    Subset.antisymm ?_ (image_subset_iff.1 hKW)⟩
  rw [← hVK]
  exact preimage_mono (hWV.trans inter_subset_left)

end Prespectral

end TopologicalSpace.CompactOpens
