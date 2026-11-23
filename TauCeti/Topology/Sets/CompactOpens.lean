/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Slices of compact open subsets of a product

A compact open set `K ⊆ X × Y` has, at each point `x : X`, the slice `K_x = {y | (x, y) ∈ K}`.
When the points of `X` are closed, `K_x` is again compact open
(`TopologicalSpace.CompactOpens.slice`), and when `X` and `Y` are Hausdorff, `x ↦ K_x` is locally
constant (`TopologicalSpace.CompactOpens.isLocallyConstant_slice`). This is how a compact open
subset of a product of locally profinite spaces is cut into finitely many rectangles.

This file also records that a compact open set is nonempty exactly when it is not `⊥`
(`TopologicalSpace.CompactOpens.coe_nonempty`), as Mathlib does for `TopologicalSpace.Compacts`.

## Main definitions

* `TopologicalSpace.CompactOpens.slice`: the slice `{y | (x, y) ∈ K}` of a compact open set
  `K ⊆ X × Y` at `x : X`.

## Main results

* `TopologicalSpace.CompactOpens.isLocallyConstant_slice`: the slices of a compact open subset of
  a product of Hausdorff spaces are locally constant.
* `TopologicalSpace.CompactOpens.slice_prod_of_mem`, `TopologicalSpace.CompactOpens.slice_sup`:
  slices of rectangles and of unions.
-/

public section

open Set

namespace TopologicalSpace.CompactOpens

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact open set is nonempty exactly when it is not `⊥`. -/
theorem coe_nonempty {K : CompactOpens X} : (K : Set X).Nonempty ↔ K ≠ ⊥ := by
  rw [← ne_empty_iff_nonempty, ← coe_bot, Ne, Ne, SetLike.coe_set_eq]

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

end TopologicalSpace.CompactOpens
