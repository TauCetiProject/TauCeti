/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finset.NoncommProd
import Mathlib.GroupTheory.Submonoid.Centralizer

/-!
# Reindexing and regrouping products of commuting elements

Mathlib's `Finset.noncommProd` multiplies a finite commuting family in an arbitrary
monoid. Here finite bijections reindex these products, fibers regroup them,
adjoining identity factors preserves them, and inversion in a group inverts each
factor. Regrouping uses `Finset.prod_fiberwise_of_maps_to` in the commutative
submonoid supplied by `Submonoid.isMulCommutative_closure`; finite bijections use
`Multiset.map_eq_map_of_bij_of_nodup`. These formulas allow unordered
simultaneous wall crossings to be restricted, transported and reversed without
choosing an order on the walls.

## Attribution

Adapted in full from `Mei/Data/Finset/NoncommProd.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained.
-/

public section

namespace Finset

variable {α β G : Type*}

/-- Adjoining identity factors preserves an unordered product of commuting elements. -/
theorem noncommProd_subset [Monoid G] {s t : Finset α} (hst : s ⊆ t) (f : α → G)
    (comm : (t : Set α).Pairwise (fun a b => Commute (f a) (f b)))
    (hf : ∀ a ∈ t, a ∉ s → f a = 1) :
    s.noncommProd f (comm.mono (coe_subset.mpr hst)) = t.noncommProd f comm := by
  classical
  have hc : ((s ∪ t \ s : Finset α) : Set α).Pairwise (fun a b => Commute (f a) (f b)) := by
    simpa only [union_sdiff_of_subset hst] using comm
  have hz : (t \ s).noncommProd f (comm.mono (coe_subset.mpr sdiff_subset)) = 1 := by
    simpa using noncommProd_eq_pow_card (t \ s) f _ 1
      (fun a ha => hf a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2)
  have hu := noncommProd_union_of_disjoint (disjoint_sdiff_self_right : Disjoint s (t \ s)) f hc
  simpa only [union_sdiff_of_subset hst, hz, mul_one] using hu.symm

/-- Reindex a product of commuting elements along an embedding. -/
theorem noncommProd_map [Monoid G] (s : Finset α) (e : α ↪ β) (f : β → G)
    (comm : (s.map e : Set β).Pairwise (fun a b => Commute (f a) (f b))) :
    (s.map e).noncommProd f comm = s.noncommProd (fun a => f (e a))
      (fun a ha b hb hab => comm (mem_map.mpr ⟨a, ha, rfl⟩)
        (mem_map.mpr ⟨b, hb, rfl⟩) (e.injective.ne hab)) := by
  simp only [noncommProd, map_val, Multiset.map_map, Function.comp_def]

/-- Reindex a commuting product along a bijection of its finite inventories. -/
theorem noncommProd_bij [Monoid G] {s : Finset α} {t : Finset β}
    (f : α → G) (f' : β → G) (comm) (comm')
    (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (hinj : ∀ a ha b hb, i a ha = i b hb → a = b)
    (hsurj : ∀ b ∈ t, ∃ a ha, i a ha = b)
    (hf : ∀ a ha, f a = f' (i a ha)) :
    s.noncommProd f comm = t.noncommProd f' comm' := by
  have he := Multiset.map_eq_map_of_bij_of_nodup f f' s.nodup t.nodup i hi hinj hsurj hf
  simp only [noncommProd, he]

open scoped IsMulCommutative in
/-- Regroup a finite commuting family into the fibers of a map. Empty fibers
contribute the identity; the target inventory may contain unused indices. -/
theorem noncommProd_fiberwise_of_maps_to [Monoid G] [DecidableEq β]
    (s : Finset α) (t : Finset β) (g : α → β) (f : α → G)
    (comm : (s : Set α).Pairwise (fun a b => Commute (f a) (f b)))
    (hg : ∀ a ∈ s, g a ∈ t) :
    t.noncommProd
      (fun b => (s.filter (g · = b)).noncommProd f
        (comm.mono (by simp only [coe_subset]; exact filter_subset _ _)))
      (fun b _ c _ _ => noncommProd_commute _ _ _ _ fun a ha =>
        (noncommProd_commute _ _ _ _ fun a' ha' =>
          comm.forall₂ (mem_filter.mp ha).1 (mem_filter.mp ha').1).symm) =
      s.noncommProd f comm := by
  classical
  let S := Submonoid.closure (f '' (s : Set α))
  have : IsMulCommutative S := Submonoid.isMulCommutative_closure G (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact comm.forall₂ ha hb)
  let F (a : α) : S := if ha : a ∈ s then
    ⟨f a, Submonoid.subset_closure ⟨a, ha, rfl⟩⟩ else 1
  have hF (a : α) (ha : a ∈ s) : (F a : G) = f a := by simp [F, ha]
  have hfiber (b : β) : S.subtype (∏ a ∈ s.filter (g · = b), F a) =
      (s.filter (g · = b)).noncommProd f
        (comm.mono (by simp only [coe_subset]; exact filter_subset _ _)) := by
    exact (congrArg S.subtype (noncommProd_eq_prod _ _).symm).trans
      ((map_noncommProd _ F _ S.subtype).trans
        (noncommProd_congr rfl (fun a ha => hF a (mem_filter.mp ha).1) _))
  calc
    _ = S.subtype (∏ b ∈ t, ∏ a ∈ s.filter (g · = b), F a) := by
      exact ((congrArg S.subtype (noncommProd_eq_prod _ _).symm).trans
        ((map_noncommProd _ _ _ S.subtype).trans
          (noncommProd_congr rfl (fun b _ => hfiber b) _))).symm
    _ = S.subtype (∏ a ∈ s, F a) :=
      congrArg S.subtype (prod_fiberwise_of_maps_to hg F)
    _ = _ := by
      exact (congrArg S.subtype (noncommProd_eq_prod _ _).symm).trans
        ((map_noncommProd _ F _ S.subtype).trans (noncommProd_congr rfl hF _))

/-- Inverting every member of a commuting family inverts its unordered product. -/
theorem noncommProd_inv [DivisionMonoid G] (s : Finset α) (f : α → G)
    (comm : (s : Set α).Pairwise (fun a b => Commute (f a) (f b))) :
    s.noncommProd (fun a => (f a)⁻¹) (fun _ ha _ hb hab => (comm ha hb hab).inv_inv) =
      (s.noncommProd f comm)⁻¹ := by
  induction s using Finset.cons_induction_on with
  | empty => exact (noncommProd_empty _ _).trans (inv_one.symm)
  | cons a s ha ih =>
    have hc : (s : Set α).Pairwise (fun a b => Commute (f a) (f b)) :=
      comm.mono (fun _ => mem_cons_of_mem)
    calc
      _ = (f a)⁻¹ * s.noncommProd (fun a => (f a)⁻¹)
          (fun _ hx _ hy hxy => (hc hx hy hxy).inv_inv) := noncommProd_cons _ _ _ _ _
      _ = (f a)⁻¹ * (s.noncommProd f hc)⁻¹ := by rw [ih]
      _ = (s.noncommProd f hc)⁻¹ * (f a)⁻¹ :=
        (noncommProd_commute s f hc (f a)
          (fun b hb => comm.forall₂ (mem_cons_self _ _) (mem_cons_of_mem hb))).inv_inv.eq
      _ = _ := by rw [noncommProd_cons, mul_inv_rev]

end Finset
