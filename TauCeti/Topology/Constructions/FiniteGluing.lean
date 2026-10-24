/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Topology.Constructions.Basic

/-!
# Quotients gluing only finitely many points

Let `s` be an equivalence relation on a topological space `X` which identifies only points of a
finite set `t`: whenever `s x y` holds with `x ≠ y`, the point `x` lies in `t`. The quotient
`Quotient s` glues finitely many finite sets of points of `X` together and leaves the rest of `X`
untouched.

The basic example is the topological carrier of a nodal curve: it is the quotient of the
normalization by the relation identifying each node flag with its partner. If `σ` is the
involution of the normalization exchanging paired flags and fixing every other point, this is the
relation `Equiv.Perm.SameCycle.setoid σ`, and `t` is the finite set of points moved by `σ`
(`Equiv.Perm.SameCycle.eq_of_left` supplies the hypothesis below). The results of this file say
that this quotient is a reasonable space: it is Hausdorff when the normalization is, and away from
the glued points it is an open copy of the complement of the flags.

## Main results

* `Setoid.isClosed_setOf_rel`: the relation is a closed subset of `X × X` when `X` is Hausdorff.
* `Setoid.isClosedMap_quotient_mk`: the quotient map is closed when `X` is T₁.
* `Setoid.t2Space_quotient`: the quotient is Hausdorff when `X` is.
* `Setoid.isOpenEmbedding_domRestrict_quotient_mk`: the quotient map restricted to the complement of
  `t` is an open embedding when `X` is T₁; `Setoid.image_quotient_mk_compl` from
  `TauCeti.Topology.Constructions.Basic` identifies its image with the complement of the image of
  `t`. This specializes `Setoid.isOpenEmbedding_domRestrict_quotient_mk_of_isOpen` from the same
  file.

Compactness of the quotient of a compact space is Mathlib's `Quotient.compactSpace`.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} (s : Setoid X) {t : Set X}

/-- A point glued to a different point lies in `t`, whichever side of the relation it is on. -/
private theorem mem_of_rel_of_ne' (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) {x y : X}
    (hxy : s x y) (hne : x ≠ y) : y ∈ t :=
  hst (s.symm hxy) hne.symm

/-- The equivalence class of `x` lies in `insert x t`. -/
private theorem setOf_rel_subset_insert (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) (x : X) :
    {y | s x y} ⊆ insert x t := by
  intro y hxy
  by_cases hne : x = y
  · exact Or.inl hne.symm
  · exact Or.inr (mem_of_rel_of_ne' s hst hxy hne)

/-- If `A ⊆ U` is closed under `s`, then removing from `U` the points of `t` outside `A` leaves a
set closed under `s`. -/
private theorem mem_diff_of_rel (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) {A U : Set X}
    (hA : ∀ ⦃a b⦄, a ∈ A → s a b → b ∈ A) (hAU : A ⊆ U) ⦃x y : X⦄ (hx : x ∈ U \ (t \ A))
    (hxy : s x y) : y ∈ U \ (t \ A) := by
  by_cases hne : x = y
  · exact hne ▸ hx
  · have hxA : x ∈ A := by_contra fun h => hx.2 ⟨hst hxy hne, h⟩
    have hyA : y ∈ A := hA hxA hxy
    exact ⟨hAU hyA, fun h => h.2 hyA⟩

variable [TopologicalSpace X] (ht : t.Finite) (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t)
include ht hst

/-- If an equivalence relation on a Hausdorff space identifies only points of a finite set, then
it is a closed subset of the product. -/
theorem isClosed_setOf_rel [T2Space X] : IsClosed {p : X × X | s p.1 p.2} := by
  have hsub : {p : X × X | s p.1 p.2} = diagonal X ∪ {p ∈ t ×ˢ t | s p.1 p.2} := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_union, mem_diagonal_iff, mem_prod]
    constructor
    · intro hxy
      by_cases hne : x = y
      · exact Or.inl hne
      · exact Or.inr ⟨⟨hst hxy hne, mem_of_rel_of_ne' s hst hxy hne⟩, hxy⟩
    · rintro (rfl | ⟨-, hxy⟩)
      · exact s.refl x
      · exact hxy
  rw [hsub]
  exact isClosed_diagonal.union ((ht.prod ht).subset (sep_subset _ _)).isClosed

/-- If an equivalence relation on a T₁ space identifies only points of a finite set, then the
quotient map is closed. -/
theorem isClosedMap_quotient_mk [T1Space X] : IsClosedMap (Quotient.mk s) := by
  intro C hC
  have hq : IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  rw [← hq.isClosed_preimage]
  have hsub : Quotient.mk s ⁻¹' (Quotient.mk s '' C) = C ∪ {y ∈ t | ∃ x ∈ C, s x y} := by
    refine Subset.antisymm ?_ ?_
    · rintro y ⟨x, hx, hxy⟩
      replace hxy := Quotient.exact hxy
      by_cases hne : x = y
      · exact Or.inl (hne ▸ hx)
      · exact Or.inr ⟨mem_of_rel_of_ne' s hst hxy hne, x, hx, hxy⟩
    · rintro y (hy | ⟨-, x, hx, hxy⟩)
      · exact subset_preimage_image _ _ hy
      · exact ⟨x, hx, Quotient.sound hxy⟩
  rw [hsub]
  exact hC.union (ht.subset (sep_subset _ _)).isClosed

/-- If an equivalence relation on a Hausdorff space identifies only points of a finite set, then
the quotient space is Hausdorff. -/
theorem t2Space_quotient [T2Space X] : T2Space (Quotient s) := by
  refine ⟨fun a b hab => ?_⟩
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  -- Separate the two (finite) classes by open sets, then shrink them to saturated open sets.
  set A := {z | s x z}
  set B := {z | s y z}
  have hA : ∀ ⦃a b⦄, a ∈ A → s a b → b ∈ A := fun _ _ ha hab => s.trans ha hab
  have hB : ∀ ⦃a b⦄, a ∈ B → s a b → b ∈ B := fun _ _ ha hab => s.trans ha hab
  have hAB : Disjoint A B := disjoint_left.2 fun z hxz hyz =>
    hab (Quotient.sound (s.trans hxz (s.symm hyz)))
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    ((ht.insert x).subset (setOf_rel_subset_insert s hst x)).isCompact
    ((ht.insert y).subset (setOf_rel_subset_insert s hst y)).isCompact hAB
  have hU' : IsOpen (U \ (t \ A)) := hU.sdiff (ht.subset sdiff_subset).isClosed
  have hV' : IsOpen (V \ (t \ B)) := hV.sdiff (ht.subset sdiff_subset).isClosed
  refine ⟨_, _, isOpen_image_quotient_mk s hU' (mem_diff_of_rel s hst hA hAU),
    isOpen_image_quotient_mk s hV' (mem_diff_of_rel s hst hB hBV),
    ⟨x, ⟨hAU (s.refl x), fun h => h.2 (s.refl x)⟩, rfl⟩,
    ⟨y, ⟨hBV (s.refl y), fun h => h.2 (s.refl y)⟩, rfl⟩, ?_⟩
  rw [disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
  have hvU := mem_diff_of_rel s hst hA hAU hu (s.symm (Quotient.exact huv))
  exact disjoint_left.1 hUV hvU.1 hv.1

/-- If an equivalence relation on a T₁ space identifies only points of a finite set `t`, then the
quotient map restricted to the complement of `t` is an open embedding. -/
theorem isOpenEmbedding_domRestrict_quotient_mk [T1Space X] :
    IsOpenEmbedding (tᶜ.domRestrict (Quotient.mk s)) :=
  -- Points outside `t` are related only to themselves.
  isOpenEmbedding_domRestrict_quotient_mk_of_isOpen s ht.isClosed.isOpen_compl
    fun _ _ hx hxy => by_contra fun hne => hx (hst hxy hne)

end Setoid
