/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms

/-!
# The number of distinct forms of a system of linear forms

A system of linear forms for the Subspace Theorem over a number field `K` assigns forms
`L v i`, `i : ι`, to every infinite place `v` of `K` and to every place `v` of a finite set `S₀`
of finite places. The same form may occur at many places: the coordinate forms, for instance,
can be repeated at arbitrarily many finite places. The proof of the Subspace Theorem imposes the
vanishing conditions on its auxiliary polynomial once per *distinct* form, so the length of the
chains of subspaces that the proof rules out depends on the number of distinct forms, not on the
number of places.

This file defines the set `TauCeti.NumberField.formSet S₀ L` of forms occurring at the infinite
places and the places of `S₀`, and its cardinality `TauCeti.NumberField.formCount S₀ L`. With
`t` the number of places, `formCount S₀ L ≤ card ι * t` (`TauCeti.NumberField.formCount_le`). A
system with the same forms at every place has at most `card ι` of them, however large `S₀` is
(`TauCeti.NumberField.formCount_const_le`), so the number of places is not bounded in terms of the
number of distinct forms. Passing to the `p`-th exterior power replaces each family
`L v` by its wedges `wedgeForms (L v) p`. Each of them is the wedge of a `p`-tuple of the original
forms, so `formCount S₀ (fun v ↦ wedgeForms (L v) p) ≤ formCount S₀ L ^ p`
(`TauCeti.NumberField.formCount_wedgeForms_le`): the parameter bounding the number of distinct
forms is raised to the power `p`, independently of the number of places.

## Main definitions

* `TauCeti.NumberField.formSet S₀ L`: the forms `L v i` at the infinite places and the places of
  `S₀`.
* `TauCeti.NumberField.formCount S₀ L`: the number of these forms.

## Main results

* `TauCeti.NumberField.formCount_le`: at most `card ι` distinct forms per place.
* `TauCeti.NumberField.formCount_const_le`: the same forms at every place count once.
* `TauCeti.NumberField.formCount_wedgeForms_le`: the wedges of degree `p` of a system have at most
  `formCount S₀ L ^ p` distinct forms.

## References

* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002), 21–127, for imposing the conditions on the auxiliary
  polynomial once per distinct form.
-/

public section

open NumberField Set

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι M : Type*}

/-- **The forms of a system** at the infinite places and the places of `S₀`: the set of all
`L v i` with `v` an infinite place or a place of `S₀`. The values of `L` at other absolute values
do not contribute. -/
def formSet (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) : Set M :=
  (⋃ v : InfinitePlace K, range (L v.val)) ∪ ⋃ v ∈ S₀, range (L v.val)

/-- Membership in the set of forms of a system, unfolded. -/
@[simp]
theorem mem_formSet {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → M} {l : M} :
    l ∈ formSet S₀ L ↔ (∃ (v : InfinitePlace K) (i : ι), L v.val i = l) ∨
      ∃ v ∈ S₀, ∃ i : ι, L v.val i = l := by
  simp [formSet]

/-- A form at an infinite place belongs to the set of forms of the system. -/
theorem apply_mem_formSet_of_infinitePlace (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → M) (v : InfinitePlace K) (i : ι) : L v.val i ∈ formSet S₀ L :=
  mem_formSet.mpr (Or.inl ⟨v, i, rfl⟩)

/-- A form at a place of `S₀` belongs to the set of forms of the system. -/
theorem apply_mem_formSet_of_mem {S₀ : Finset (FinitePlace K)} (L : AbsoluteValue K ℝ → ι → M)
    {v : FinitePlace K} (hv : v ∈ S₀) (i : ι) : L v.val i ∈ formSet S₀ L :=
  mem_formSet.mpr (Or.inr ⟨v, hv, i, rfl⟩)

/-- The set of forms depends on the system only at the infinite places and the places of `S₀`. -/
theorem formSet_congr {S₀ : Finset (FinitePlace K)} {L L' : AbsoluteValue K ℝ → ι → M}
    (hinf : ∀ v : InfinitePlace K, L v.val = L' v.val) (hfin : ∀ v ∈ S₀, L v.val = L' v.val) :
    formSet S₀ L = formSet S₀ L' := by
  ext l
  simp only [mem_formSet]
  refine or_congr (exists_congr fun v ↦ ?_) (exists_congr fun v ↦ ?_)
  · rw [hinf v]
  · exact ⟨fun ⟨hv, h⟩ ↦ ⟨hv, hfin v hv ▸ h⟩, fun ⟨hv, h⟩ ↦ ⟨hv, (hfin v hv).symm ▸ h⟩⟩

/-- **A system with the same forms at every place** has exactly those forms, however many places
`S₀` contains. -/
@[simp]
theorem formSet_const (S₀ : Finset (FinitePlace K)) (l : ι → M) :
    formSet S₀ (fun _ ↦ l) = range l := by
  rw [formSet, iUnion_const, union_eq_left]
  exact iUnion₂_subset fun _ _ ↦ subset_rfl

/-- Enlarging the set of finite places can only add forms. -/
theorem formSet_mono {S₀ S₁ : Finset (FinitePlace K)} (h : S₀ ⊆ S₁)
    (L : AbsoluteValue K ℝ → ι → M) : formSet S₀ L ⊆ formSet S₁ L :=
  union_subset_union_right _ (biUnion_subset_biUnion_left (by simpa using h))

/-- The set of forms of a system is the range of a function on the pairs of a place and an index,
the places being the infinite places and the places of `S₀`. -/
theorem formSet_eq_range (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) :
    formSet S₀ L = range (Sum.elim (fun p : InfinitePlace K × ι ↦ L p.1.val p.2)
      fun p : S₀ × ι ↦ L p.1.val.val p.2) := by
  ext l
  simp only [mem_formSet, mem_range, Sum.exists, Sum.elim_inl, Sum.elim_inr, Prod.exists,
    Subtype.exists]
  refine or_congr Iff.rfl ⟨fun ⟨v, hv, i, h⟩ ↦ ⟨v, hv, i, h⟩, fun ⟨v, hv, i, h⟩ ↦ ⟨v, hv, i, h⟩⟩

/-- A system with finitely many forms per place has finitely many forms. -/
theorem finite_formSet [Finite ι] (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) :
    (formSet S₀ L).Finite := by
  rw [formSet_eq_range]
  exact finite_range _

/-- **The number of distinct forms of a system** at the infinite places and the places of `S₀`.
It is `0` when there are infinitely many, which cannot happen for a finite index type
(`TauCeti.NumberField.finite_formSet`). -/
noncomputable def formCount (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) : ℕ :=
  (formSet S₀ L).ncard

/-- The number of distinct forms is the cardinality of the set of forms. -/
theorem formCount_def (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) :
    formCount S₀ L = (formSet S₀ L).ncard :=
  (rfl)

/-- **At most `card ι` distinct forms per place**: a system has at most `card ι · t` distinct
forms, where `t` is the number of infinite places plus the number of places of `S₀`. -/
theorem formCount_le [Fintype ι] (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → M) :
    formCount S₀ L ≤ Fintype.card ι * (Fintype.card (InfinitePlace K) + S₀.card) := by
  rw [formCount_def, formSet_eq_range, ← Nat.card_coe_set_eq]
  refine (Finite.card_range_le _).trans_eq ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_coe]
  ring

/-- **The same forms at every place** count once: a system with the same `card ι` forms at every
place has at most `card ι` distinct forms, independently of `S₀`. -/
theorem formCount_const_le [Fintype ι] (S₀ : Finset (FinitePlace K)) (l : ι → M) :
    formCount S₀ (fun _ ↦ l) ≤ Fintype.card ι := by
  rw [formCount_def, formSet_const, ← Nat.card_coe_set_eq]
  exact (Finite.card_range_le l).trans_eq Nat.card_eq_fintype_card

/-- Enlarging the set of finite places can only increase the number of distinct forms. -/
theorem formCount_mono [Finite ι] {S₀ S₁ : Finset (FinitePlace K)} (h : S₀ ⊆ S₁)
    (L : AbsoluteValue K ℝ → ι → M) : formCount S₀ L ≤ formCount S₁ L :=
  ncard_le_ncard (formSet_mono h L) (finite_formSet S₁ L)

/-- **Distinct wedge forms**: the wedges of degree `p` of a system of forms on `ι → R`, indexed
by a finite type `κ`, have at most `formCount S₀ L ^ p` distinct members, since each is the wedge
of a `p`-tuple of forms of the system. -/
theorem formCount_wedgeForms_le {R : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]
    {κ : Type*} [Finite κ] [LinearOrder κ] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Module.Dual R (ι → R)) (p : ℕ) :
    formCount S₀ (fun v ↦ wedgeForms (L v) p) ≤ formCount S₀ L ^ p := by
  have hfin := finite_formSet S₀ L
  have : Finite (formSet S₀ L) := hfin.to_subtype
  -- Every wedge form is the wedge of a `p`-tuple of forms of the system.
  have hsub : formSet S₀ (fun v ↦ wedgeForms (L v) p) ⊆
      range fun t : Fin p → formSet S₀ L ↦ wedgeForm (fun a ↦ (t a : Module.Dual R (ι → R))) := by
    intro l hl
    have key (w : AbsoluteValue K ℝ) (hw : ∀ i, L w i ∈ formSet S₀ L) (T) :
        wedgeForms (L w) p T ∈ range fun t : Fin p → formSet S₀ L ↦
          wedgeForm (fun a ↦ (t a : Module.Dual R (ι → R))) :=
      ⟨fun a ↦ ⟨_, hw (powersetCard.ofFinEmbEquiv.symm T a)⟩,
        by simp only [wedgeForms_apply, Function.comp_def]⟩
    rcases mem_formSet.mp hl with ⟨v, T, rfl⟩ | ⟨v, hv, T, rfl⟩
    · exact key v.val (apply_mem_formSet_of_infinitePlace S₀ L v) T
    · exact key v.val (apply_mem_formSet_of_mem L hv) T
  rw [formCount_def, formCount_def]
  refine (ncard_le_ncard hsub (finite_range _)).trans ?_
  rw [← Nat.card_coe_set_eq]
  refine (Finite.card_range_le _).trans_eq ?_
  rw [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]

end TauCeti.NumberField
