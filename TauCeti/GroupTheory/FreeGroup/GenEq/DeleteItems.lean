/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
import Mathlib.Data.Fin.VecNotation
import TauCeti.Data.Finset.Sort

/-!
# Deleting items of a generalised equation

The removal of a lonely base (Kharlampovich–Myasnikov, §5.1, ET4) and the passage from a
generalised equation `Ω` to the equation without its free variables (§5.2, D4) delete items
of a generalised equation. This file deletes a set `S` of items which meets no variable base
(`TauCeti.GenEq.deleteItems`): the remaining items keep their order, a boundary `j` becomes the
boundary numbered by the remaining items before `j` (`TauCeti.GenEq.collapse`), so that the two
end-points of a deleted item are identified, and the constant bases on deleted items are dropped.

Since no variable base contains a deleted item, the equations of the result are the basic and
boundary equations of `Ω` and the coefficient equations of the remaining items, rewritten in the
remaining items; hence a solution of `Ω` restricts to a solution of the result
(`TauCeti.GenEq.Solution.deleteItems`).

## Main definitions

* `TauCeti.GenEq.collapse`: the new number of a boundary.
* `TauCeti.GenEq.deleteItems`: delete a set of items meeting no variable base.
* `TauCeti.GenEq.Solution.deleteItems`: the restriction of a solution to the remaining items.

## Main results

* `TauCeti.GenEq.map_segment_deleteItems`: a segment of the result, read in the items of `Ω`, is
  the segment of `Ω` between the corresponding boundaries.
* `TauCeti.GenEq.image_equations_deleteItems_subset`,
  `TauCeti.GenEq.equations_subset_union_deleteItems`: the equations of the result, read in the
  items of `Ω`, are the equations of `Ω` other than the coefficient equations of deleted items.
* `TauCeti.GenEq.IsFormallyConsistent.deleteItems`: deleting items preserves formal consistency.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1 (ET4) and §5.2 (D4).
-/

public section

namespace TauCeti

namespace GenEq

open Finset

variable {A : Type*} (Ω : GenEq A)

/-! ### Renumbering the boundaries -/

/-- The number of items outside `S` before the boundary `j`: the number of the boundary `j` after
the items of `S` are deleted. -/
def collapse (S : Finset (Fin Ω.numItems)) (j : ℕ) : ℕ :=
  (Sᶜ.filter fun k : Fin Ω.numItems => (k : ℕ) < j).card

/-- The number of a boundary is at most the number of remaining items. -/
theorem collapse_le_card (S : Finset (Fin Ω.numItems)) (j : ℕ) : Ω.collapse S j ≤ Sᶜ.card :=
  card_le_card (filter_subset _ _)

/-- The boundary `i` comes strictly before the boundary `j` after the deletion exactly when a
remaining item lies between them. -/
theorem collapse_lt_collapse_iff {S : Finset (Fin Ω.numItems)} {i j : ℕ} :
    Ω.collapse S i < Ω.collapse S j ↔ ∃ k ∉ S, i ≤ (k : ℕ) ∧ (k : ℕ) < j := by
  refine ⟨fun h => ?_, fun ⟨k, hk, hik, hkj⟩ => card_lt_card ?_⟩
  · by_contra hne
    refine h.not_ge (card_le_card fun k hk => ?_)
    simp only [mem_filter, mem_compl] at hk ⊢
    exact ⟨hk.1, by_contra fun hik => hne ⟨k, hk.1, not_lt.1 hik, hk.2⟩⟩
  · refine (ssubset_iff_of_subset fun l hl => ?_).2 ⟨k, ?_, ?_⟩
    · simp only [mem_filter] at hl ⊢
      exact ⟨hl.1, by omega⟩
    · simpa [mem_filter] using ⟨hk, hkj⟩
    · simp only [mem_filter, not_and, not_lt]
      exact fun _ => hik

/-- The boundaries are renumbered monotonically. -/
theorem collapse_mono (S : Finset (Fin Ω.numItems)) : Monotone (Ω.collapse S) :=
  fun _ _ hij => card_le_card fun k hk => by
    simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, by omega⟩

/-- Passing a remaining item increases the number of a boundary by one. -/
theorem collapse_succ_of_notMem {S : Finset (Fin Ω.numItems)} {k : Fin Ω.numItems} (hk : k ∉ S) :
    Ω.collapse S (k + 1) = Ω.collapse S k + 1 := by
  rw [collapse, collapse, ← card_insert_of_notMem (s := Sᶜ.filter _) (a := k) (by simp)]
  congr 1
  ext l
  simp only [mem_filter, mem_compl, mem_insert]
  grind [Fin.ext_iff]

/-- Passing a deleted item does not change the number of a boundary: the two end-points of a
deleted item are identified. -/
theorem collapse_succ_of_mem {S : Finset (Fin Ω.numItems)} {k : Fin Ω.numItems} (hk : k ∈ S) :
    Ω.collapse S (k + 1) = Ω.collapse S k := by
  rw [collapse, collapse]
  congr 1
  ext l
  simp only [mem_filter, mem_compl]
  grind [Fin.ext_iff]

/-- The remaining item with number `k` lies after the boundary with number `k`. -/
@[simp]
theorem collapse_orderEmbOfFin (S : Finset (Fin Ω.numItems)) (k : Fin Sᶜ.card) :
    Ω.collapse S (Sᶜ.orderEmbOfFin rfl k) = k :=
  Sᶜ.card_filter_lt_orderEmbOfFin rfl k

/-- The boundary `k` before a remaining item `k` is followed by a remaining item (`k` itself), so
its number is the number of an item of the result. -/
theorem collapse_lt_card {S : Finset (Fin Ω.numItems)} {k : Fin Ω.numItems} (hk : k ∉ S) :
    Ω.collapse S k < Sᶜ.card := by
  have := Ω.collapse_le_card S (k + 1)
  rw [Ω.collapse_succ_of_notMem hk] at this
  omega

/-- Distinct remaining items have distinct numbers. -/
theorem collapse_injOn (S : Finset (Fin Ω.numItems)) :
    Set.InjOn (fun k : Fin Ω.numItems => Ω.collapse S k) (Sᶜ : Finset (Fin Ω.numItems)) := by
  intro k hk l hl h
  rw [coe_compl, Set.mem_compl_iff, mem_coe] at hk hl
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · exact absurd h (Ω.collapse_lt_collapse_iff.2 ⟨k, hk, le_rfl, hkl⟩).ne
  · exact hkl
  · exact absurd h (Ω.collapse_lt_collapse_iff.2 ⟨l, hl, le_rfl, hkl⟩).ne'

/-- A remaining item `k` gets the number `Ω.collapse S k`. -/
@[simp]
theorem orderEmbOfFin_collapse {S : Finset (Fin Ω.numItems)} {k : Fin Ω.numItems} (hk : k ∉ S) :
    Sᶜ.orderEmbOfFin rfl ⟨Ω.collapse S k, Ω.collapse_lt_card hk⟩ = k :=
  Ω.collapse_injOn S (mem_coe.2 (orderEmbOfFin_mem Sᶜ rfl _)) (mem_coe.2 (mem_compl.2 hk))
    (Ω.collapse_orderEmbOfFin S _)

/-- On the boundaries of a variable base meeting no deleted item, the renumbering is strictly
monotone. -/
theorem collapse_strictMonoOn {S : Finset (Fin Ω.numItems)} {μ : Fin Ω.numBases}
    (hμ : Disjoint (Ω.baseItems μ) S) :
    StrictMonoOn (Ω.collapse S) (Set.Icc (Ω.left μ : ℕ) (Ω.right μ)) := by
  rintro a ⟨ha, -⟩ b ⟨-, hb⟩ hab
  exact Ω.collapse_lt_collapse_iff.2 ⟨⟨a, (hab.trans_le hb).trans_le (Ω.right μ).is_le⟩,
    disjoint_left.1 hμ (Ω.mem_baseItems.2 ⟨ha, hab.trans_le hb⟩), le_rfl, hab⟩

/-! ### Deleting items -/

-- Reducible, so that the items of the result are reducibly `Fin Sᶜ.card`: the restricted
-- solutions and the statements comparing `Ω` with the result use this numbering.
/-- Delete a set `S` of items meeting no variable base. The remaining items keep their order,
the item `k` of the result being the item `Sᶜ.orderEmbOfFin rfl k` of `Ω`; the boundary `j` of
`Ω` becomes the boundary `Ω.collapse S j`; the constant bases on the items of `S` are dropped.
The variable bases, their signs and their duality are unchanged. -/
abbrev deleteItems (S : Finset (Fin Ω.numItems)) (hS : ∀ μ, Disjoint (Ω.baseItems μ) S) :
    GenEq A where
  numItems := Sᶜ.card
  numBases := Ω.numBases
  left μ := ⟨Ω.collapse S (Ω.left μ), Nat.lt_succ_of_le (Ω.collapse_le_card S _)⟩
  right μ := ⟨Ω.collapse S (Ω.right μ), Nat.lt_succ_of_le (Ω.collapse_le_card S _)⟩
  left_lt_right μ := Ω.collapse_strictMonoOn (hS μ) ⟨le_rfl, (Ω.left_lt_right μ).le⟩
    ⟨(Ω.left_lt_right μ).le, le_rfl⟩ (Ω.left_lt_right μ)
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.filterMap
    (fun b => if h : b.1 ∈ S then none else some (⟨Ω.collapse S b.1, Ω.collapse_lt_card h⟩, b.2))
    (by
      intro b b' c hb hb'
      by_cases h : b.1 ∈ S
      · simp [h] at hb
      by_cases h' : b'.1 ∈ S
      · simp [h'] at hb'
      simp only [h, h', dite_false, Option.mem_def, Option.some.injEq] at hb hb'
      subst hb
      refine Prod.ext ?_ (Prod.ext_iff.1 hb').2.symm
      rw [← Ω.orderEmbOfFin_collapse h, ← Ω.orderEmbOfFin_collapse h']
      exact congrArg _ (Prod.ext_iff.1 hb').1.symm)
  connections := univ.filter fun d => ∃ c ∈ Ω.connections,
    c.2.1 = d.2.1 ∧ Ω.collapse S c.1 = d.1 ∧ Ω.collapse S c.2.2 = d.2.2
  bounds_of_mem_connections := by
    rintro ⟨p', μ', q'⟩ hd
    obtain ⟨⟨p, μ, q⟩, hc, hμ, hp, hq⟩ := (mem_filter.1 hd).2
    subst hμ
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc
    simp only [Fin.lt_def] at h₁ h₂ h₃ h₄ ⊢
    rw [← hp, ← hq]
    exact ⟨Ω.collapse_strictMonoOn (hS μ) ⟨le_rfl, by omega⟩ ⟨h₁.le, h₂.le⟩ h₁,
      Ω.collapse_strictMonoOn (hS μ) ⟨h₁.le, h₂.le⟩ ⟨by omega, le_rfl⟩ h₂,
      Ω.collapse_strictMonoOn (hS _) ⟨le_rfl, by omega⟩ ⟨h₃.le, h₄.le⟩ h₃,
      Ω.collapse_strictMonoOn (hS _) ⟨h₃.le, h₄.le⟩ ⟨by omega, le_rfl⟩ h₄⟩
  dual_mem_connections := by
    rintro d hd
    obtain ⟨⟨p, μ, q⟩, hc, rfl, hp, hq⟩ := (mem_filter.1 hd).2
    exact mem_filter.2 ⟨mem_univ _, _, Ω.dual_mem_connections _ hc, rfl, hq, hp⟩

variable {Ω} {S : Finset (Fin Ω.numItems)} (hS : ∀ μ, Disjoint (Ω.baseItems μ) S)

/-- The boundary connections of the result are the renumbered boundary connections of `Ω`. -/
theorem mem_connections_deleteItems
    {d : Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)} :
    d ∈ (Ω.deleteItems S hS).connections ↔ ∃ c ∈ Ω.connections,
      c.2.1 = d.2.1 ∧ Ω.collapse S c.1 = d.1 ∧ Ω.collapse S c.2.2 = d.2.2 :=
  mem_filter.trans (and_iff_right (mem_univ d))

/-- The constant bases of the result are the constant bases of `Ω` on the remaining items. -/
theorem mem_constBases_deleteItems {b : Fin Sᶜ.card × (A × Bool)} :
    b ∈ (Ω.deleteItems S hS).constBases ↔ (Sᶜ.orderEmbOfFin rfl b.1, b.2) ∈ Ω.constBases := by
  simp only [mem_filterMap]
  constructor
  · rintro ⟨a, ha, hab⟩
    split_ifs at hab with h
    simp only [Option.some.injEq] at hab
    subst hab
    simpa [Ω.orderEmbOfFin_collapse h] using ha
  · intro hb
    have hb' : Sᶜ.orderEmbOfFin rfl b.1 ∉ S := mem_compl.1 (orderEmbOfFin_mem _ _ _)
    refine ⟨_, hb, ?_⟩
    simp only [hb', ↓reduceDIte]
    exact congrArg some (Prod.ext (Fin.ext (Ω.collapse_orderEmbOfFin S b.1)) rfl)

/-- A variable base contains a remaining item exactly when it contains it in `Ω`. -/
theorem mem_baseItems_deleteItems {μ : Fin Ω.numBases} {k : Fin Sᶜ.card} :
    k ∈ (Ω.deleteItems S hS).baseItems μ ↔ Sᶜ.orderEmbOfFin rfl k ∈ Ω.baseItems μ := by
  have hk : Sᶜ.orderEmbOfFin rfl k ∉ S := mem_compl.1 (orderEmbOfFin_mem _ _ _)
  rw [mem_baseItems, mem_baseItems, ← Ω.collapse_orderEmbOfFin S k]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨l, -, hl₁, hl₂⟩ := Ω.collapse_lt_collapse_iff.1 h₂
    refine ⟨not_lt.1 fun h => h₁.not_gt ?_, by omega⟩
    exact Ω.collapse_lt_collapse_iff.2 ⟨_, hk, le_rfl, h⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Ω.collapse_mono S h₁, Ω.collapse_lt_collapse_iff.2 ⟨_, hk, le_rfl, h₂⟩⟩

/-! ### The equations after deleting items -/

/-- The positive case of `map_segment_deleteItems`, by induction on the right end-point. -/
private theorem map_segment_deleteItems_true (i : ℕ) :
    ∀ j, Disjoint (Ω.sectionItems i j) S →
      ((Ω.deleteItems S hS).segment (Ω.collapse S i) (Ω.collapse S j) true).map
        (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id) = Ω.segment i j true
  | 0, _ => by simp [segment_true, collapse]
  | j + 1, h => by
    have ih := map_segment_deleteItems_true i j (h.mono_left fun k hk => by
      rw [mem_sectionItems] at hk ⊢
      omega)
    rcases lt_or_ge j i with hji | hij
    · -- Both segments are empty.
      have h₁ : Ω.segment i (j + 1) true = [] := by
        rw [← List.length_eq_zero_iff, length_segment]
        omega
      have h₂ : (Ω.deleteItems S hS).segment (Ω.collapse S i) (Ω.collapse S (j + 1)) true = [] := by
        rw [← List.length_eq_zero_iff, length_segment]
        have := Ω.collapse_mono S (show j + 1 ≤ i by omega)
        omega
      rw [h₁, h₂, List.map_nil]
    rcases lt_or_ge j Ω.numItems with hjn | hjn
    · -- The item `hⱼ` is not deleted: both segments grow by one item.
      let k : Fin Ω.numItems := ⟨j, hjn⟩
      have hk : k ∉ S := disjoint_left.1 h (Ω.mem_sectionItems.2 ⟨hij, Nat.lt_succ_self j⟩)
      have hc : Ω.collapse S (j + 1) = Ω.collapse S j + 1 := Ω.collapse_succ_of_notMem hk
      have hlt := Ω.collapse_lt_card hk
      rw [← Ω.segment_append hij j.le_succ hjn, hc,
        ← (Ω.deleteItems S hS).segment_append (Ω.collapse_mono S hij) (Ω.collapse S j).le_succ hlt,
        List.map_append, ih]
      have h₁ : Ω.segment j (j + 1) true = [(Sum.inl k, true)] := Ω.segment_succ k true
      have h₂ : (Ω.deleteItems S hS).segment (Ω.collapse S j) (Ω.collapse S j + 1) true =
          [(Sum.inl ⟨Ω.collapse S k, hlt⟩, true)] :=
        (Ω.deleteItems S hS).segment_succ ⟨Ω.collapse S k, hlt⟩ true
      rw [h₁, h₂]
      simp [Ω.orderEmbOfFin_collapse hk]
    · -- Past the last boundary nothing changes.
      have h₁ : Ω.segment i (j + 1) true = Ω.segment i j true := by
        simp only [segment_true]
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      have h₂ : Ω.collapse S (j + 1) = Ω.collapse S j := by
        refine le_antisymm (not_lt.1 fun hlt => ?_) (Ω.collapse_mono S j.le_succ)
        obtain ⟨l, -, hl, hl'⟩ := Ω.collapse_lt_collapse_iff.1 hlt
        have := l.is_lt
        omega
      rw [h₁, h₂, ih]

/-- A segment of the result between the renumbered boundaries `i` and `j`, read in the items of
`Ω`, is the segment of `Ω` between `i` and `j`, provided that no item between `i` and `j` is
deleted. -/
theorem map_segment_deleteItems {i j : ℕ} (hij : Disjoint (Ω.sectionItems i j) S) (s : Bool) :
    ((Ω.deleteItems S hS).segment (Ω.collapse S i) (Ω.collapse S j) s).map
      (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id) = Ω.segment i j s := by
  cases s
  · rw [segment_false, segment_false, ← map_segment_deleteItems_true hS i j hij]
    simp [FreeGroup.invRev, List.map_reverse]
  · exact map_segment_deleteItems_true hS i j hij

include hS in
/-- A section inside a variable base meets no deleted item. -/
private theorem disjoint_sectionItems {μ : Fin Ω.numBases} {i j : ℕ} (hi : (Ω.left μ : ℕ) ≤ i)
    (hj : j ≤ Ω.right μ) : Disjoint (Ω.sectionItems i j) S :=
  (hS μ).mono_left fun k hk => by
    rw [mem_sectionItems] at hk
    rw [mem_baseItems]
    omega

include hS in
/-- A boundary `p` with `α(μ) ≤ p < β(μ)` is the left end-point of a remaining item. -/
private theorem collapse_succ_of_mem_base {μ : Fin Ω.numBases} {p : ℕ}
    (h₁ : (Ω.left μ : ℕ) ≤ p) (h₂ : p < Ω.right μ) :
    Ω.collapse S (p + 1) = Ω.collapse S p + 1 :=
  Ω.collapse_succ_of_notMem (k := ⟨p, h₂.trans_le (Ω.right μ).is_le⟩)
    (disjoint_left.1 (hS μ) (Ω.mem_baseItems.2 ⟨h₁, h₂⟩))

include hS in
/-- A boundary `p` with `α(μ) ≤ p < β(μ)` with the number of a remaining item `k` is the left
end-point of `k`. -/
private theorem eq_of_collapse_eq {μ : Fin Ω.numBases} {p : ℕ} (h₁ : (Ω.left μ : ℕ) ≤ p)
    (h₂ : p < Ω.right μ) {k : Fin Ω.numItems} (hk : k ∉ S)
    (h : Ω.collapse S p = Ω.collapse S k) : p = k :=
  Fin.mk.inj_iff.1 (Ω.collapse_injOn S (x₁ := ⟨p, h₂.trans_le (Ω.right μ).is_le⟩)
    (mem_coe.2 (mem_compl.2 (disjoint_left.1 (hS μ) (Ω.mem_baseItems.2 ⟨h₁, h₂⟩))))
    (mem_coe.2 (mem_compl.2 hk)) h)

/-- The basic equation of a base of the result, read in the items of `Ω`, is its basic equation
in `Ω`. -/
theorem map_basicEquation_deleteItems (μ : Fin Ω.numBases) :
    Prod.map (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      ((Ω.deleteItems S hS).basicEquation μ) = Ω.basicEquation μ :=
  Prod.ext (by
      simpa using map_segment_deleteItems hS (disjoint_sectionItems hS le_rfl le_rfl) _)
    (by simpa using map_segment_deleteItems hS (disjoint_sectionItems hS le_rfl le_rfl) _)

/-- The coefficient equation `h′ₖ = a` of the result, read in the items of `Ω`, is the coefficient
equation `hₑ = a` of `Ω`, where `e = Sᶜ.orderEmbOfFin rfl k` is the item of `Ω` numbered `k`. -/
theorem map_coeffEquation_deleteItems (b : Fin Sᶜ.card × (A × Bool)) :
    Prod.map (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      ((Ω.deleteItems S hS).coeffEquation b) =
      Ω.coeffEquation (Sᶜ.orderEmbOfFin rfl b.1, b.2) :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a renumbered boundary connection, read in the items of `Ω`, is the
boundary equation of the boundary connection of `Ω`. -/
theorem map_boundaryEquation_deleteItems
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections)
    {d : Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)} (h₁ : c.2.1 = d.2.1)
    (h₂ : Ω.collapse S c.1 = d.1) (h₃ : Ω.collapse S c.2.2 = d.2.2) :
    Prod.map (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      ((Ω.deleteItems S hS).boundaryEquation d) = Ω.boundaryEquation c := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨p', μ', q'⟩ := d
  dsimp only at h₁ h₂ h₃
  subst h₁
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections _ hc
  rw [Fin.lt_def] at hp₁ hp₂ hq₁ hq₂
  refine Prod.ext ?_ ?_
  · rw [Prod.map_fst, boundaryEquation_fst, boundaryEquation_fst, ← h₂]
    exact map_segment_deleteItems hS (disjoint_sectionItems hS le_rfl hp₂.le) true
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Prod.map_snd, boundaryEquation_snd_of_sign_eq Ω hs,
      boundaryEquation_snd_of_sign_eq (Ω.deleteItems S hS) hs, ← h₃]
    exact map_segment_deleteItems hS (disjoint_sectionItems hS le_rfl hq₂.le) true
  · rw [Prod.map_snd, boundaryEquation_snd_of_sign_ne Ω hs,
      boundaryEquation_snd_of_sign_ne (Ω.deleteItems S hS) hs, ← h₃]
    exact map_segment_deleteItems hS (disjoint_sectionItems hS hq₁.le le_rfl) false

/-- The equations of the result, read in the items of `Ω`, are equations of `Ω`. -/
theorem image_equations_deleteItems_subset :
    Prod.map (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id)) ''
      (Ω.deleteItems S hS).equations ⊆ Ω.equations := by
  rintro _ ⟨e, he, rfl⟩
  rcases (mem_equations_iff _).1 he with ⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [map_basicEquation_deleteItems]
    exact Ω.basicEquation_mem_equations μ
  · rw [map_coeffEquation_deleteItems]
    exact Ω.coeffEquation_mem_equations ((mem_constBases_deleteItems hS).1 hb)
  · obtain ⟨c, hc, h₁, h₂, h₃⟩ := (mem_connections_deleteItems hS).1 hd
    rw [map_boundaryEquation_deleteItems hS hc h₁ h₂ h₃]
    exact Ω.boundaryEquation_mem_equations hc

/-- Every equation of `Ω` is an equation of the result read in the items of `Ω`, or the
coefficient equation of a constant base on a deleted item. -/
theorem equations_subset_union_deleteItems :
    Ω.equations ⊆ Prod.map (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id))
      (List.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id)) ''
      (Ω.deleteItems S hS).equations ∪ Ω.coeffEquation '' {b | b ∈ Ω.constBases ∧ b.1 ∈ S} := by
  refine (Ω.forall_mem_equations (P := (· ∈ _))).2 ⟨fun μ => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · exact Or.inl ⟨_, (Ω.deleteItems S hS).basicEquation_mem_equations μ,
      map_basicEquation_deleteItems hS μ⟩
  · by_cases h : b.1 ∈ S
    · exact Or.inr ⟨b, ⟨hb, h⟩, rfl⟩
    · have hb' : ((⟨Ω.collapse S b.1, Ω.collapse_lt_card h⟩ : Fin Sᶜ.card), b.2) ∈
          (Ω.deleteItems S hS).constBases := by
        rw [mem_constBases_deleteItems, Ω.orderEmbOfFin_collapse h]
        exact hb
      refine Or.inl ⟨_, (Ω.deleteItems S hS).coeffEquation_mem_equations hb', ?_⟩
      rw [map_coeffEquation_deleteItems, Ω.orderEmbOfFin_collapse h]
  · have hd : ((⟨Ω.collapse S c.1, Nat.lt_succ_of_le (Ω.collapse_le_card S _)⟩,
        c.2.1, ⟨Ω.collapse S c.2.2, Nat.lt_succ_of_le (Ω.collapse_le_card S _)⟩) :
          Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)) ∈
          (Ω.deleteItems S hS).connections :=
      (mem_connections_deleteItems hS).2 ⟨c, hc, rfl, rfl, rfl⟩
    exact Or.inl ⟨_, (Ω.deleteItems S hS).boundaryEquation_mem_equations hd,
      map_boundaryEquation_deleteItems hS hc rfl rfl rfl⟩

/-! ### Formal consistency and solutions -/

include hS in
/-- Clause 5 of formal consistency for the result: boundary connections at the two ends of a
constant item come from boundary connections of `Ω` at the two ends of the corresponding item. -/
private theorem IsFormallyConsistent.connections_adjacent_deleteItems
    (hΩ : Ω.IsFormallyConsistent) :
    ∀ b ∈ (Ω.deleteItems S hS).constBases, ∀ d ∈ (Ω.deleteItems S hS).connections,
      ∀ d' ∈ (Ω.deleteItems S hS).connections, d.2.1 = d'.2.1 → d.1 = b.1.castSucc →
        d'.1 = b.1.succ → (d.2.2 : ℕ) + 1 = d'.2.2 ∨ (d'.2.2 : ℕ) + 1 = d.2.2 := by
  intro b hb d hd d' hd' hμ hp hp'
  obtain ⟨c, hc, hμc, h₁, h₃⟩ := (mem_connections_deleteItems hS).1 hd
  obtain ⟨c', hc', hμc', h₁', h₃'⟩ := (mem_connections_deleteItems hS).1 hd'
  have hcc : c.2.1 = c'.2.1 := hμc.trans (hμ.trans hμc'.symm)
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections _ hc
  obtain ⟨hp₁', hp₂', hq₁', hq₂'⟩ := Ω.bounds_of_mem_connections _ hc'
  rw [← hcc] at hp₁' hp₂'
  rw [Fin.lt_def] at hp₁ hp₂ hq₁ hq₂ hp₁' hp₂' hq₁' hq₂'
  -- The constant base `b` lies on the remaining item `k`, and `c`, `c'` sit at its ends.
  set k := Sᶜ.orderEmbOfFin rfl b.1
  have hk : k ∉ S := mem_compl.1 (orderEmbOfFin_mem _ _ _)
  have hkb : Ω.collapse S k = b.1 := Ω.collapse_orderEmbOfFin S b.1
  have e₁ : (c.1 : ℕ) = k := eq_of_collapse_eq hS hp₁.le hp₂ hk <| by
    rw [h₁, hp, hkb, Fin.val_castSucc]
  have e₂ : (c'.1 : ℕ) = k + 1 := by
    have := collapse_succ_of_mem_base hS (μ := c.2.1) (p := c'.1 - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega), h₁', hp', Fin.val_succ, ← hkb] at this
    have := eq_of_collapse_eq hS (μ := c.2.1) (p := c'.1 - 1) (by omega) (by omega) hk (by omega)
    omega
  rw [← h₃, ← h₃']
  rcases hΩ.connections_adjacent _ ((mem_constBases_deleteItems hS).1 hb) c hc c' hc' hcc
    (Fin.ext e₁) (Fin.ext e₂) with h | h
  · exact Or.inl (h ▸ (collapse_succ_of_mem_base hS hq₁.le hq₂).symm)
  · exact Or.inr (h ▸ (collapse_succ_of_mem_base hS hq₁'.le hq₂').symm)

/-- Deleting items meeting no variable base preserves formal consistency. -/
theorem IsFormallyConsistent.deleteItems (hΩ : Ω.IsFormallyConsistent) :
    (Ω.deleteItems S hS).IsFormallyConsistent where
  disjoint_of_sign_ne μ h := by
    rcases hΩ.disjoint_of_sign_ne μ h with h' | h'
    · exact Or.inl (Ω.collapse_mono S h')
    · exact Or.inr (Ω.collapse_mono S h')
  connections_monotone_or_antitone d hd d' hd' hμ hp := by
    obtain ⟨c, hc, hμc, h₁, h₃⟩ := (mem_connections_deleteItems hS).1 hd
    obtain ⟨c', hc', hμc', h₁', h₃'⟩ := (mem_connections_deleteItems hS).1 hd'
    have hcc : c.2.1 = c'.2.1 := hμc.trans (hμ.trans hμc'.symm)
    obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc
    obtain ⟨hp₁', hp₂', -, -⟩ := Ω.bounds_of_mem_connections _ hc'
    rw [hcc] at hp₁ hp₂
    -- The renumbering is strictly monotone on the boundaries of the base, so `c.1 ≤ c'.1`.
    have hle : c.1 ≤ c'.1 := not_lt.1 fun hlt => hp.not_gt <| by
      rw [Fin.lt_def, ← h₁, ← h₁']
      exact Ω.collapse_strictMonoOn (hS _) ⟨hp₁'.le, hp₂'.le⟩ ⟨hp₁.le, hp₂.le⟩ hlt
    have := hΩ.connections_monotone_or_antitone c hc c' hc' hcc hle
    rw [← hμc]
    dsimp only
    split_ifs at this ⊢ <;> rw [Fin.le_def, ← h₃, ← h₃'] <;> exact Ω.collapse_mono S this
  eq_of_left_eq d hd h := by
    obtain ⟨c, hc, hμc, h₁, h₃⟩ := (mem_connections_deleteItems hS).1 hd
    rw [← hμc] at h
    -- The left end-points of `c.2.1` and of its dual are the left end-points of remaining items.
    have hleft : Ω.left c.2.1 = Ω.left (Ω.dual c.2.1) := by
      have := Ω.collapse_injOn S
        (by simpa using disjoint_left.1 (hS _) (Ω.left_mem_baseItems c.2.1))
        (by simpa using disjoint_left.1 (hS _) (Ω.left_mem_baseItems (Ω.dual c.2.1)))
        (congrArg Fin.val h)
      exact Fin.ext (Fin.mk.inj_iff.1 this)
    exact Fin.ext (h₁.symm.trans ((congrArg (fun x : Fin _ => Ω.collapse S x)
      (hΩ.eq_of_left_eq c hc hleft)).trans h₃))
  label_eq b hb b' hb' h :=
    hΩ.label_eq _ ((mem_constBases_deleteItems hS).1 hb) _
      ((mem_constBases_deleteItems hS).1 hb') (by rw [h])
  connections_adjacent := hΩ.connections_adjacent_deleteItems hS

namespace Solution

/-- A solution of `Ω` restricts to a solution of `Ω` with a set of items meeting no variable
base deleted. -/
def deleteItems (U : Ω.Solution) : (Ω.deleteItems S hS).Solution :=
  -- Substituting the words of the remaining items into a word of the result is substituting the
  -- words of `U` into that word read in the items of `Ω`.
  have key (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
      FreeGroup.substituteVars (fun k => U.word (Sᶜ.orderEmbOfFin rfl k)) w =
        FreeGroup.substituteVars U.word
          (w.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id)) := by
    simp only [FreeGroup.substituteVars, List.flatMap_map]
    congr 1
    funext ⟨x, b⟩
    cases x <;> rfl
  { word k := U.word (Sᶜ.orderEmbOfFin rfl k)
    isReduced_word k := U.isReduced_word _
    word_ne_nil k := U.word_ne_nil _
    isReduced_subst e he := by
      rw [key, key]
      exact U.isReduced_subst _ (image_equations_deleteItems_subset hS ⟨e, he, rfl⟩)
    subst_eq e he := by
      rw [key, key]
      exact U.subst_eq _ (image_equations_deleteItems_subset hS ⟨e, he, rfl⟩) }

/-- The word of the item `k` of the restricted solution is the word of the item of `Ω` numbered
`k`. -/
@[simp]
theorem deleteItems_word (U : Ω.Solution) (k : Fin Sᶜ.card) :
    (U.deleteItems hS).word k = U.word (Sᶜ.orderEmbOfFin rfl k) :=
  (rfl)

end Solution

/-! ### Example -/

/-- The generalised equation `h₀ = h₂` over `F(a, b)`, with the free item `h₁`. -/
private abbrev freeItemExample : GenEq (Fin 2) where
  numItems := 3
  numBases := 2
  left := ![0, 2]
  right := ![1, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- No variable base of `h₀ = h₂` contains the free item `h₁`. -/
private theorem disjoint_baseItems_freeItemExample (μ : Fin 2) :
    Disjoint (freeItemExample.baseItems μ) {1} := by
  rw [disjoint_singleton_right, mem_baseItems]
  revert μ
  decide

/-- Deleting the free item `h₁` from `h₀ = h₂` leaves two items, and identifies the boundaries
`1` and `2`: the bases become `[0, 1]` and `[1, 2]`, the equation `h′₀ = h′₁`. -/
example : (freeItemExample.deleteItems {1} disjoint_baseItems_freeItemExample).numItems = 2 ∧
    (freeItemExample.deleteItems {1} disjoint_baseItems_freeItemExample).left = ![0, 1] ∧
    (freeItemExample.deleteItems {1} disjoint_baseItems_freeItemExample).right = ![1, 2] := by
  decide

/-- The solution `h₀ = h₂ = a`, `h₁ = b` of `h₀ = h₂`, with `a = 0` and `b = 1`. -/
private def freeItemSolution : freeItemExample.Solution where
  word := ![[(0, true)], [(1, true)], [(0, true)]]
  isReduced_word := by unfold FreeGroup.IsReduced; decide
  word_ne_nil := by decide
  isReduced_subst := (forall_mem_equations _).2 ⟨by
      simp only [basicEquation_fst, basicEquation_snd, segment_true]
      unfold FreeGroup.IsReduced
      decide,
    fun _ hb => absurd hb (Finset.notMem_empty _), fun _ hc => absurd hc (Finset.notMem_empty _)⟩
  subst_eq := (forall_mem_equations _).2 ⟨by
      simp only [basicEquation_fst, basicEquation_snd, segment_true]
      decide,
    fun _ hb => absurd hb (Finset.notMem_empty _), fun _ hc => absurd hc (Finset.notMem_empty _)⟩

/-- Its restriction to the remaining items is the solution `h′₀ = h′₁ = a` of `h′₀ = h′₁`: the
item `h′₁` is the former item `h₂`. -/
example : (freeItemSolution.deleteItems disjoint_baseItems_freeItemExample).word ⟨1, by decide⟩ =
    [(0, true)] := by
  have hk : (2 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
  have h : (⟨1, by decide⟩ : Fin ({1} : Finset (Fin 3))ᶜ.card) =
      ⟨freeItemExample.collapse {1} (2 : Fin 3), freeItemExample.collapse_lt_card hk⟩ :=
    Fin.ext (by decide : 1 = freeItemExample.collapse {1} (2 : Fin 3))
  rw [Solution.deleteItems_word, h, freeItemExample.orderEmbOfFin_collapse hk]
  rfl

end GenEq

end TauCeti
