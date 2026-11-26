/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.Sort
public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
import Mathlib.Data.Fin.VecNotation

/-!
# Deleting items of a generalised equation

The removal of a lonely base (Kharlampovich–Myasnikov, §5.1, ET4) and the passage from a
generalised equation `Ω` to the equation without its free variables (§5.2, D4) delete items
of a generalised equation. This file deletes a set `S` of items which meets no variable base
(`TauCeti.GenEq.deleteItems`): the remaining items keep their order, a boundary `j` becomes the
boundary numbered by the remaining items before `j` (`Finset.collapse`), so that the two
end-points of a deleted item are identified, and the constant bases on deleted items are dropped.

Since no variable base contains a deleted item, the equations of the result, read in the items of
`Ω` (`TauCeti.GenEq.restoreEquation`), are the basic and boundary equations of `Ω` and the
coefficient equations of the remaining items; hence a solution of `Ω` restricts to a solution of
the result (`TauCeti.GenEq.Solution.deleteItems`).

## Main definitions

* `TauCeti.GenEq.deleteItems`: delete a set of items meeting no variable base.
* `TauCeti.GenEq.restoreWord`, `TauCeti.GenEq.restoreEquation`: a word or an equation in the
  remaining items, read in all the items.
* `TauCeti.GenEq.Solution.deleteItems`: the restriction of a solution to the remaining items.

## Main results

* `TauCeti.GenEq.restoreWord_segment_deleteItems`: a segment of the result, read in the items of
  `Ω`, is the segment of `Ω` between the corresponding boundaries, provided that no item between
  these boundaries is deleted.
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

/-- On the boundaries of a variable base meeting no deleted item, the renumbering is strictly
monotone. -/
theorem collapse_strictMonoOn {S : Finset (Fin Ω.numItems)} {μ : Fin Ω.numBases}
    (hμ : Disjoint (Ω.baseItems μ) S) :
    StrictMonoOn S.collapse (Set.Icc (Ω.left μ : ℕ) (Ω.right μ)) := by
  rintro a ⟨ha, -⟩ b ⟨-, hb⟩ hab
  exact collapse_lt_collapse_iff.2 ⟨⟨a, (hab.trans_le hb).trans_le (Ω.right μ).is_le⟩,
    disjoint_left.1 hμ (Ω.mem_baseItems.2 ⟨ha, hab.trans_le hb⟩), le_rfl, hab⟩

/-! ### Deleting items -/

-- Reducible, so that the items of the result are reducibly `Fin Sᶜ.card`: the restricted
-- solutions and the statements comparing `Ω` with the result use this numbering.
/-- Delete a set `S` of items meeting no variable base. The remaining items keep their order,
the item `k` of the result being the item `Sᶜ.orderEmbOfFin rfl k` of `Ω`; the boundary `j` of
`Ω` becomes the boundary `S.collapse j`; the constant bases on the items of `S` are dropped.
The variable bases, their signs and their duality are unchanged. -/
abbrev deleteItems (S : Finset (Fin Ω.numItems)) (hS : ∀ μ, Disjoint (Ω.baseItems μ) S) :
    GenEq A where
  numItems := Sᶜ.card
  numBases := Ω.numBases
  left μ := ⟨S.collapse (Ω.left μ), Nat.lt_succ_of_le (S.collapse_le_card _)⟩
  right μ := ⟨S.collapse (Ω.right μ), Nat.lt_succ_of_le (S.collapse_le_card _)⟩
  left_lt_right μ := Ω.collapse_strictMonoOn (hS μ) ⟨le_rfl, (Ω.left_lt_right μ).le⟩
    ⟨(Ω.left_lt_right μ).le, le_rfl⟩ (Ω.left_lt_right μ)
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.filterMap
    (fun b => if h : b.1 ∈ S then none else some (⟨S.collapse b.1, collapse_lt_card h⟩, b.2))
    (by
      intro b b' c hb hb'
      by_cases h : b.1 ∈ S
      · simp [h] at hb
      by_cases h' : b'.1 ∈ S
      · simp [h'] at hb'
      simp only [h, h', dite_false, Option.mem_def, Option.some.injEq] at hb hb'
      subst hb
      refine Prod.ext ?_ (Prod.ext_iff.1 hb').2.symm
      rw [← orderEmbOfFin_collapse h, ← orderEmbOfFin_collapse h']
      exact congrArg _ (Prod.ext_iff.1 hb').1.symm)
  connections := univ.filter fun d => ∃ c ∈ Ω.connections,
    c.2.1 = d.2.1 ∧ S.collapse c.1 = d.1 ∧ S.collapse c.2.2 = d.2.2
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

/-! ### Reading words in the remaining items -/

section Restore

variable {n : ℕ} (S : Finset (Fin n))

/-- A word in the items left after deleting the items of `S`, read in all the items: the item `k`
becomes the item `Sᶜ.orderEmbOfFin rfl k`. -/
def restoreWord (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) : List ((Fin n ⊕ A) × Bool) :=
  w.map (Prod.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) id)

/-- An equation in the items left after deleting the items of `S`, read in all the items. -/
def restoreEquation (e : List ((Fin Sᶜ.card ⊕ A) × Bool) × List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    List ((Fin n ⊕ A) × Bool) × List ((Fin n ⊕ A) × Bool) :=
  (restoreWord S e.1, restoreWord S e.2)

@[simp]
theorem restoreWord_nil : restoreWord S ([] : List ((Fin Sᶜ.card ⊕ A) × Bool)) = [] :=
  (rfl)

@[simp]
theorem restoreWord_cons_inl (k : Fin Sᶜ.card) (b : Bool) (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    restoreWord S ((Sum.inl k, b) :: w) =
      (Sum.inl (Sᶜ.orderEmbOfFin rfl k), b) :: restoreWord S w :=
  (rfl)

@[simp]
theorem restoreWord_cons_inr (a : A) (b : Bool) (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    restoreWord S ((Sum.inr a, b) :: w) = (Sum.inr a, b) :: restoreWord S w :=
  (rfl)

@[simp]
theorem restoreWord_append (w w' : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    restoreWord S (w ++ w') = restoreWord S w ++ restoreWord S w' :=
  List.map_append

@[simp]
theorem restoreWord_invRev (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    restoreWord S (FreeGroup.invRev w) = FreeGroup.invRev (restoreWord S w) := by
  simp [restoreWord, FreeGroup.invRev, List.map_reverse]

/-- Substituting into a word read in all the items is substituting the words of the remaining
items. -/
@[simp]
theorem substituteVars_restoreWord (U : Fin n → List (A × Bool))
    (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    FreeGroup.substituteVars U (restoreWord S w) =
      FreeGroup.substituteVars (U ∘ Sᶜ.orderEmbOfFin rfl) w :=
  FreeGroup.substituteVars_map _ _ _

/-- In the free group, a word read in all the items is the image of the word under the renaming
`k ↦ Sᶜ.orderEmbOfFin rfl k` of the remaining items. -/
theorem mk_restoreWord (w : List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    FreeGroup.mk (restoreWord S w) =
      FreeGroup.map (Sum.map (Sᶜ.orderEmbOfFin rfl) id) (FreeGroup.mk w) := by
  rw [FreeGroup.map.mk, restoreWord]
  exact congrArg _ (List.map_congr_left fun _ _ => rfl)

@[simp]
theorem restoreEquation_fst
    (e : List ((Fin Sᶜ.card ⊕ A) × Bool) × List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    (restoreEquation S e).1 = restoreWord S e.1 :=
  (rfl)

@[simp]
theorem restoreEquation_snd
    (e : List ((Fin Sᶜ.card ⊕ A) × Bool) × List ((Fin Sᶜ.card ⊕ A) × Bool)) :
    (restoreEquation S e).2 = restoreWord S e.2 :=
  (rfl)

end Restore

variable {Ω} {S : Finset (Fin Ω.numItems)} (hS : ∀ μ, Disjoint (Ω.baseItems μ) S)

/-- Deleting the items of `S` leaves `numItems - #S` items. -/
theorem numItems_deleteItems : (Ω.deleteItems S hS).numItems = Ω.numItems - S.card := by
  simp [card_compl]

/-- Deleting a nonempty set of items decreases the number of items. -/
theorem numItems_deleteItems_lt (hne : S.Nonempty) :
    (Ω.deleteItems S hS).numItems < Ω.numItems := by
  simpa using (card_compl_lt_iff_nonempty S).2 hne

/-- The boundary connections of the result are the renumbered boundary connections of `Ω`. -/
theorem mem_connections_deleteItems
    {d : Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)} :
    d ∈ (Ω.deleteItems S hS).connections ↔ ∃ c ∈ Ω.connections,
      c.2.1 = d.2.1 ∧ S.collapse c.1 = d.1 ∧ S.collapse c.2.2 = d.2.2 :=
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
    simpa [orderEmbOfFin_collapse h] using ha
  · intro hb
    have hb' : Sᶜ.orderEmbOfFin rfl b.1 ∉ S := mem_compl.1 (orderEmbOfFin_mem _ _ _)
    refine ⟨_, hb, ?_⟩
    simp only [hb', ↓reduceDIte]
    exact congrArg some (Prod.ext (Fin.ext (S.collapse_orderEmbOfFin b.1)) rfl)

/-- A variable base contains a remaining item exactly when it contains it in `Ω`. -/
@[simp]
theorem mem_baseItems_deleteItems {μ : Fin Ω.numBases} {k : Fin Sᶜ.card} :
    k ∈ (Ω.deleteItems S hS).baseItems μ ↔ Sᶜ.orderEmbOfFin rfl k ∈ Ω.baseItems μ := by
  have hk : Sᶜ.orderEmbOfFin rfl k ∉ S := mem_compl.1 (orderEmbOfFin_mem _ _ _)
  rw [mem_baseItems, mem_baseItems, ← S.collapse_orderEmbOfFin k]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨l, -, hl₁, hl₂⟩ := collapse_lt_collapse_iff.1 h₂
    refine ⟨not_lt.1 fun h => h₁.not_gt ?_, by omega⟩
    exact collapse_lt_collapse_iff.2 ⟨_, hk, le_rfl, h⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨S.collapse_mono h₁, collapse_lt_collapse_iff.2 ⟨_, hk, le_rfl, h₂⟩⟩

/-! ### The equations after deleting items -/

/-- The positive case of `restoreWord_segment_deleteItems`, by induction on the right
end-point. -/
private theorem restoreWord_segment_deleteItems_true (i : ℕ) :
    ∀ j, Disjoint (Ω.sectionItems i j) S →
      restoreWord S ((Ω.deleteItems S hS).segment (S.collapse i) (S.collapse j) true) =
        Ω.segment i j true
  | 0, _ => by simp [segment_true]
  | j + 1, h => by
    have ih := restoreWord_segment_deleteItems_true i j (h.mono_left fun k hk => by
      rw [mem_sectionItems] at hk ⊢
      omega)
    rcases lt_or_ge j i with hji | hij
    · -- Both segments are empty.
      have h₁ : Ω.segment i (j + 1) true = [] := by
        rw [← List.length_eq_zero_iff, length_segment]
        omega
      have h₂ : (Ω.deleteItems S hS).segment (S.collapse i) (S.collapse (j + 1)) true = [] := by
        rw [← List.length_eq_zero_iff, length_segment]
        have := S.collapse_mono (show j + 1 ≤ i by omega)
        omega
      rw [h₁, h₂, restoreWord_nil]
    rcases lt_or_ge j Ω.numItems with hjn | hjn
    · -- The item `hⱼ` is not deleted: both segments grow by one item.
      let k : Fin Ω.numItems := ⟨j, hjn⟩
      have hk : k ∉ S := disjoint_left.1 h (Ω.mem_sectionItems.2 ⟨hij, Nat.lt_succ_self j⟩)
      have hc : S.collapse (j + 1) = S.collapse j + 1 := collapse_succ_of_notMem hk
      have hlt := collapse_lt_card hk
      rw [← Ω.segment_append hij j.le_succ, hc,
        ← (Ω.deleteItems S hS).segment_append (S.collapse_mono hij) (S.collapse j).le_succ,
        restoreWord_append, ih]
      have h₁ : Ω.segment j (j + 1) true = [(Sum.inl k, true)] := Ω.segment_succ k true
      have h₂ : (Ω.deleteItems S hS).segment (S.collapse j) (S.collapse j + 1) true =
          [(Sum.inl ⟨S.collapse k, hlt⟩, true)] :=
        (Ω.deleteItems S hS).segment_succ ⟨S.collapse k, hlt⟩ true
      rw [h₁, h₂, restoreWord_cons_inl, restoreWord_nil, orderEmbOfFin_collapse hk]
    · -- Past the last boundary nothing changes.
      have h₁ : Ω.segment i (j + 1) true = Ω.segment i j true := by
        simp only [segment_true]
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      have h₂ : S.collapse (j + 1) = S.collapse j := by
        refine le_antisymm (not_lt.1 fun hlt => ?_) (S.collapse_mono j.le_succ)
        obtain ⟨l, -, hl, hl'⟩ := collapse_lt_collapse_iff.1 hlt
        have := l.is_lt
        omega
      rw [h₁, h₂, ih]

/-- A segment of the result between the renumbered boundaries `i` and `j`, read in the items of
`Ω`, is the segment of `Ω` between `i` and `j`, provided that no item between `i` and `j` is
deleted. -/
theorem restoreWord_segment_deleteItems {i j : ℕ} (hij : Disjoint (Ω.sectionItems i j) S)
    (s : Bool) :
    restoreWord S ((Ω.deleteItems S hS).segment (S.collapse i) (S.collapse j) s) =
      Ω.segment i j s := by
  cases s
  · rw [segment_false, segment_false, restoreWord_invRev,
      restoreWord_segment_deleteItems_true hS i j hij]
  · exact restoreWord_segment_deleteItems_true hS i j hij

include hS in
/-- A section inside a variable base meets no deleted item. -/
private theorem disjoint_sectionItems {μ : Fin Ω.numBases} {i j : ℕ} (hi : (Ω.left μ : ℕ) ≤ i)
    (hj : j ≤ Ω.right μ) : Disjoint (Ω.sectionItems i j) S :=
  (hS μ).mono_left (Ω.sectionItems_subset_baseItems hi hj)

include hS in
/-- A boundary `p` with `α(μ) ≤ p < β(μ)` is the left end-point of a remaining item. -/
private theorem collapse_succ_of_mem_base {μ : Fin Ω.numBases} {p : ℕ}
    (h₁ : (Ω.left μ : ℕ) ≤ p) (h₂ : p < Ω.right μ) :
    S.collapse (p + 1) = S.collapse p + 1 :=
  collapse_succ_of_notMem (k := ⟨p, h₂.trans_le (Ω.right μ).is_le⟩)
    (disjoint_left.1 (hS μ) (Ω.mem_baseItems.2 ⟨h₁, h₂⟩))

include hS in
/-- A boundary `p` with `α(μ) ≤ p < β(μ)` with the number of a remaining item `k` is the left
end-point of `k`. -/
private theorem eq_of_collapse_eq {μ : Fin Ω.numBases} {p : ℕ} (h₁ : (Ω.left μ : ℕ) ≤ p)
    (h₂ : p < Ω.right μ) {k : Fin Ω.numItems} (hk : k ∉ S)
    (h : S.collapse p = S.collapse k) : p = k :=
  Fin.mk.inj_iff.1 (S.collapse_injOn (x₁ := ⟨p, h₂.trans_le (Ω.right μ).is_le⟩)
    (mem_coe.2 (mem_compl.2 (disjoint_left.1 (hS μ) (Ω.mem_baseItems.2 ⟨h₁, h₂⟩))))
    (mem_coe.2 (mem_compl.2 hk)) h)

/-- The basic equation of a base of the result, read in the items of `Ω`, is its basic equation
in `Ω`. -/
@[simp]
theorem restoreEquation_basicEquation_deleteItems (μ : Fin Ω.numBases) :
    restoreEquation S ((Ω.deleteItems S hS).basicEquation μ) = Ω.basicEquation μ :=
  Prod.ext
    (by simpa using restoreWord_segment_deleteItems hS (disjoint_sectionItems hS le_rfl le_rfl) _)
    (by simpa using restoreWord_segment_deleteItems hS (disjoint_sectionItems hS le_rfl le_rfl) _)

/-- The coefficient equation `h′ₖ = a` of the result, read in the items of `Ω`, is the coefficient
equation `hₑ = a` of `Ω`, where `e = Sᶜ.orderEmbOfFin rfl k` is the item of `Ω` numbered `k`. -/
@[simp]
theorem restoreEquation_coeffEquation_deleteItems (b : Fin Sᶜ.card × (A × Bool)) :
    restoreEquation S ((Ω.deleteItems S hS).coeffEquation b) =
      Ω.coeffEquation (Sᶜ.orderEmbOfFin rfl b.1, b.2) :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a renumbered boundary connection, read in the items of `Ω`, is the
boundary equation of the boundary connection of `Ω`. -/
theorem restoreEquation_boundaryEquation_deleteItems
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections)
    {d : Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)} (h₁ : c.2.1 = d.2.1)
    (h₂ : S.collapse c.1 = d.1) (h₃ : S.collapse c.2.2 = d.2.2) :
    restoreEquation S ((Ω.deleteItems S hS).boundaryEquation d) = Ω.boundaryEquation c := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨p', μ', q'⟩ := d
  dsimp only at h₁ h₂ h₃
  subst h₁
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections _ hc
  rw [Fin.lt_def] at hp₁ hp₂ hq₁ hq₂
  refine Prod.ext ?_ ?_
  · rw [restoreEquation_fst, boundaryEquation_fst, boundaryEquation_fst, ← h₂]
    exact restoreWord_segment_deleteItems hS (disjoint_sectionItems hS le_rfl hp₂.le) true
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [restoreEquation_snd, boundaryEquation_snd_of_sign_eq Ω hs,
      boundaryEquation_snd_of_sign_eq (Ω.deleteItems S hS) hs, ← h₃]
    exact restoreWord_segment_deleteItems hS (disjoint_sectionItems hS le_rfl hq₂.le) true
  · rw [restoreEquation_snd, boundaryEquation_snd_of_sign_ne Ω hs,
      boundaryEquation_snd_of_sign_ne (Ω.deleteItems S hS) hs, ← h₃]
    exact restoreWord_segment_deleteItems hS (disjoint_sectionItems hS hq₁.le le_rfl) false

/-- The equations of the result, read in the items of `Ω`, are equations of `Ω`. -/
theorem image_equations_deleteItems_subset :
    restoreEquation S '' (Ω.deleteItems S hS).equations ⊆ Ω.equations := by
  rintro _ ⟨e, he, rfl⟩
  rcases (mem_equations_iff _).1 he with ⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [restoreEquation_basicEquation_deleteItems]
    exact Ω.basicEquation_mem_equations μ
  · rw [restoreEquation_coeffEquation_deleteItems]
    exact Ω.coeffEquation_mem_equations ((mem_constBases_deleteItems hS).1 hb)
  · obtain ⟨c, hc, h₁, h₂, h₃⟩ := (mem_connections_deleteItems hS).1 hd
    rw [restoreEquation_boundaryEquation_deleteItems hS hc h₁ h₂ h₃]
    exact Ω.boundaryEquation_mem_equations hc

/-- Every equation of `Ω` is an equation of the result read in the items of `Ω`, or the
coefficient equation of a constant base on a deleted item. -/
theorem equations_subset_union_deleteItems :
    Ω.equations ⊆ restoreEquation S '' (Ω.deleteItems S hS).equations ∪
      Ω.coeffEquation '' {b | b ∈ Ω.constBases ∧ b.1 ∈ S} := by
  refine (Ω.forall_mem_equations (P := (· ∈ _))).2 ⟨fun μ => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · exact Or.inl ⟨_, (Ω.deleteItems S hS).basicEquation_mem_equations μ,
      restoreEquation_basicEquation_deleteItems hS μ⟩
  · by_cases h : b.1 ∈ S
    · exact Or.inr ⟨b, ⟨hb, h⟩, rfl⟩
    · have hb' : ((⟨S.collapse b.1, collapse_lt_card h⟩ : Fin Sᶜ.card), b.2) ∈
          (Ω.deleteItems S hS).constBases := by
        rw [mem_constBases_deleteItems, orderEmbOfFin_collapse h]
        exact hb
      refine Or.inl ⟨_, (Ω.deleteItems S hS).coeffEquation_mem_equations hb', ?_⟩
      rw [restoreEquation_coeffEquation_deleteItems, orderEmbOfFin_collapse h]
  · have hd : ((⟨S.collapse c.1, Nat.lt_succ_of_le (S.collapse_le_card _)⟩,
        c.2.1, ⟨S.collapse c.2.2, Nat.lt_succ_of_le (S.collapse_le_card _)⟩) :
          Fin (Sᶜ.card + 1) × Fin Ω.numBases × Fin (Sᶜ.card + 1)) ∈
          (Ω.deleteItems S hS).connections :=
      (mem_connections_deleteItems hS).2 ⟨c, hc, rfl, rfl, rfl⟩
    exact Or.inl ⟨_, (Ω.deleteItems S hS).boundaryEquation_mem_equations hd,
      restoreEquation_boundaryEquation_deleteItems hS hc rfl rfl rfl⟩

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
  have hkb : S.collapse k = b.1 := S.collapse_orderEmbOfFin b.1
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
    · exact Or.inl (S.collapse_mono h')
    · exact Or.inr (S.collapse_mono h')
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
    split_ifs at this ⊢ <;> rw [Fin.le_def, ← h₃, ← h₃'] <;> exact S.collapse_mono this
  eq_of_left_eq d hd h := by
    obtain ⟨c, hc, hμc, h₁, h₃⟩ := (mem_connections_deleteItems hS).1 hd
    rw [← hμc] at h
    -- The left end-points of `c.2.1` and of its dual are the left end-points of remaining items.
    have hleft : Ω.left c.2.1 = Ω.left (Ω.dual c.2.1) := by
      have := S.collapse_injOn
        (by simpa using disjoint_left.1 (hS _) (Ω.left_mem_baseItems c.2.1))
        (by simpa using disjoint_left.1 (hS _) (Ω.left_mem_baseItems (Ω.dual c.2.1)))
        (congrArg Fin.val h)
      exact Fin.ext (Fin.mk.inj_iff.1 this)
    exact Fin.ext (h₁.symm.trans ((congrArg (fun x : Fin _ => S.collapse x)
      (hΩ.eq_of_left_eq c hc hleft)).trans h₃))
  label_eq b hb b' hb' h :=
    hΩ.label_eq _ ((mem_constBases_deleteItems hS).1 hb) _
      ((mem_constBases_deleteItems hS).1 hb') (by rw [h])
  connections_adjacent := hΩ.connections_adjacent_deleteItems hS

namespace Solution

/-- A solution of `Ω` restricts to a solution of `Ω` with a set of items meeting no variable
base deleted. -/
def deleteItems (U : Ω.Solution) : (Ω.deleteItems S hS).Solution where
  word := U.word ∘ Sᶜ.orderEmbOfFin rfl
  isReduced_word k := U.isReduced_word _
  word_ne_nil k := U.word_ne_nil _
  isReduced_subst e he := by
    simpa only [restoreEquation_fst, restoreEquation_snd, substituteVars_restoreWord] using
      U.isReduced_subst _ (image_equations_deleteItems_subset hS ⟨e, he, rfl⟩)
  subst_eq e he := by
    simpa only [restoreEquation_fst, restoreEquation_snd, substituteVars_restoreWord] using
      U.subst_eq _ (image_equations_deleteItems_subset hS ⟨e, he, rfl⟩)

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
  refine ⟨by decide, ?_, ?_⟩ <;>
    simp only [funext_iff, Fin.forall_fin_two, Fin.ext_iff, collapse_def] <;> decide

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
      ⟨({1} : Finset (Fin 3)).collapse (2 : Fin 3), collapse_lt_card hk⟩ :=
    Fin.ext ((by rw [collapse_def]; decide) : 1 = ({1} : Finset (Fin 3)).collapse (2 : Fin 3))
  rw [Solution.deleteItems_word, h, orderEmbOfFin_collapse hk]
  rfl

end GenEq

end TauCeti
