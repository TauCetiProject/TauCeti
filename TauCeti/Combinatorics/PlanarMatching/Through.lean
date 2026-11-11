/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.HalfDiagram
public import TauCeti.Combinatorics.PlanarMatching.TLDiagram

/-!
# Cutting diagrams into half-diagrams

Cutting a Temperley–Lieb diagram horizontally leaves a half-diagram on each boundary.
An arc within a boundary keeps its partner, while a through strand becomes a defect.
The number of defects is the number of through strands, independent of the stored circles.
These cuts provide the boundary data for the through-strand factorization and refined count.

The top half is read left to right, so it is obtained by cutting the bottom of the vertically
reflected diagram. In the cyclic boundary numbering, partners of bottom through endpoints
occur in reverse order; in the left-to-right top numbering their order is preserved.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

open Equiv Finset

namespace TauCeti
namespace TLDiagram

variable {n m : ℕ}

/-- The number of strands connecting the bottom to the top. The top boundary starts at
label `n` in the counterclockwise numbering. Closed circles are not counted. -/
def through (D : TLDiagram n m) : ℕ :=
  #{i : Fin n | n ≤ (D.matching.1.val (i.castAdd m) : ℕ)}

/-- The through-strand count is the number of bottom points whose partners lie on the top. -/
theorem through_def (D : TLDiagram n m) :
    D.through = #{i : Fin n | n ≤ (D.matching.1.val (i.castAdd m) : ℕ)} := (rfl)

private def bottomPartner (D : TLDiagram n m) (i : Fin n) : Fin n :=
  if h : (D.matching.1.val (i.castAdd m) : ℕ) < n then
    ⟨D.matching.1.val (i.castAdd m), h⟩ else i

private theorem bottomPartner_of_lt (D : TLDiagram n m) (i : Fin n)
    (h : (D.matching.1.val (i.castAdd m) : ℕ) < n) :
    (D.bottomPartner i).castAdd m = D.matching.1.val (i.castAdd m) := by
  simp [bottomPartner, h]

private theorem bottomPartner_of_le (D : TLDiagram n m) (i : Fin n)
    (h : n ≤ (D.matching.1.val (i.castAdd m) : ℕ)) : D.bottomPartner i = i := by
  simp [bottomPartner, not_lt.mpr h]

private theorem bottomPartner_involutive (D : TLDiagram n m) :
    Function.Involutive D.bottomPartner := by
  intro i
  by_cases h : (D.matching.1.val (i.castAdd m) : ℕ) < n
  · have hi : D.matching.1.val ((D.bottomPartner i).castAdd m) = i.castAdd m := by
      rw [bottomPartner_of_lt D i h, D.matching.1.apply_apply]
    apply Fin.ext
    simpa [hi] using congrArg Fin.val
      (D.bottomPartner_of_lt (D.bottomPartner i) (by simp [hi]))
  · rw [bottomPartner_of_le D i (by omega), bottomPartner_of_le D i (by omega)]

private theorem bottomPartner_eq_self_iff (D : TLDiagram n m) (i : Fin n) :
    D.bottomPartner i = i ↔ n ≤ (D.matching.1.val (i.castAdd m) : ℕ) := by
  refine ⟨fun h => ?_, D.bottomPartner_of_le i⟩
  by_contra! hi
  exact D.matching.1.apply_ne (i.castAdd m) (by rw [← D.bottomPartner_of_lt i hi, h])

private theorem bottomPartner_lt_of_ne (D : TLDiagram n m) (i : Fin n)
    (h : D.bottomPartner i ≠ i) : (D.matching.1.val (i.castAdd m) : ℕ) < n :=
  not_le.mp ((D.bottomPartner_eq_self_iff i).not.mp h)

private theorem bottomPartner_isHalfDiagram (D : TLDiagram n m) :
    ((D.bottomPartner_involutive).toPerm _).IsHalfDiagram := by
  rw [Perm.isHalfDiagram_iff]
  refine ⟨D.bottomPartner_involutive, Perm.isNoncrossingMatching_iff.mpr ?_, ?_⟩ <;>
    simp only [Function.Involutive.coe_toPerm]
  · intro a b hab hba hlt
    have ha := D.bottomPartner_lt_of_ne a (hab.trans hba).ne'
    have hb := D.bottomPartner_lt_of_ne b (hba.trans hlt).ne'
    exact (Perm.isNoncrossingMatching_iff.mp D.matching.2)
      (a := a.castAdd m) (b := b.castAdd m) (by simpa only [Fin.lt_def, Fin.val_castAdd] using hab)
      (by simpa only [← D.bottomPartner_of_lt a ha, Fin.lt_def, Fin.val_castAdd] using hba)
      (by simpa only [← D.bottomPartner_of_lt a ha, ← D.bottomPartner_of_lt b hb,
        Fin.lt_def, Fin.val_castAdd] using hlt)
  · intro a x hax hxa hx
    have ha := D.bottomPartner_lt_of_ne a (hax.trans hxa).ne'
    have hin := D.matching.val_apply_mem_Ioo (a := a.castAdd m) (b := x.castAdd m)
      (by simpa only [Fin.lt_def, Fin.val_castAdd] using hax)
      (by simpa only [← D.bottomPartner_of_lt a ha, Fin.lt_def, Fin.val_castAdd] using hxa)
    have hdef := (D.bottomPartner_eq_self_iff x).mp hx
    have hbound := (D.bottomPartner a).isLt
    rw [← D.bottomPartner_of_lt a ha] at hin
    simp only [Set.mem_Ioo, Fin.lt_def, Fin.val_castAdd] at hin
    omega

/-- The bottom half of a diagram: caps are retained and through strands become defects.
Its points are read left to right, as on the bottom boundary of the original diagram. -/
def bottomHalf (D : TLDiagram n m) : HalfDiagram n D.through :=
  ⟨D.bottomPartner_involutive.toPerm _, D.bottomPartner_isHalfDiagram, by
    simp only [Function.Involutive.coe_toPerm, bottomPartner_eq_self_iff, through_def]⟩

/-- The partner in the bottom half is the original partner for a cap, and the point itself
for a through strand. -/
theorem bottomHalf_apply (D : TLDiagram n m) (i : Fin n) :
    D.bottomHalf.val i =
      if h : (D.matching.1.val (i.castAdd m) : ℕ) < n then
        ⟨D.matching.1.val (i.castAdd m), h⟩ else i := (rfl)

/-- The defects of the bottom half are exactly the bottom endpoints of through strands. -/
@[simp]
theorem bottomHalf_apply_eq_self_iff (D : TLDiagram n m) (i : Fin n) :
    D.bottomHalf.val i = i ↔ n ≤ (D.matching.1.val (i.castAdd m) : ℕ) :=
  D.bottomPartner_eq_self_iff i

/-- A cap keeps its partner when the diagram is cut. -/
theorem castAdd_bottomHalf_apply (D : TLDiagram n m) (i : Fin n)
    (h : (D.matching.1.val (i.castAdd m) : ℕ) < n) :
    (D.bottomHalf.val i).castAdd m = D.matching.1.val (i.castAdd m) :=
  D.bottomPartner_of_lt i h

/-- There are no more through strands than bottom points. -/
theorem through_le_bottom (D : TLDiagram n m) : D.through ≤ n :=
  D.bottomHalf.defects_le

/-- Counting through endpoints in the full cyclic boundary instead of just its bottom row. -/
private theorem through_eq_card_boundary (D : TLDiagram n m) :
    D.through = #{a : Fin (n + m) | (a : ℕ) < n ∧ n ≤ (D.matching.1.val a : ℕ)} := by
  unfold through
  refine Finset.card_bij' (fun i _ => i.castAdd m)
    (fun a ha => ⟨a, (mem_filter.mp ha).2.1⟩) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro a ha
    have h : (⟨(a : ℕ), (mem_filter.mp ha).2.1⟩ : Fin n).castAdd m = a := Fin.ext rfl
    simpa only [mem_filter, mem_univ, true_and, h] using (mem_filter.mp ha).2.2
  · intros; rfl
  · intros; rfl

/-- Turning a diagram upside down preserves its number of through strands. -/
@[simp]
theorem through_verticalReflect (D : TLDiagram n m) :
    (verticalReflect n m D).through = D.through := by
  rw [through_eq_card_boundary, through_eq_card_boundary]
  let e : Fin (n + m) ≃ Fin (m + n) :=
    D.matching.1.val.trans (Fin.revPerm.trans (finCongr (Nat.add_comm n m)))
  symm
  apply Finset.card_equiv e
  intro i
  have he : (e i : ℕ) = n + m - 1 - (D.matching.1.val i : ℕ) := by
    simp [e, Fin.rev, Nat.sub_sub, Nat.add_comm]
  have hp : ((verticalReflect n m D).matching.1.val (e i) : ℕ) =
      n + m - 1 - i := by
    rw [coe_verticalReflect_matching_val_apply]
    have h : (⟨n + m - 1 - (e i : ℕ), by omega⟩ : Fin (n + m)) =
        D.matching.1.val i := by
      apply Fin.ext
      dsimp only
      have := (D.matching.1.val i).isLt
      omega
    rw [h, D.matching.1.apply_apply]
  simp only [mem_filter, mem_univ, true_and, hp, he]
  have := i.isLt
  have := (D.matching.1.val i).isLt
  omega

/-- The top half of a diagram, read left to right: cups are retained and through strands
become defects. It has the same number of defects as the bottom half. -/
def topHalf (D : TLDiagram n m) : HalfDiagram m D.through :=
  ⟨(verticalReflect n m D).bottomHalf.val,
    (verticalReflect n m D).bottomHalf.property.1, by
      simpa only [through_verticalReflect] using
        (verticalReflect n m D).bottomHalf.property.2⟩

/-- Reading the top half left to right is cutting the bottom of the upside-down diagram. -/
theorem topHalf_val (D : TLDiagram n m) :
    D.topHalf.val = (verticalReflect n m D).bottomHalf.val := (rfl)

/-- The top half of the upside-down diagram is the bottom half of the original diagram. -/
@[simp]
theorem topHalf_verticalReflect_val (D : TLDiagram n m) :
    (verticalReflect n m D).topHalf.val = D.bottomHalf.val := by
  rw [topHalf_val]
  exact congrArg (fun E : TLDiagram n m => E.bottomHalf.val) (verticalReflect_verticalReflect D)

/-- The partner in the top half is the original cup partner, read left to right, or the
point itself for a through strand. The cyclic label of `j` is `n + m - 1 - j`. -/
theorem topHalf_apply (D : TLDiagram n m) (j : Fin m) :
    D.topHalf.val j =
      if h : n ≤ (D.matching.1.val ⟨n + m - 1 - j, by omega⟩ : ℕ) then
        ⟨n + m - 1 - (D.matching.1.val ⟨n + m - 1 - j, by omega⟩ : ℕ), by
          have := (D.matching.1.val ⟨n + m - 1 - j, by omega⟩).isLt
          omega⟩ else j := by
  rw [topHalf_val, bottomHalf_apply]
  apply Fin.ext
  have hv := D.coe_verticalReflect_matching_val_apply (j.castAdd n)
  simp only [Fin.val_castAdd] at hv
  have := (D.matching.1.val ⟨n + m - 1 - j, by omega⟩).isLt
  split_ifs <;> simp_all only <;> omega

/-- A top point is a defect of the cut exactly when its original partner is on the bottom.
The index `j` is left-to-right, hence its cyclic label is `n + m - 1 - j`. -/
@[simp]
theorem topHalf_apply_eq_self_iff (D : TLDiagram n m) (j : Fin m) :
    D.topHalf.val j = j ↔
      (D.matching.1.val ⟨n + m - 1 - j, by omega⟩ : ℕ) < n := by
  rw [topHalf_val, bottomHalf_apply_eq_self_iff, coe_verticalReflect_matching_val_apply]
  simp only [Fin.val_castAdd]
  have := (D.matching.1.val ⟨n + m - 1 - j, by omega⟩).isLt
  omega

/-- There are no more through strands than top points. -/
theorem through_le_top (D : TLDiagram n m) : D.through ≤ m :=
  D.topHalf.defects_le

/-- The bottom points not lying on through strands come in pairs. -/
theorem even_bottom_sub_through (D : TLDiagram n m) : Even (n - D.through) :=
  D.bottomHalf.even_sub

/-- The top points not lying on through strands come in pairs. -/
theorem even_top_sub_through (D : TLDiagram n m) : Even (m - D.through) :=
  D.topHalf.even_sub

/-- A diagram with empty bottom boundary has no through strands. -/
@[simp]
theorem through_zero_left (D : TLDiagram 0 m) : D.through = 0 := by
  simp [through_def]

/-- A diagram with empty top boundary has no through strands. -/
@[simp]
theorem through_zero_right (D : TLDiagram n 0) : D.through = 0 :=
  Nat.eq_zero_of_le_zero D.through_le_top

/-- Every strand of the identity diagram goes through. -/
@[simp]
theorem through_id (n : ℕ) : (id n).through = n := by
  rw [through_def]
  have h : ({i : Fin n | n ≤ ((id n).matching.1.val (i.castAdd n) : ℕ)} :
      Finset (Fin n)) = univ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, iff_true, id_matching_val]
    simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castAdd]
    omega
  rw [h, card_univ, Fintype.card_fin]

/-- Cutting the identity leaves all bottom points as defects. -/
@[simp]
theorem bottomHalf_id_val (n : ℕ) : (id n).bottomHalf.val = 1 := by
  apply Equiv.ext
  intro i
  apply (bottomHalf_apply_eq_self_iff _ _).mpr
  simp only [id_matching_val, Fin.revPerm_apply, Fin.val_rev, Fin.val_castAdd]
  omega

/-- Cutting the identity leaves all top points as defects. -/
@[simp]
theorem topHalf_id_val (n : ℕ) : (id n).topHalf.val = 1 := by
  rw [topHalf_val, congrArg (fun E : TLDiagram n n => E.bottomHalf.val) (verticalReflect_id n),
    bottomHalf_id_val]

/-- Stored circles do not affect the through strands or either cut half. -/
example (x : PlanarMatching (n + m)) (c d : ℕ) :
    (TLDiagram.mk x c).through = (TLDiagram.mk x d).through ∧
      (TLDiagram.mk x c).bottomHalf.val = (TLDiagram.mk x d).bottomHalf.val ∧
      (TLDiagram.mk x c).topHalf.val = (TLDiagram.mk x d).topHalf.val := by
  refine ⟨rfl, rfl, ?_⟩
  rw [topHalf_val, topHalf_val]
  apply Equiv.ext
  intro i
  simp only [bottomHalf_apply, matching_verticalReflect]

/-- The cup and cap have no through strands, even though each has a boundary arc. -/
example : cup.through = 0 ∧ cap.through = 0 := by simp

/-- Cutting the nested six-point matching as a `4 → 2` diagram retains the bottom cap
on points `2, 3` and leaves two defects on each boundary. Stored circles are irrelevant. -/
example :
    let D : TLDiagram 4 2 := ⟨PlanarMatching.nested 3, 7⟩
    D.through = 2 ∧ D.bottomHalf.val = swap 2 3 ∧ D.topHalf.val = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [through_def]
    simp only [PlanarMatching.nested_val]
    decide
  · apply Equiv.ext
    intro i
    rw [bottomHalf_apply]
    simp only [PlanarMatching.nested_val]
    revert i
    decide
  · rw [topHalf_val]
    apply Equiv.ext
    intro i
    apply (bottomHalf_apply_eq_self_iff _ _).mpr
    rw [coe_verticalReflect_matching_val_apply]
    simp only [PlanarMatching.nested_val]
    revert i
    decide

end TLDiagram
end TauCeti
