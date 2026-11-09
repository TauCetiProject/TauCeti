/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Cut
import TauCeti.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Sort

/-!
# Gluing half-diagrams

Two half-diagrams with the same number of defects determine a planar boundary matching:
keep their arcs and join their defects in left-to-right order. The top boundary is read
right-to-left in the cyclic numbering, so the resulting through strands do not cross.
Cutting this matching recovers both halves. Together with uniqueness of cutting, this gives
the through-strand decomposition of planar matchings.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

open Equiv Finset

namespace TauCeti.HalfDiagram

variable {n m k : ℕ}

/-- The order-preserving correspondence between the defects of two half-diagrams with the
same number of defects. -/
def defectOrderIso (B : HalfDiagram n k) (T : HalfDiagram m k) :
    {i : Fin n // B.val i = i} ≃o {j : Fin m // T.val j = j} :=
  (Fintype.orderIsoFinOfCardEq _ (by simpa only [Fintype.card_subtype] using B.2.2)).symm.trans
    (Fintype.orderIsoFinOfCardEq _ (by simpa only [Fintype.card_subtype] using T.2.2))

private def partner (B : HalfDiagram n k) (T : HalfDiagram m k) :
    Fin n ⊕ Fin m → Fin n ⊕ Fin m
  | .inl i => if h : B.val i = i then .inr (B.defectOrderIso T ⟨i, h⟩).val else .inl (B.val i)
  | .inr j => if h : T.val j = j then .inl ((B.defectOrderIso T).symm ⟨j, h⟩).val
      else .inr (T.val j)

private theorem partner_involutive (B : HalfDiagram n k) (T : HalfDiagram m k) :
    Function.Involutive (partner B T) := by
  have hB := Perm.isHalfDiagram_iff.mp B.2.1
  have hT := Perm.isHalfDiagram_iff.mp T.2.1
  rintro (i | j)
  · by_cases hi : B.val i = i
    · simp [partner, hi, (B.defectOrderIso T ⟨i, hi⟩).property]
    · simp [partner, hi, hB.1 i, Ne.symm hi]
  · by_cases hj : T.val j = j
    · simp [partner, hj, ((B.defectOrderIso T).symm ⟨j, hj⟩).property]
    · simp [partner, hj, hT.1 j, Ne.symm hj]

private theorem partner_ne (B : HalfDiagram n k) (T : HalfDiagram m k)
    (x : Fin n ⊕ Fin m) : partner B T x ≠ x := by
  rcases x with i | j <;> simp only [partner] <;> split_ifs <;> simp_all

private def boundary (n m : ℕ) : Fin n ⊕ Fin m ≃ Fin (n + m) :=
  finSumFinRevEquiv n m (n + m) rfl

private theorem boundary_left (i : Fin n) : boundary n m (.inl i) = i.castAdd m := by
  apply Fin.ext
  simp [boundary]

private theorem boundary_right_val (j : Fin m) :
    (boundary n m (.inr j) : ℕ) = n + m - 1 - j := by
  simp only [boundary, finSumFinRevEquiv_inr_val]
  omega

private def gluedPerm (B : HalfDiagram n k) (T : HalfDiagram m k) : Perm (Fin (n + m)) :=
  (boundary n m).permCongr ((partner_involutive B T).toPerm _)

private theorem gluedPerm_boundary (B : HalfDiagram n k) (T : HalfDiagram m k)
    (x : Fin n ⊕ Fin m) :
    gluedPerm B T (boundary n m x) = boundary n m (partner B T x) := by
  simp [gluedPerm]

-- Bottom arcs cannot cross each other or enclose a defect. Through strands preserve
-- the order of their defect endpoints, which is reversed in the top cyclic numbering.
private theorem not_crossing_bottom (B : HalfDiagram n k) (T : HalfDiagram m k) (i j : Fin n)
    (hab : boundary n m (.inl i) < boundary n m (.inl j))
    (hba : boundary n m (.inl j) < boundary n m (partner B T (.inl i))) :
    ¬ boundary n m (partner B T (.inl i)) < boundary n m (partner B T (.inl j)) := by
  have hB := Perm.isHalfDiagram_iff.mp B.2.1
  intro hcross
  by_cases hi : B.val i = i <;> by_cases hj : B.val j = j
  · rw [boundary_left, boundary_left] at hab
    have hij : (⟨i, hi⟩ : {i // B.val i = i}) < ⟨j, hj⟩ := hab
    have he := (B.defectOrderIso T).strictMono hij
    simp only [partner, hi, hj, dite_true, boundary_right_val, Fin.lt_def] at hcross
    have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
    have := (B.defectOrderIso T ⟨j, hj⟩).val.isLt
    have he' : ((B.defectOrderIso T ⟨i, hi⟩).val : ℕ) <
        (B.defectOrderIso T ⟨j, hj⟩).val := he
    omega
  · simp only [partner, hi, hj, dite_true, dite_false, boundary_left,
      boundary_right_val, Fin.lt_def, Fin.val_castAdd] at hcross
    have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
    have := (B.val j).isLt
    omega
  · have hax : i < j := by simpa only [boundary_left, Fin.lt_def, Fin.val_castAdd] using hab
    have hxa : j < B.val i := by
      simpa only [partner, hi, dite_false, boundary_left, Fin.lt_def, Fin.val_castAdd] using hba
    exact hB.2.2 hax hxa hj
  · apply (Perm.isNoncrossingMatching_iff.mp hB.2.1)
    · simpa only [boundary_left, Fin.lt_def, Fin.val_castAdd] using hab
    · simpa only [partner, hi, dite_false, boundary_left, Fin.lt_def, Fin.val_castAdd] using hba
    · simpa only [partner, hi, hj, dite_false, boundary_left,
        Fin.lt_def, Fin.val_castAdd] using hcross

-- A crossing between a bottom-starting strand and a top arc would put a defect
-- strictly inside that top arc, forbidden by the half-diagram condition.
private theorem not_crossing_mixed (B : HalfDiagram n k) (T : HalfDiagram m k)
    (i : Fin n) (j : Fin m)
    (hba : boundary n m (.inr j) < boundary n m (partner B T (.inl i))) :
    ¬ boundary n m (partner B T (.inl i)) < boundary n m (partner B T (.inr j)) := by
  have hT := Perm.isHalfDiagram_iff.mp T.2.1
  intro hcross
  by_cases hi : B.val i = i
  · by_cases hj : T.val j = j
    · simp only [partner, hi, hj, dite_true, boundary_left, boundary_right_val,
        Fin.lt_def, Fin.val_castAdd] at hcross
      have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
      have := ((B.defectOrderIso T).symm ⟨j, hj⟩).val.isLt
      omega
    · have he := (B.defectOrderIso T ⟨i, hi⟩).property
      have h₁ : T.val j < (B.defectOrderIso T ⟨i, hi⟩).val := by
        simp only [partner, hi, hj, dite_true, dite_false, boundary_right_val,
          Fin.lt_def] at hcross
        have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
        have := (T.val j).isLt
        omega
      have h₂ : (B.defectOrderIso T ⟨i, hi⟩).val < T.val (T.val j) := by
        rw [hT.1 j]
        simp only [partner, hi, dite_true, boundary_right_val, Fin.lt_def] at hba
        have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
        have := j.isLt
        omega
      exact hT.2.2 h₁ h₂ he
  · simp only [partner, hi, dite_false, boundary_right_val, boundary_left,
      Fin.lt_def, Fin.val_castAdd] at hba
    have := (B.val i).isLt
    have := j.isLt
    omega

private theorem not_crossing_top (B : HalfDiagram n k) (T : HalfDiagram m k) (i j : Fin m)
    (hab : boundary n m (.inr i) < boundary n m (.inr j))
    (hba : boundary n m (.inr j) < boundary n m (partner B T (.inr i))) :
    ¬ boundary n m (partner B T (.inr i)) < boundary n m (partner B T (.inr j)) := by
  have hT := Perm.isHalfDiagram_iff.mp T.2.1
  intro hcross
  by_cases hi : T.val i = i
  · simp only [partner, hi, dite_true, boundary_right_val, boundary_left,
      Fin.lt_def, Fin.val_castAdd] at hba
    have := ((B.defectOrderIso T).symm ⟨i, hi⟩).val.isLt
    have := j.isLt
    omega
  · by_cases hj : T.val j = j
    · simp only [partner, hi, hj, dite_true, dite_false, boundary_right_val, boundary_left,
        Fin.lt_def, Fin.val_castAdd] at hcross
      have := ((B.defectOrderIso T).symm ⟨j, hj⟩).val.isLt
      have := (T.val i).isLt
      omega
    · have hn := Perm.isNoncrossingMatching_iff.mp hT.2.1
      apply hn (a := T.val j) (b := T.val i)
      · simp only [partner, hi, hj, dite_false, boundary_right_val, Fin.lt_def] at hcross
        have := (T.val i).isLt
        have := (T.val j).isLt
        omega
      · rw [hT.1 j]
        simp only [partner, hi, dite_false, boundary_right_val, Fin.lt_def] at hba
        have := (T.val i).isLt
        have := j.isLt
        omega
      · rw [hT.1 i, hT.1 j]
        simp only [boundary_right_val, Fin.lt_def] at hab
        have := i.isLt
        have := j.isLt
        omega

private theorem gluedPerm_noncrossing (B : HalfDiagram n k) (T : HalfDiagram m k) :
    (gluedPerm B T).IsNoncrossingMatching := by
  rw [Perm.isNoncrossingMatching_iff]
  intro a b hab hba hcross
  obtain ⟨a, rfl⟩ := (boundary n m).surjective a
  obtain ⟨b, rfl⟩ := (boundary n m).surjective b
  rw [gluedPerm_boundary] at hba
  rw [gluedPerm_boundary, gluedPerm_boundary] at hcross
  rcases a with i | i <;> rcases b with j | j
  · exact not_crossing_bottom B T i j hab hba hcross
  · exact not_crossing_mixed B T i j hba hcross
  · simp only [boundary_right_val, boundary_left, Fin.lt_def, Fin.val_castAdd] at hab
    have := i.isLt
    have := j.isLt
    omega
  · exact not_crossing_top B T i j hab hba hcross

/-- Glue two half-diagrams by joining their defects in left-to-right order. The first half
is the bottom boundary, the second is the top boundary, and no closed circles are added. -/
def glue (B : HalfDiagram n k) (T : HalfDiagram m k) : PlanarMatching (n + m) :=
  ⟨⟨gluedPerm B T, isPerfectMatching_iff.mpr ⟨by
      intro a
      obtain ⟨x, rfl⟩ := (boundary n m).surjective a
      simp only [gluedPerm_boundary, partner_involutive B T x], by
      intro a ha
      obtain ⟨x, rfl⟩ := (boundary n m).surjective a
      rw [gluedPerm_boundary] at ha
      exact partner_ne B T x ((boundary n m).injective ha)⟩⟩,
    gluedPerm_noncrossing B T⟩

/-- The bottom partner after gluing: retain an arc, or join a defect to the corresponding
top defect (whose cyclic label is reversed). -/
theorem glue_apply_bottom (B : HalfDiagram n k) (T : HalfDiagram m k) (i : Fin n) :
    (B.glue T).1.val (i.castAdd m) =
      if h : B.val i = i then
        ⟨n + m - 1 - (B.defectOrderIso T ⟨i, h⟩).val, by
          have := (B.defectOrderIso T ⟨i, h⟩).val.isLt
          omega⟩
      else (B.val i).castAdd m := by
  rw [← boundary_left]
  simp only [glue, gluedPerm_boundary, partner]
  split_ifs
  · apply Fin.ext
    exact boundary_right_val _
  · exact boundary_left _

/-- The top partner after gluing, with top indices read left-to-right. -/
theorem glue_apply_top (B : HalfDiagram n k) (T : HalfDiagram m k) (j : Fin m) :
    (B.glue T).1.val ⟨n + m - 1 - j, by omega⟩ =
      if h : T.val j = j then ((B.defectOrderIso T).symm ⟨j, h⟩).val.castAdd m
      else ⟨n + m - 1 - T.val j, by have := (T.val j).isLt; omega⟩ := by
  have hb : (⟨n + m - 1 - j, by omega⟩ : Fin (n + m)) = boundary n m (.inr j) :=
    Fin.ext (boundary_right_val j).symm
  rw [hb]
  simp only [glue, gluedPerm_boundary, partner]
  split_ifs
  · exact boundary_left _
  · apply Fin.ext
    exact boundary_right_val _

/-- Cutting the bottom of a glued matching recovers the first half-diagram. -/
@[simp]
theorem bottomHalf_glue_val (B : HalfDiagram n k) (T : HalfDiagram m k) :
    (TLDiagram.mk (B.glue T) 0).bottomHalf.val = B.val := by
  apply Equiv.ext
  intro i
  rw [TLDiagram.bottomHalf_apply, glue_apply_bottom]
  by_cases hi : B.val i = i
  · simp only [hi, dite_true]
    have := (B.defectOrderIso T ⟨i, hi⟩).val.isLt
    split_ifs
    · omega
    · rfl
  · simp only [hi, dite_false, Fin.val_castAdd, (B.val i).isLt, dite_true]

/-- Cutting the top of a glued matching recovers the second half-diagram. -/
@[simp]
theorem topHalf_glue_val (B : HalfDiagram n k) (T : HalfDiagram m k) :
    (TLDiagram.mk (B.glue T) 0).topHalf.val = T.val := by
  apply Equiv.ext
  intro j
  apply Fin.ext
  simp only [TLDiagram.topHalf_apply, glue_apply_top]
  by_cases hj : T.val j = j
  · simp only [hj, dite_true, Fin.val_castAdd]
    have := ((B.defectOrderIso T).symm ⟨j, hj⟩).val.isLt
    split_ifs
    · omega
    · rfl
  · simp only [hj, dite_false]
    have := (T.val j).isLt
    split_ifs
    · dsimp only
      omega
    · omega

/-- The through strands of a glued matching are precisely the joined defects. -/
@[simp]
theorem through_glue (B : HalfDiagram n k) (T : HalfDiagram m k) :
    (TLDiagram.mk (B.glue T) 0).through = k := by
  have h := (TLDiagram.mk (B.glue T) 0).bottomHalf.property.2
  rw [bottomHalf_glue_val, B.property.2] at h
  exact h.symm

/-- Gluing halves with a cap on the last two points joins the remaining two defects in
order; cyclic top labels run in the opposite direction. -/
example :
    let B : HalfDiagram 4 2 := ⟨swap 2 3, by decide, by decide⟩
    (B.glue B).1.val 0 = 7 ∧ (B.glue B).1.val 1 = 6 ∧
      (B.glue B).1.val 2 = 3 ∧ (B.glue B).1.val 4 = 5 := by
  dsimp only
  let B : HalfDiagram 4 2 := ⟨swap 2 3, by decide, by decide⟩
  have he : B.defectOrderIso B = OrderIso.refl _ := Subsingleton.elim _ _
  have h₀ := glue_apply_bottom B B 0
  have h₁ := glue_apply_bottom B B 1
  have h₂ := glue_apply_bottom B B 2
  have h₃ := glue_apply_top B B 3
  norm_num [he, B, Equiv.swap_apply_def] at h₀ h₁ h₂ h₃
  exact ⟨h₀, h₁, h₂, h₃⟩

end TauCeti.HalfDiagram

namespace TauCeti.PlanarMatching

/-- Cutting a matching with `k` through strands is a bijection with pairs of half-diagrams
having `k` defects. Its inverse joins the corresponding defects in left-to-right order. -/
def throughEquivHalfDiagrams (n m k : ℕ) :
    {x : PlanarMatching (n + m) // (TLDiagram.mk x 0).through = k} ≃
      HalfDiagram n k × HalfDiagram m k where
  toFun x :=
    (⟨(TLDiagram.mk x.val 0).bottomHalf.val, (TLDiagram.mk x.val 0).bottomHalf.property.1,
      (TLDiagram.mk x.val 0).bottomHalf.property.2.trans x.property⟩,
     ⟨(TLDiagram.mk x.val 0).topHalf.val, (TLDiagram.mk x.val 0).topHalf.property.1,
      (TLDiagram.mk x.val 0).topHalf.property.2.trans x.property⟩)
  invFun p := ⟨p.1.glue p.2, p.1.through_glue p.2⟩
  left_inv x := by
    apply Subtype.ext
    apply TLDiagram.matching_eq_of_halves (D := TLDiagram.mk _ 0) (E := TLDiagram.mk x.val 0)
    · exact HalfDiagram.bottomHalf_glue_val _ _
    · exact HalfDiagram.topHalf_glue_val _ _
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (HalfDiagram.bottomHalf_glue_val p.1 p.2)
    · exact Subtype.ext (HalfDiagram.topHalf_glue_val p.1 p.2)

/-- Cutting a matching retains all bottom arcs and turns through strands into defects. -/
@[simp]
theorem throughEquivHalfDiagrams_apply_fst_val {n m k : ℕ}
    (x : {x : PlanarMatching (n + m) // (TLDiagram.mk x 0).through = k}) :
    (throughEquivHalfDiagrams n m k x).1.val = (TLDiagram.mk x.val 0).bottomHalf.val := (rfl)

/-- Cutting a matching retains all top arcs and turns through strands into defects. -/
@[simp]
theorem throughEquivHalfDiagrams_apply_snd_val {n m k : ℕ}
    (x : {x : PlanarMatching (n + m) // (TLDiagram.mk x 0).through = k}) :
    (throughEquivHalfDiagrams n m k x).2.val = (TLDiagram.mk x.val 0).topHalf.val := (rfl)

/-- The inverse of cutting is gluing. -/
@[simp]
theorem throughEquivHalfDiagrams_symm_apply_val {n m k : ℕ}
    (p : HalfDiagram n k × HalfDiagram m k) :
    ((throughEquivHalfDiagrams n m k).symm p).val = p.1.glue p.2 := (rfl)

/-- The number of boundary matchings with `k` through strands is the product of the two
half-diagram counts. Stored circles are not part of this finite count. -/
theorem card_through_eq (n m k : ℕ) :
    Fintype.card {x : PlanarMatching (n + m) // (TLDiagram.mk x 0).through = k} =
      halfCount n k * halfCount m k := by
  rw [Fintype.card_congr (throughEquivHalfDiagrams n m k), Fintype.card_prod,
    card_halfDiagram, card_halfDiagram]

/-- Nine matchings on four bottom and four top points have exactly two through strands. -/
example :
    Fintype.card {x : PlanarMatching (4 + 4) // (TLDiagram.mk x 0).through = 2} = 9 := by
  rw [card_through_eq, halfCount_eq_choose_sub_choose (by decide) (by decide)]
  decide

end TauCeti.PlanarMatching
