/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Through
import Mathlib.Order.Hom.Set

/-!
# Uniqueness of cutting a Temperley–Lieb diagram

The through strands induce an order isomorphism between the defects of the bottom and top
halves, both read left to right. Thus the two halves determine all the strands: the caps and
cups are retained by cutting, and the through strands join corresponding defects in order.
Together with the stored circle count, the halves determine the entire diagram.

`TauCeti.TLDiagram.throughOrderIso` records the correspondence of defects.
`TauCeti.TLDiagram.ext_halves` is the uniqueness statement needed to reconstruct diagrams from their
halves; it does not assert existence of a gluing operation.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

namespace TauCeti.TLDiagram

open Equiv

variable {n m : ℕ}

private def throughTop (D : TLDiagram n m)
    (i : {i : Fin n // D.bottomHalf.val i = i}) : Fin m :=
  ⟨n + m - 1 - (D.matching.1.val (i.val.castAdd m) : ℕ), by
    have hi := (D.bottomHalf_apply_eq_self_iff i).mp i.property
    have := (D.matching.1.val (i.val.castAdd m)).isLt
    omega⟩

private theorem throughTop_boundary (D : TLDiagram n m)
    (i : {i : Fin n // D.bottomHalf.val i = i}) :
    (⟨n + m - 1 - (D.throughTop i : ℕ), by omega⟩ : Fin (n + m)) =
      D.matching.1.val (i.val.castAdd m) := by
  apply Fin.ext
  have := (D.matching.1.val (i.val.castAdd m)).isLt
  simp only [throughTop]
  omega

private theorem throughTop_defect (D : TLDiagram n m)
    (i : {i : Fin n // D.bottomHalf.val i = i}) :
    D.topHalf.val (D.throughTop i) = D.throughTop i := by
  rw [topHalf_apply_eq_self_iff, throughTop_boundary, D.matching.1.apply_apply]
  exact i.val.isLt

private def throughBottom (D : TLDiagram n m)
    (j : {j : Fin m // D.topHalf.val j = j}) : Fin n :=
  ⟨D.matching.1.val ⟨n + m - 1 - j.val, by omega⟩,
    (D.topHalf_apply_eq_self_iff j).mp j.property⟩

private theorem throughBottom_boundary (D : TLDiagram n m)
    (j : {j : Fin m // D.topHalf.val j = j}) :
    (D.throughBottom j).castAdd m =
      D.matching.1.val ⟨n + m - 1 - j.val, by omega⟩ := by
  rfl

private theorem throughBottom_defect (D : TLDiagram n m)
    (j : {j : Fin m // D.topHalf.val j = j}) :
    D.bottomHalf.val (D.throughBottom j) = D.throughBottom j := by
  rw [bottomHalf_apply_eq_self_iff, throughBottom_boundary, D.matching.1.apply_apply]
  have := j.val.isLt
  dsimp only
  omega

private theorem throughTop_strictMono (D : TLDiagram n m) :
    StrictMono D.throughTop := by
  intro i j hij
  have hi := (D.bottomHalf_apply_eq_self_iff i).mp i.property
  have hj := (D.bottomHalf_apply_eq_self_iff j).mp j.property
  have hne : D.matching.1.val (i.val.castAdd m) ≠
      D.matching.1.val (j.val.castAdd m) := by
    intro h
    have := D.matching.1.val.injective h
    have : i.val = j.val := by
      apply Fin.ext
      exact congrArg (fun a : Fin (n + m) => a.val) this
    exact (ne_of_lt hij) (Subtype.ext this)
  have hnc := Perm.isNoncrossingMatching_iff.mp D.matching.2
  have hnot : ¬ D.matching.1.val (i.val.castAdd m) <
      D.matching.1.val (j.val.castAdd m) := by
    intro h
    exact hnc (a := i.val.castAdd m) (b := j.val.castAdd m)
      hij
      (by simp only [Fin.lt_def, Fin.val_castAdd]; omega) h
  have hlt := lt_of_le_of_ne (not_lt.mp hnot) hne.symm
  have := (D.matching.1.val (i.val.castAdd m)).isLt
  have := (D.matching.1.val (j.val.castAdd m)).isLt
  simp only [throughTop, Fin.lt_def] at *
  omega

/-- Through strands join the defects of the bottom and top halves in left-to-right order.
The top half is read left to right, opposite to its cyclic boundary numbering. -/
def throughOrderIso (D : TLDiagram n m) :
    {i : Fin n // D.bottomHalf.val i = i} ≃o {j : Fin m // D.topHalf.val j = j} where
  toFun i := ⟨D.throughTop i, D.throughTop_defect i⟩
  invFun j := ⟨D.throughBottom j, D.throughBottom_defect j⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    simp only [throughBottom, throughTop_boundary, D.matching.1.apply_apply,
      Fin.val_castAdd]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only [throughTop, throughBottom_boundary, D.matching.1.apply_apply]
    have := j.val.isLt
    omega
  map_rel_iff' := by
    intro i j
    exact D.throughTop_strictMono.le_iff_le

/-- The top endpoint of a through strand is the reflected cyclic partner of its bottom
endpoint. -/
-- Simplify before the dependent defect argument is normalized, including at numeral indices.
@[simp↓]
theorem throughOrderIso_apply_val (D : TLDiagram n m)
    (i : {i : Fin n // D.bottomHalf.val i = i}) :
    ((D.throughOrderIso i).val : ℕ) =
      n + m - 1 - (D.matching.1.val (i.val.castAdd m) : ℕ) := (rfl)

/-- The bottom endpoint of a through strand is the cyclic partner of its top endpoint. -/
@[simp↓]
theorem throughOrderIso_symm_apply_val (D : TLDiagram n m)
    (j : {j : Fin m // D.topHalf.val j = j}) :
    ((D.throughOrderIso.symm j).val : ℕ) =
      (D.matching.1.val ⟨n + m - 1 - j.val, by omega⟩ : ℕ) := (rfl)

private theorem matching_bottom_eq_of_halves {D E : TLDiagram n m}
    (hb : D.bottomHalf.val = E.bottomHalf.val) (ht : D.topHalf.val = E.topHalf.val)
    (i : Fin n) : D.matching.1.val (i.castAdd m) = E.matching.1.val (i.castAdd m) := by
  by_cases hi : D.bottomHalf.val i = i
  · let eb : {i : Fin n // D.bottomHalf.val i = i} ≃o
        {i : Fin n // E.bottomHalf.val i = i} :=
      Set.orderIsoOfEq {i : Fin n | D.bottomHalf.val i = i}
        {i : Fin n | E.bottomHalf.val i = i} (by rw [hb])
    let et : {j : Fin m // D.topHalf.val j = j} ≃o
        {j : Fin m // E.topHalf.val j = j} :=
      Set.orderIsoOfEq {j : Fin m | D.topHalf.val j = j}
        {j : Fin m | E.topHalf.val j = j} (by rw [ht])
    have he : D.throughOrderIso = (eb.trans E.throughOrderIso).trans et.symm :=
      Subsingleton.elim _ _
    have hv := congrArg (fun f => ((f ⟨i, hi⟩).val : ℕ)) he
    have eb_val (x : {i : Fin n // D.bottomHalf.val i = i}) : (eb x).val = x.val := by
      exact congrArg Subtype.val (Set.orderIsoOfEq_apply
        {i : Fin n | D.bottomHalf.val i = i} {i : Fin n | E.bottomHalf.val i = i} _ x)
    have et_val (y : {j : Fin m // E.topHalf.val j = j}) : (et.symm y).val = y.val := by
      exact congrArg Subtype.val (Set.orderIsoOfEq_symm_apply
        {j : Fin m | D.topHalf.val j = j} {j : Fin m | E.topHalf.val j = j} _ y)
    simp only [OrderIso.trans_apply, et_val, throughOrderIso_apply_val, eb_val] at hv
    apply Fin.ext
    have hd := (D.matching.1.val (i.castAdd m)).isLt
    have he := (E.matching.1.val (i.castAdd m)).isLt
    omega
  · have hiE : E.bottomHalf.val i ≠ i := by simpa only [hb] using hi
    have hd := not_le.mp ((D.bottomHalf_apply_eq_self_iff i).not.mp hi)
    have he := not_le.mp ((E.bottomHalf_apply_eq_self_iff i).not.mp hiE)
    rw [← D.castAdd_bottomHalf_apply i hd, hb, E.castAdd_bottomHalf_apply i he]

/-- The two cut halves determine the boundary matching, independently of stored circles. -/
theorem matching_eq_of_halves {D E : TLDiagram n m}
    (hb : D.bottomHalf.val = E.bottomHalf.val) (ht : D.topHalf.val = E.topHalf.val) :
    D.matching = E.matching := by
  apply PlanarMatching.ext
  intro a
  by_cases ha : (a : ℕ) < n
  · exact matching_bottom_eq_of_halves hb ht ⟨a, ha⟩
  · have hj : n + m - 1 - (a : ℕ) < m := by omega
    have h := matching_bottom_eq_of_halves
      (D := verticalReflect n m D) (E := verticalReflect n m E)
      (by simpa only [← topHalf_val] using ht)
      (by simpa only [topHalf_verticalReflect_val] using hb)
      ⟨n + m - 1 - a, hj⟩
    have hv := congrArg Fin.val h
    rw [coe_verticalReflect_matching_val_apply, coe_verticalReflect_matching_val_apply] at hv
    have heq : (⟨n + m - 1 -
        ((⟨n + m - 1 - (a : ℕ), hj⟩ : Fin m).castAdd n : ℕ), by omega⟩ : Fin (n + m)) = a := by
      apply Fin.ext
      simp only [Fin.val_castAdd]
      omega
    rw [heq] at hv
    apply Fin.ext
    have := (D.matching.1.val a).isLt
    have := (E.matching.1.val a).isLt
    omega

/-- A diagram is determined by its bottom half, top half, and number of closed circles. -/
theorem ext_halves {D E : TLDiagram n m}
    (hb : D.bottomHalf.val = E.bottomHalf.val) (ht : D.topHalf.val = E.topHalf.val)
    (hc : D.circles = E.circles) : D = E :=
  TLDiagram.ext (matching_eq_of_halves hb ht) hc

end TauCeti.TLDiagram
