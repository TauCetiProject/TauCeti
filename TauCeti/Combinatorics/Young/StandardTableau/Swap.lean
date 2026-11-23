/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Relation
public import TauCeti.Combinatorics.Young.StandardTableau.Content
public import TauCeti.Combinatorics.Young.StandardTableau.Reading
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Fintype.BigOperators
import TauCeti.Combinatorics.Young.StandardTableau.Order
import Mathlib.Tactic.Ring

/-!
# Exchanging consecutive labels connects the standard tableaux of a shape

Exchanging the labels `k` and `k + 1` of a standard Young tableau gives a standard tableau when the
two labels lie neither next to each other in one row nor next to each other in one column
(`TauCeti.StandardYoungTableau.swap`). These exchanges connect all the standard tableaux of a
shape: every standard tableau is joined to the row-superstandard tableau by a chain of them
(`TauCeti.StandardYoungTableau.reflTransGen_swap_rowSuperstandard`). Since an exchange can be
undone, any two standard tableaux of one shape are joined by such a chain. In Young's seminormal
form a generator sends the vector of a tableau to a combination of it and the vector of the
exchanged tableau, so connectedness, together with nonzero exchange coefficients and Jucys–Murphy
eigenvalues that separate the tableaux, makes the seminormal representations irreducible.

To find the exchanges, read the cells of the shape left to right along the first row, then along
the second, and so on. The row-superstandard tableau is the only standard tableau whose labels are
read in increasing order, since a strictly monotone self-map of a finite linear order is the
identity. In any other one some label `k + 1` is read before `k`; then `k` and `k + 1` lie neither
next to each other in a row nor in a column, and exchanging them increases the sum over the labels
`k` of `k` times the reading position of `k`. Since there are finitely many tableaux, repeated
exchanges reach the row-superstandard tableau.

## Main results

* `TauCeti.StandardYoungTableau.reflTransGen_swap_rowSuperstandard`: every standard tableau is
  joined to the row-superstandard tableau by exchanges of consecutive labels.

## References

* A. Okounkov and A. Vershik, *A new approach to representation theory of symmetric groups*,
  Selecta Math. (N.S.) 2 (1996), 581–605, for the admissible transpositions of standard tableaux.
-/

public section

namespace TauCeti.StandardYoungTableau

open YoungTableau

variable {μ : YoungDiagram}

/-- The reading positions of the labels of `T`: the label `k` goes to the label that the
row-superstandard tableau gives to the cell carrying `k` in `T`. -/
private noncomputable def readingPerm (T : StandardYoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  relabelPerm T.toTableau (rowSuperstandard μ).toTableau

private theorem readingPerm_apply_val (T : StandardYoungTableau μ) (k : Fin μ.card) :
    (readingPerm T k : ℕ) = YoungDiagram.readingIndex μ (T.toTableau.symm k : ℕ × ℕ) := by
  rw [readingPerm, relabelPerm_apply, toTableau_apply, rowSuperstandard_apply_val]

/-- A standard tableau whose labels are read in increasing order is row-superstandard. -/
private theorem eq_rowSuperstandard_of_forall_lt (T : StandardYoungTableau μ)
    (h : ∀ k (hk : k + 1 < μ.card), readingPerm T ⟨k, by omega⟩ < readingPerm T ⟨k + 1, hk⟩) :
    T = rowSuperstandard μ := by
  have hmono : StrictMono (readingPerm T) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rw [Fin.mk_lt_mk] at hab
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hab | rfl
      · exact (ih (by omega) hab).trans (h b hb)
      · exact h a hb
  have hid : readingPerm T = 1 := Equiv.ext fun _ => hmono.apply_eq
  have hrel := relabel_relabelPerm T.toTableau (rowSuperstandard μ).toTableau
  rw [← readingPerm, hid, relabel_one] at hrel
  exact toTableau_injective hrel

/-- If the label `k + 1` is read before `k`, the two labels lie neither next to each other in a
row nor next to each other in a column. -/
private theorem abs_axialDistance_ne_one_of_lt (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k + 1 < μ.card) (hlt : readingPerm T ⟨k + 1, hk⟩ < readingPerm T ⟨k, by omega⟩) :
    |axialDistance T.toTableau k hk| ≠ 1 := by
  rw [Fin.lt_def, readingPerm_apply_val, readingPerm_apply_val] at hlt
  have hlab : (⟨k, by omega⟩ : Fin μ.card) < ⟨k + 1, hk⟩ := Fin.mk_lt_mk.mpr (Nat.lt_add_one k)
  rw [ne_eq, abs_eq zero_le_one, not_or, T.axialDistance_eq_one_iff,
    T.axialDistance_eq_neg_one_iff]
  constructor
  · intro hrow
    have hcol := (T.lt_iff_colIndex_lt hrow.symm).mp hlab
    rw [rowIndex_def, rowIndex_def] at hrow
    rw [colIndex_def, colIndex_def] at hcol
    exact (YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt hrow.symm hcol).not_gt hlt
  · intro hcol
    have hrow := (T.lt_iff_rowIndex_lt hcol.symm).mp hlab
    rw [rowIndex_def, rowIndex_def] at hrow
    exact (YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      ((YoungDiagram.mem_cells _).mp (T.toTableau.symm _).property) hrow).not_gt hlt

/-- Exchanging the labels `k` and `k + 1` exchanges their reading positions. -/
private theorem readingPerm_swap_apply (T : StandardYoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card)
    (h) (j : Fin μ.card) :
    readingPerm (T.swap k hk h) j = readingPerm T (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ j) := by
  rw [readingPerm, readingPerm, relabelPerm_apply, relabelPerm_apply, toTableau_swap,
    relabel_symm_apply, Equiv.swap_inv]

/-- The sum over the labels `k` of `k` times the reading position of `k`. -/
private noncomputable def readingSum (T : StandardYoungTableau μ) : ℤ :=
  ∑ j : Fin μ.card, ((j : ℕ) : ℤ) * ((readingPerm T j : ℕ) : ℤ)

/-- Exchanging labels `k` and `k + 1` with `k + 1` read before `k` increases `readingSum`. -/
private theorem readingSum_lt_readingSum_swap (T : StandardYoungTableau μ) (k : ℕ)
    (hk : k + 1 < μ.card) (hlt : readingPerm T ⟨k + 1, hk⟩ < readingPerm T ⟨k, by omega⟩) :
    readingSum T < readingSum (T.swap k hk (abs_axialDistance_ne_one_of_lt T k hk hlt)) := by
  set a : Fin μ.card := ⟨k, by omega⟩
  set b : Fin μ.card := ⟨k + 1, hk⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hdiff : readingSum (T.swap k hk (abs_axialDistance_ne_one_of_lt T k hk hlt)) -
      readingSum T = ∑ j : Fin μ.card, ((j : ℕ) : ℤ) *
        (((readingPerm T (Equiv.swap a b j) : ℕ) : ℤ) - ((readingPerm T j : ℕ) : ℤ)) := by
    simp only [readingSum, readingPerm_swap_apply, mul_sub, Finset.sum_sub_distrib, a, b]
  rw [Fintype.sum_eq_add a b hab fun j hj => by
    rw [Equiv.swap_apply_of_ne_of_ne hj.1 hj.2, sub_self, mul_zero],
    Equiv.swap_apply_left, Equiv.swap_apply_right] at hdiff
  rw [Fin.lt_def] at hlt
  have hval : ((b : ℕ) : ℤ) = (a : ℕ) + 1 := by simp [a, b]
  rw [hval, show ∀ x y z : ℤ, x * (y - z) + (x + 1) * (z - y) = z - y by intros; ring] at hdiff
  omega

/-- **Exchanges of consecutive labels connect the standard tableaux of a shape**: every standard
Young tableau is joined to the row-superstandard tableau by a chain of exchanges of labels `k` and
`k + 1` lying neither next to each other in a row nor next to each other in a column. -/
theorem reflTransGen_swap_rowSuperstandard (T : StandardYoungTableau μ) :
    Relation.ReflTransGen (fun U V : StandardYoungTableau μ => ∃ k hk h, V = U.swap k hk h) T
      (rowSuperstandard μ) := by
  -- induction on the number of tableaux with a larger `readingSum`
  generalize hm :
    (Finset.univ.filter fun U : StandardYoungTableau μ => readingSum T < readingSum U).card = m
  induction m using Nat.strong_induction_on generalizing T with
  | _ m ih =>
  by_cases hinc : ∀ k (hk : k + 1 < μ.card),
      readingPerm T ⟨k, by omega⟩ < readingPerm T ⟨k + 1, hk⟩
  · -- `T` is the row-superstandard tableau, and `rw` closes the goal by reflexivity
    rw [eq_rowSuperstandard_of_forall_lt T hinc]
  push Not at hinc
  obtain ⟨k, hk, hle⟩ := hinc
  have hlt : readingPerm T ⟨k + 1, hk⟩ < readingPerm T ⟨k, by omega⟩ :=
    lt_of_le_of_ne hle fun h => by simpa [Fin.ext_iff] using (readingPerm T).injective h
  have hsum := readingSum_lt_readingSum_swap T k hk hlt
  refine Relation.ReflTransGen.head ⟨k, hk, abs_axialDistance_ne_one_of_lt T k hk hlt, rfl⟩
    (ih _ ?_ _ rfl)
  rw [← hm]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr
    ⟨T.swap k hk (abs_axialDistance_ne_one_of_lt T k hk hlt), ?_, ?_⟩)
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    exact hsum.trans hU
  · simpa using hsum
  · simp

end TauCeti.StandardYoungTableau
