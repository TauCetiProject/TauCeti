/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# The quantum determinant of a two-by-two RTT family

For a spectral-parameter family of matrices satisfying the rational RTT exchange relation,
entries at parameters one unit apart satisfy determinant identities with the standard
alternating matrix. In size two these identities have a common coefficient, the quantum
determinant. This coefficient commutes with every matrix entry at every parameter, even when two
of the parameters coincide. No inverses of differences of parameters are needed.

## References

* A. Molev, M. Nazarov, G. Olshanski, *Yangians and classical Lie algebras*, Russian Math.
  Surveys 51 (1996), Propositions 2.4–2.5 and Theorem 2.10 (arXiv v2 numbering).
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet L-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>,
  `Formalism.FourierDecayAlt.Q.QdetFromRTT`, for the scalar-parameter formulation in size two.
-/

public section

namespace TauCeti

variable {K A ι : Type*}

/-- The rational RTT exchange relation, in entries. The spectral parameters are scalars, and the
products on the right are in the indicated order in the coefficient algebra. -/
def IsRTT [Sub K] [Mul A] [Sub A] [SMul K A] (t : K → Matrix ι ι A) : Prop :=
  ∀ (u v : K) (i j k l : ι), (u - v) • (t u i j * t v k l - t v k l * t u i j) =
    t u k j * t v i l - t v k j * t u i l

/-- The entrywise characterization of the rational RTT exchange relation. -/
theorem isRTT_iff [Sub K] [Mul A] [Sub A] [SMul K A] {t : K → Matrix ι ι A} : IsRTT t ↔
    ∀ (u v : K) (i j k l : ι), (u - v) • (t u i j * t v k l - t v k l * t u i j) =
      t u k j * t v i l - t v k j * t u i l := (Iff.rfl)

/-- The size-two quantum determinant, in column order with parameters `v + 1` and `v`. -/
def quantumDetTwo [Add K] [One K] [Mul A] [Sub A] (t : K → Matrix (Fin 2) (Fin 2) A) (v : K) : A :=
  t (v + 1) 0 0 * t v 1 1 - t (v + 1) 1 0 * t v 0 1

/-- The ordered two-term formula for the size-two quantum determinant. -/
theorem quantumDetTwo_def [Add K] [One K] [Mul A] [Sub A]
    (t : K → Matrix (Fin 2) (Fin 2) A) (v : K) :
    quantumDetTwo t v = t (v + 1) 0 0 * t v 1 1 - t (v + 1) 1 0 * t v 0 1 := (rfl)

namespace IsRTT

variable [CommRing K] [Ring A] [Algebra K A] {t : K → Matrix ι ι A}

/-- The exchange relation at adjacent spectral parameters `v + 1` and `v`, where the scalar
coefficient is one. -/
theorem adjacent (ht : IsRTT t) (v : K) (i j k l : ι) :
    t (v + 1) i j * t v k l - t v k l * t (v + 1) i j =
      t (v + 1) k j * t v i l - t v k j * t (v + 1) i l := by
  simpa only [add_sub_cancel_left, one_smul] using isRTT_iff.mp ht (v + 1) v i j k l

/-- The two ordered products from a repeated column agree at adjacent spectral parameters. -/
theorem mul_adjacent_same_col (ht : IsRTT t) (v : K) (i k j : ι) :
    t (v + 1) i j * t v k j = t (v + 1) k j * t v i j :=
  sub_left_injective (ht.adjacent v i j k j)

/-- The products from a repeated row agree in reverse parameter order. -/
theorem mul_adjacent_same_row (ht : IsRTT t) (v : K) (i j l : ι) :
    t v i j * t (v + 1) i l = t v i l * t (v + 1) i j :=
  sub_right_injective (ht.adjacent v i l i j)

/-- Reversing the order of the spectral parameters converts a column-ordered two-by-two minor
into the row-ordered expression with the same value. -/
theorem minor_eq_reverse (ht : IsRTT t) (v : K) (i k j l : ι) :
    t (v + 1) i j * t v k l - t (v + 1) k j * t v i l =
      t v k l * t (v + 1) i j - t v k j * t (v + 1) i l := by
  linear_combination (norm := abel) ht.adjacent v i j k l

/-- The adjacent-parameter column-ordered minor changes sign when its columns are swapped. -/
theorem minor_eq_neg_swap_cols (ht : IsRTT t) (v : K) (i k j l : ι) :
    t (v + 1) i j * t v k l - t (v + 1) k j * t v i l =
      -(t (v + 1) i l * t v k j - t (v + 1) k l * t v i j) := by
  have h₁ := ht.minor_eq_reverse v i k j l
  have h₂ := ht.minor_eq_reverse v i k l j
  linear_combination (norm := abel) h₁ + h₂

/-- An adjacent-parameter minor commutes with the entry at its first row and first column,
evaluated at any spectral parameter. -/
theorem commute_minor (ht : IsRTT t) (v w : K) (i k j l : ι) :
    Commute (t (v + 1) i j * t v k l - t (v + 1) k j * t v i l) (t w i j) := by
  let U := t (v + 1)
  let V := t v
  let W := t w
  let x := v + 1 - w
  have hy : w - v = 1 - x := by dsimp [x]; abel
  have h₁ : x • (U i j * W i l - W i l * U i j) = U i j * W i l - W i j * U i l :=
    isRTT_iff.mp ht (v + 1) w i j i l
  have h₂ : x • (U k j * W i l - W i l * U k j) = U i j * W k l - W i j * U k l :=
    isRTT_iff.mp ht (v + 1) w k j i l
  have h₃ : (1 - x) • (W i l * V k j - V k j * W i l) = W k l * V i j - V k l * W i j := by
    rw [← hy]
    exact isRTT_iff.mp ht w v i l k j
  have h₄ : (1 - x) • (W i l * V i j - V i j * W i l) = W i l * V i j - V i l * W i j := by
    rw [← hy]
    exact isRTT_iff.mp ht w v i l i j
  let p := U i j * V k j - U k j * V i j
  have hp : p = 0 := sub_eq_zero.mpr (ht.mul_adjacent_same_col v i k j)
  let q := U i j * V k l - U k j * V i l
  let q' := U k l * V i j - U i l * V k j
  have hq : q = q' := by
    simpa only [neg_sub] using ht.minor_eq_neg_swap_cols v i k j l
  -- Multiply the exchanges with `U` on the right by entries of `V`, and those with `V` on the
  -- left by entries of `U`. Their difference gives the commutator up to the repeated-column minor.
  have hcert :
      (x • (U i j * W i l - W i l * U i j) - (U i j * W i l - W i j * U i l)) * V k j -
      (x • (U k j * W i l - W i l * U k j) - (U i j * W k l - W i j * U k l)) * V i j +
      U i j * ((1 - x) • (W i l * V k j - V k j * W i l) - (W k l * V i j - V k l * W i j)) -
      U k j * ((1 - x) • (W i l * V i j - V i j * W i l) - (W i l * V i j - V i l * W i j)) =
      (x - 1) • (p * W i l) - x • (W i l * p) + q * W i j - W i j * q' := by
    dsimp only [p, q, q']
    noncomm_ring [sub_smul, add_smul, neg_smul, one_smul, smul_add, smul_neg, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc]
  rw [h₁, h₂, h₃, h₄, hp, ← hq] at hcert
  simp only [sub_self, mul_zero, zero_mul, smul_zero, zero_add] at hcert
  -- `hcert` now reads `0 = q * W i j - W i j * q`, and `q` is the let-bound minor in the goal.
  refine (commute_iff_eq _ _).mpr ?_
  exact sub_eq_zero.mp hcert.symm

variable {t₂ : K → Matrix (Fin 2) (Fin 2) A}

/-- The size-two quantum determinant commutes with every matrix entry at every parameter. -/
theorem commute_quantumDetTwo (ht₂ : IsRTT t₂) (v w : K) (i j : Fin 2) :
    Commute (quantumDetTwo t₂ v) (t₂ w i j) := by
  rw [quantumDetTwo_def]
  have h₁ := ht₂.minor_eq_neg_swap_cols v 0 1 0 1
  have h₂ := ht₂.minor_eq_neg_swap_cols v 1 0 0 1
  fin_cases i <;> fin_cases j
  · exact ht₂.commute_minor v w 0 1 0 1
  · rw [h₁]
    exact (ht₂.commute_minor v w 0 1 1 0).neg_left
  · rw [← neg_sub]
    exact (ht₂.commute_minor v w 1 0 0 1).neg_left
  · rw [← neg_sub, h₂, neg_neg]
    exact ht₂.commute_minor v w 1 0 1 0

local notation "J" => (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) A)

/-- The alternating matrix between the transposed matrix at `v + 1` and the matrix at `v`
picks out the quantum determinant. -/
theorem transpose_mul_alt_mul_eq_quantumDetTwo_smul (ht₂ : IsRTT t₂) (v : K) :
    (t₂ (v + 1)).transpose * J * t₂ v = quantumDetTwo t₂ v • J := by
  ext j l
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  fin_cases j <;> fin_cases l <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, mul_zero, mul_neg,
      mul_one, zero_add, neg_mul, add_zero, neg_add_rev, neg_neg, quantumDetTwo_def,
      sub_eq_add_neg]
  · linear_combination (norm := abel) ht₂.mul_adjacent_same_col v 0 1 0
  · abel
  · linear_combination (norm := abel) ht₂.minor_eq_neg_swap_cols v 0 1 1 0
  · linear_combination (norm := abel) ht₂.mul_adjacent_same_col v 0 1 1

/-- The alternating matrix between the matrix at `v` and the transposed matrix at `v + 1`
picks out the same quantum determinant. -/
theorem mul_alt_mul_transpose_eq_quantumDetTwo_smul (ht₂ : IsRTT t₂) (v : K) :
    t₂ v * J * (t₂ (v + 1)).transpose = quantumDetTwo t₂ v • J := by
  ext i k
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, mul_zero, mul_neg,
      mul_one, zero_add, neg_mul, add_zero, neg_add_rev, neg_neg, quantumDetTwo_def,
      sub_eq_add_neg]
  · linear_combination (norm := abel) ht₂.mul_adjacent_same_row v 0 0 1
  · have h := ht₂.minor_eq_reverse v 1 0 1 0
    have h' := ht₂.minor_eq_neg_swap_cols v 1 0 1 0
    linear_combination (norm := abel) -h + h'
  · linear_combination (norm := abel) ht₂.minor_eq_reverse v 0 1 0 1
  · linear_combination (norm := abel) ht₂.mul_adjacent_same_row v 1 0 1

end IsRTT

end TauCeti
