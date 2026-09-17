/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Linear independence of polynomial sequences

This file generalizes Mathlib's `Polynomial.Sequence.linearIndependent` from domains to additive
cancellation semirings where the sequence elements have right-regular leading coefficients, and
constructs a basis over rings when those coefficients are units.

## Main statements

* `Polynomial.Sequence.linearIndependent_of_isRightRegular_leadingCoeff`: a polynomial sequence
  whose elements have right-regular leading coefficients is linearly independent over any additive
  cancellation semiring.
* `Polynomial.Sequence.basisOfIsUnitLeadingCoeff`: the corresponding basis of `R[X]`.
-/

public section

namespace Polynomial.Sequence

open Module Submodule

variable {R : Type*} [Semiring R] (S : Polynomial.Sequence R)

/-- Polynomials in a polynomial sequence whose leading coefficients are right-regular are linearly
independent. -/
theorem linearIndependent_of_isRightRegular_leadingCoeff
    [IsCancelAdd R] (hCoeff : ∀ i, IsRightRegular (S i).leadingCoeff) :
    LinearIndependent R S := by
  classical
  refine linearIndependent_iff'ₛ.2 fun s f g hsum i hi => ?_
  by_contra hfg
  have hne : (s.filter fun j => f j ≠ g j).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨hi, hfg⟩⟩
  let m := (s.filter fun j => f j ≠ g j).max' hne
  have hm : m ∈ s.filter fun j => f j ≠ g j := Finset.max'_mem _ hne
  have hfm : f m ≠ g m := (Finset.mem_filter.1 hm).2
  have hms : m ∈ s := (Finset.mem_filter.1 hm).1
  have hle (j : ℕ) (hj : j ∈ s) (hfj : f j ≠ g j) : j ≤ m :=
    Finset.le_max' _ j (Finset.mem_filter.2 ⟨hj, hfj⟩)
  have heq (j : ℕ) (hj : j ∈ s) (hj_gt : m < j) : f j = g j := by
    by_contra h
    exact (not_lt_of_ge (hle j hj h)) hj_gt
  have h_split :
      f m • S m + ∑ j ∈ s.erase m, f j • S j =
        g m • S m + ∑ j ∈ s.erase m, g j • S j := by
    rw [Finset.add_sum_erase s (fun j => f j • S j) hms,
      Finset.add_sum_erase s (fun j => g j • S j) hms]
    exact hsum
  have h_coeff := congrArg (Polynomial.coeff · m) h_split
  rw [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_add,
    Polynomial.coeff_smul] at h_coeff
  have h_m_coeff : (S m).coeff m = (S m).leadingCoeff := by
    rw [Polynomial.leadingCoeff, S.natDegree_eq m]
  have h_erase_eq :
      (∑ j ∈ s.erase m, f j • S j).coeff m =
        (∑ j ∈ s.erase m, g j • S j).coeff m := by
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_s := Finset.mem_of_mem_erase hj
    have hj_ne := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hj_ne with hj_lt | hj_gt
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [S.natDegree_eq]), smul_zero,
        smul_zero]
    · rw [heq j hj_s hj_gt]
  rw [h_erase_eq, h_m_coeff] at h_coeff
  exact hfm ((hCoeff m) (by simpa [smul_eq_mul] using add_right_cancel h_coeff))

section Ring

variable {R : Type*} [Ring R] (S : Polynomial.Sequence R)

/-- Every polynomial sequence with unit leading coefficients is a basis of `R[X]`. -/
noncomputable def basisOfIsUnitLeadingCoeff
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) :
    Basis ℕ R R[X] :=
  Basis.mk (S.linearIndependent_of_isRightRegular_leadingCoeff fun i =>
      (hCoeff i).isRegular.right)
    (eq_top_iff.mp (S.span hCoeff))

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
theorem basisOfIsUnitLeadingCoeff_apply
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) (i : ℕ) :
    S.basisOfIsUnitLeadingCoeff hCoeff i = S i :=
  Basis.mk_apply _ _ _

end Ring

end Polynomial.Sequence
