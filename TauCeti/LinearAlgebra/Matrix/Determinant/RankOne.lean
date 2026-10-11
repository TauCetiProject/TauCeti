/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Tactic.LinearCombination

/-!
# Determinants along rank-one perturbations

The determinant is affine in the scalar multiplying a rank-one perturbation, even when
the original matrix is singular and the coefficient ring has zero divisors. This is the
linear algebra behind determinant skein identities: positive and negative crossings
change the same matrix by different scalar multiples of one rank-one matrix.

The proof uses Mathlib's alternating multilinear determinant expansion. Terms choosing
at least two rows of the perturbation vanish because those rows are proportional.
-/

public section

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The determinant is affine in the coefficient of a rank-one perturbation.
No invertibility assumption on `A` or on the scalar is required. -/
theorem det_add_smul_vecMulVec (A : Matrix ι ι R) (u v : ι → R) (c : R) :
    (A + c • vecMulVec u v).det =
      A.det + c * ((A + vecMulVec u v).det - A.det) := by
  classical
  -- Expand by the subsets of rows supplied by the rank-one perturbation.
  let D : (ι → R) [⋀^ι]→ₗ[R] R := detRowAlternating
  have hD (B : Matrix ι ι R) : D (fun i => B i) = B.det := rfl
  let d (c : R) (s : Finset ι) :=
    D (s.piecewise (fun i => (c * u i) • v) (fun i => A i))
  have hexpand (c : R) : (A + c • vecMulVec u v).det = ∑ s : Finset ι, d c s := by
    have hm : (fun i => (A + c • vecMulVec u v) i) =
        (fun i => (c * u i) • v) + (fun i => A i) := by
      ext i j
      simp [vecMulVec_apply, mul_assoc, add_comm]
    exact (hD _).symm.trans ((congrArg D hm).trans
      (D.map_add_univ (fun i => (c * u i) • v) (fun i => A i)))
  -- Only singleton subsets contribute a nonconstant term.
  have hterm (s : Finset ι) (hs : s ≠ ∅) : d c s = c * d 1 s := by
    by_cases hcard : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simp [d, Finset.piecewise_singleton, D.map_update_smul, mul_assoc]
    · have hs_card : 1 < s.card := by
        have : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs_card
      have hz (a : R) : d a s = 0 := by
        have hfactor : s.piecewise (fun i => (a * u i) • v) (fun i => A i) =
            fun i => (if i ∈ s then a * u i else 1) •
              s.piecewise (fun _ => v) (fun i => A i) i := by
          ext i k
          by_cases h : i ∈ s <;> simp [h]
        dsimp only [d]
        rw [hfactor]
        rw [D.map_smul_univ]
        have hzero : D (s.piecewise (fun _ => v) (fun i => A i)) = 0 :=
          D.map_eq_zero_of_eq _ (by simp [hi, hj]) hij
        simp [hzero]
      simp [hz]
  -- In the difference of the two expansions only the empty subset remains.
  have hsum : (∑ s : Finset ι, (d c s - c * d 1 s)) = (1 - c) * A.det := by
    rw [Finset.sum_eq_single ∅]
    · simp [d, hD, sub_mul]
    · intro s _ hs
      rw [hterm s hs, sub_self]
    · simp
  rw [hexpand c]
  have h := hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hexpand 1] at h
  simp only [one_smul] at h
  linear_combination h

end Matrix
