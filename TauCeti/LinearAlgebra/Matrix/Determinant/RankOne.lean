/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Tactic.Ring

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
  -- Expand by the subsets `s` of rows supplied by the rank-one perturbation. Those rows are
  -- multiples of `v`, so each term is a scalar multiple of `e s`.
  let D : (ι → R) [⋀^ι]→ₗ[R] R := detRowAlternating
  let e (s : Finset ι) := D (s.piecewise (fun _ => v) (fun i => A i))
  have he : e ∅ = A.det := by simp only [e, Finset.piecewise_empty]; rfl
  have hexpand (c : R) :
      (A + c • vecMulVec u v).det = ∑ s : Finset ι, (∏ i ∈ s, c * u i) * e s := by
    have hm : (fun i => (A + c • vecMulVec u v) i) =
        (fun i => (c * u i) • v) + (fun i => A i) := by
      ext i j
      simp [vecMulVec_apply, mul_assoc, add_comm]
    refine (congrArg D hm).trans <| (D.map_add_univ _ _).trans <|
      Finset.sum_congr rfl fun s _ => ?_
    convert D.map_piecewise_smul (fun i => c * u i) (s.piecewise (fun _ => v) fun i => A i) s
      using 2
    exact congrArg D <| s.piecewise_congr (fun i hi => by simp [hi]) fun i hi => by simp [hi]
  -- Only the empty set and singletons contribute: `e s = 0` once `s` has two rows.
  have hterm (s : Finset ι) : (∏ i ∈ s, c * u i) * e s =
      (if s = ∅ then (1 - c) * A.det else 0) + c * ((∏ i ∈ s, 1 * u i) * e s) := by
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp [he]
      ring
    obtain ⟨i, rfl⟩ | ⟨i, hi, j, hj, hij⟩ := hs.exists_eq_singleton_or_nontrivial
    · simp
      ring
    have hzero : e s = 0 :=
      D.map_eq_zero_of_eq _ (by simp [Finset.mem_coe.mp hi, Finset.mem_coe.mp hj]) hij
    simp [hzero, hs.ne_empty]
  rw [hexpand, ← one_smul R (vecMulVec u v), hexpand, Finset.sum_congr rfl fun s _ => hterm s,
    Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum]
  simp
  ring

end Matrix
