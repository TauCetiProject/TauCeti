/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Diagonal
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Cokernel length and determinant

For a square matrix with nonzero determinant over a principal ideal domain, the length of
its cokernel is the order of its determinant. In particular, over a discrete valuation ring
this computes the cokernel length by the normalized valuation of the determinant. Applied
to a trace Gram matrix, this is the linear algebra input to the discriminant-length formula.

The diagonal computation works over any commutative ring, including for zero entries.
The general computation uses `Matrix.exists_mul_mul_eq_diagonal` and
invariance of quotients under linear equivalences; no choice of uniformizer is needed.

## References

* J.-P. Serre, *Local Fields*, Chapter III, Section 3 (discriminants and differents).
-/

public section

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The cokernel of a diagonal matrix has length equal to the sum of the orders of its
entries. Zero entries are allowed, with length and order valued in `ℕ∞`. -/
theorem length_quotient_range_diagonal_mulVecLin (d : ι → R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (diagonal d).mulVecLin) =
      ∑ i, Ring.ord R (d i) := by
  have hrange : LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i ↦ (Ideal.span {d i} : Submodule R R)) := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_const,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by simp [mulVec_diagonal]⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, by ext i; simpa [mulVecLin_apply, mulVec_diagonal] using (hy i).symm⟩
  rw [hrange, (Submodule.quotientPi (fun i ↦ (Ideal.span {d i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype]
  rfl

/-- Over a principal ideal domain, the cokernel length of a square matrix with nonzero
determinant is the order of its determinant. For a discrete valuation ring this is the
usual determinant valuation formula. -/
theorem length_quotient_range_mulVecLin_eq_ord_det [IsDomain R] [IsPrincipalIdealRing R]
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range A.mulVecLin) = Ring.ord R A.det := by
  obtain ⟨L, Q, d, hL, hQ, hdiag⟩ := A.exists_mul_mul_eq_diagonal
  let e : (ι → R) ≃ₗ[R] (ι → R) := LinearEquiv.ofBijective L.mulVecLin
    ⟨mulVec_injective_of_isUnit (L.isUnit_iff_isUnit_det.mpr hL),
      mulVec_surjective_iff_isUnit.mpr (L.isUnit_iff_isUnit_det.mpr hL)⟩
  have hrange : (LinearMap.range A.mulVecLin).map e.toLinearMap =
      LinearMap.range (diagonal d).mulVecLin := by
    rw [← hdiag, mulVecLin_mul, mulVecLin_mul,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
        (mulVec_surjective_iff_isUnit.mpr (Q.isUnit_iff_isUnit_det.mpr hQ))),
      LinearMap.range_comp]
    rfl
  have hlength := (Submodule.Quotient.equiv _ _ e hrange).length_eq
  rw [length_quotient_range_diagonal_mulVecLin] at hlength
  have hdet : L.det * A.det * Q.det = ∏ i, d i := by
    simpa only [det_mul, det_diagonal] using congrArg det hdiag
  have hd : ∀ i, d i ≠ 0 := by
    have hprod : ∏ i, d i ≠ 0 := by
      rw [← hdet]
      exact mul_ne_zero (mul_ne_zero hL.ne_zero hA) hQ.ne_zero
    simpa only [Finset.mem_univ, forall_const] using Finset.prod_ne_zero_iff.mp hprod
  have hord : Ring.ord R (∏ i, d i) = ∑ i, Ring.ord R (d i) := by
    have hprod (s : Finset ι) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simp only [Finset.prod_insert hi, Finset.sum_insert hi]
        rw [Ring.ord_mul' R (mem_nonZeroDivisors_iff_ne_zero.mpr (hd i)), ih]
    exact hprod Finset.univ
  rw [← hord, ← hdet, Ring.ord_mul_of_isUnit_right hQ,
    Ring.ord_mul_of_isUnit_left hL] at hlength
  exact hlength

end Matrix
