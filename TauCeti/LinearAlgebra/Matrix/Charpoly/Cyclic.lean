/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Characteristic polynomials without determinants

Two generic tools for computing characteristic polynomials with no determinant in the kernel.

* `Matrix.charpoly_eq_of_cyclic`: if the vectors `v, M v, …, Mⁿ⁻¹ v` are linearly independent and
  a monic `q` of degree `n` kills `v`, then `charpoly M = q`.
* `Matrix.det_ne_zero_of_mul_left_cancel`: a left-cancellable matrix over a domain has nonzero
  determinant. Together with Mathlib's `Matrix.charpoly_eq_of_mul_eq_mul`, an intertwiner that can
  be cancelled transfers the characteristic polynomial.
-/

public section

open Polynomial Matrix

namespace Matrix

/-- **Cyclic-vector criterion.** If the vectors `v, M v, …, Mⁿ⁻¹ v` are linearly independent and
a monic polynomial `q` of degree `n` satisfies `q(M) v = 0`, then `q` is the characteristic
polynomial of `M`: by Cayley–Hamilton `charpoly M - q` also kills `v`, and it has degree less than
`n`, so linear independence forces all its coefficients to vanish. -/
theorem charpoly_eq_of_cyclic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) {q : R[X]} (hq : q.Monic) (hdeg : q.natDegree = n)
    (v : Fin n → R) (hv : LinearIndependent R fun k : Fin n => (M ^ (k : ℕ)) *ᵥ v)
    (hqv : (aeval M q) *ᵥ v = 0) : M.charpoly = q := by
  have hcp : M.charpoly.natDegree = n := by simp
  have hrn : (M.charpoly - q).coeff n = 0 := by
    rw [coeff_sub]
    have h1 := M.charpoly_monic.coeff_natDegree
    have h2 := hq.coeff_natDegree
    rw [hcp] at h1
    rw [hdeg] at h2
    rw [h1, h2, sub_self]
  have hzero : (aeval M (M.charpoly - q)) *ᵥ v = 0 := by
    rw [map_sub, aeval_self_charpoly, zero_sub, neg_mulVec, hqv, neg_zero]
  have hlt : (M.charpoly - q).natDegree < n + 1 := by
    have := natDegree_sub_le M.charpoly q
    rw [hcp, hdeg, max_self] at this
    omega
  rw [aeval_eq_sum_range' hlt, Finset.sum_range_succ, hrn, zero_smul, add_zero,
    sum_mulVec, Finset.sum_range] at hzero
  simp only [smul_mulVec] at hzero
  have hc := Fintype.linearIndependent_iff.1 hv _ hzero
  refine sub_eq_zero.1 (Polynomial.ext fun k => ?_)
  rw [coeff_zero]
  rcases lt_trichotomy k n with hk | rfl | hk
  · exact hc ⟨k, hk⟩
  · exact hrn
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]

/-- **A left-cancellable matrix over a domain has nonzero determinant.** -/
theorem det_ne_zero_of_mul_left_cancel {E : Matrix ι ι R}
    (h : ∀ X Y : Matrix ι ι R, E * X = E * Y → X = Y) : E.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hEv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  have hX := h (Matrix.of fun i _ => v i) 0 (by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hEv i)
  funext i
  simpa using congrFun (congrFun hX i) i

end Matrix

end
