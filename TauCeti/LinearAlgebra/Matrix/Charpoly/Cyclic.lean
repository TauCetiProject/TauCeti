/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic polynomials via cyclic vectors

If a monic polynomial `p` of degree `n` annihilates an `n × n` matrix `M` over a commutative ring
and the first `n` powers of `M` carry `e₀` to `e₀, …, eₙ₋₁`, then `M.charpoly = p`: the
difference `M.charpoly - p` has degree `< n` and annihilates `M`, so evaluating at `e₀` forces
every coefficient below `n` to vanish.

## Main results

* `Matrix.charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single`: a monic
  annihilating polynomial of degree `n` with standard-basis orbit of `e₀` equals the
  characteristic polynomial.
-/

public section

open Polynomial

namespace Matrix

/-- **Cyclic-vector criterion for the characteristic polynomial.** If `p` is monic of degree `n`,
annihilates `M`, and the first `n` powers of `M` carry `e₀` to the standard basis vectors `eₘ`,
then `M.charpoly = p`: the difference `M.charpoly - p` has degree `< n` and annihilates `M`, so its
evaluation at `e₀` forces every coefficient below `n` to vanish. -/
theorem charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single {n : ℕ} {R : Type*}
    [CommRing R] (hn : 0 < n) {M : Matrix (Fin n) (Fin n) R} {p : R[X]}
    (hp : p.IsMonicOfDegree n) (hann : aeval M p = 0)
    (hcyc : ∀ m (hm : m < n), M ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1) :
    M.charpoly = p := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  have hdeg_lt : (M.charpoly - p).natDegree < n :=
    IsMonicOfDegree.natDegree_sub_lt hn.ne'
      ⟨by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], M.charpoly_monic⟩ hp
  have hann_sub : aeval M (M.charpoly - p) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hann, sub_zero]
  rw [← sub_eq_zero]
  set q := M.charpoly - p
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j n with hj | hj
  · have hvec : (aeval M q *ᵥ Pi.single ⟨0, hn⟩ 1) ⟨j, hj⟩ = 0 := by
      rw [hann_sub, Matrix.zero_mulVec, Pi.zero_apply]
    rw [aeval_eq_sum_range' hdeg_lt, Matrix.sum_mulVec, Finset.sum_apply,
      Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)] at hvec
    · rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc j hj, Pi.single_eq_same, smul_eq_mul,
        mul_one] at hvec
      exact hvec
    · intro i hi hij
      rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc i (Finset.mem_range.mp hi),
        Pi.single_eq_of_ne (Fin.ne_of_val_ne hij.symm), smul_zero]
  · exact coeff_eq_zero_of_natDegree_lt (hdeg_lt.trans_le hj)

end Matrix
