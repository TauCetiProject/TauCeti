/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Ostrowski–Taussky determinant inequality

The determinant of the positive-semidefinite Hermitian part of a complex matrix is bounded
by the modulus of its determinant. More generally, `Matrix.PosSemidef.norm_det_le_two_pow_mul`
bounds the determinant of any positive-semidefinite lower bound for `A + Aᴴ`.
Both results include singular matrices and the empty index type.

## Provenance

`Matrix.PosSemidef.norm_det_le_two_pow_mul` and its private eigenvalue estimate are adapted from
`New.ostrowski_taussky` and `New.one_le_re_of_mem_roots_charpoly_inv_mul` in
`src/Lib/General/Analysis/GaussianIntegral.lean` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The normalized Hermitian-part formulation
`Matrix.PosSemidef.norm_det_le_norm_det_of_two_smul_eq` is derived here from that comparison.

## References

* A. M. Ostrowski and O. Taussky, *On the variation of the determinant of a positive
  definite matrix*, Indagationes Mathematicae 13 (1951), 383–385.
-/

public section

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The relative matrix `H⁻¹ (A + A)` has its eigenvalues to the right of `1` when
`H` is positive definite and `A + Aᴴ - H` is positive semidefinite. -/
private lemma Matrix.PosDef.one_le_re_of_mem_roots_charpoly_inv_mul {A H : Matrix ι ι ℂ}
    (hH : H.PosDef) (hsub : (A + Aᴴ - H).PosSemidef) {z : ℂ}
    (hz : z ∈ (H⁻¹ * (A + A)).charpoly.roots) : 1 ≤ z.re := by
  -- Pair an eigenvector with `H`: the real part of `vᴴ (2A) v` is `vᴴ (A + Aᴴ) v`.
  obtain ⟨v, hv_ne, hv⟩ : ∃ v : ι → ℂ, v ≠ 0 ∧ z • v = (H⁻¹ * (A + A)) *ᵥ v := by
    simpa [eval_charpoly, ← exists_mulVec_eq_zero_iff, sub_mulVec, sub_eq_zero] using
      Polynomial.isRoot_of_mem_roots hz
  have heigen : z • H *ᵥ v = A *ᵥ v + A *ᵥ v := by
    simp [← mulVec_smul, hv, ← add_mulVec, hH.det_pos.ne']
  obtain ⟨hpos, him⟩ : 0 < (star v ⬝ᵥ H *ᵥ v).re ∧ 0 = (star v ⬝ᵥ H *ᵥ v).im :=
    Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hv_ne)
  have hre : z.re * (star v ⬝ᵥ H *ᵥ v).re = 2 * (star v ⬝ᵥ A *ᵥ v).re := by
    simpa [← him, two_mul] using congrArg (fun w : ι → ℂ ↦ (star v ⬝ᵥ w).re) heigen
  have hle : (star v ⬝ᵥ H *ᵥ v).re ≤ 2 * (star v ⬝ᵥ A *ᵥ v).re := by
    simpa [add_mulVec, sub_mulVec, mulVec_conjTranspose, dotProduct_star, ← dotProduct_mulVec,
      two_mul] using hsub.re_dotProduct_nonneg v
  exact le_of_mul_le_mul_right (by rwa [one_mul, hre]) hpos

/-- **Ostrowski–Taussky comparison.** If `H` and `A + Aᴴ - H` are positive semidefinite,
then `‖det H‖ ≤ 2ⁿ ‖det A‖`. -/
theorem Matrix.PosSemidef.norm_det_le_two_pow_mul {A H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hsub : (A + Aᴴ - H).PosSemidef) :
    ‖H.det‖ ≤ 2 ^ Fintype.card ι * ‖A.det‖ := by
  by_cases hdet : H.det = 0
  · simp [hdet]
  let M := H⁻¹ * (A + A)
  have hroot (z : ℂ) (hz : z ∈ M.charpoly.roots) : 1 ≤ ‖z‖ :=
    ((hH.posDef_iff_det_ne_zero.2 hdet).one_le_re_of_mem_roots_charpoly_inv_mul hsub hz).trans
      z.re_le_norm
  have hprod : 1 ≤ ‖M.det‖ := by
    -- Each characteristic root has modulus at least one.
    rw [det_eq_prod_roots_charpoly]
    exact Multiset.prod_induction (1 ≤ ‖·‖) _
      (fun a b ha hb ↦ by simpa using one_le_mul_of_one_le_of_one_le ha hb) norm_one.ge hroot
  have hnorm : ‖M.det‖ = 2 ^ Fintype.card ι * ‖A.det‖ / ‖H.det‖ := by
    simp [M, ← two_smul ℂ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rwa [hnorm, one_le_div (norm_pos_iff.2 hdet)] at hprod

/-- **Ostrowski–Taussky inequality.** If `H` is a positive-semidefinite Hermitian part of
`A`, given by `2 • H = A + Aᴴ`, then `‖det H‖ ≤ ‖det A‖`. -/
theorem Matrix.PosSemidef.norm_det_le_norm_det_of_two_smul_eq {A H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (h2 : (2 : ℂ) • H = A + Aᴴ) : ‖H.det‖ ≤ ‖A.det‖ := by
  have hsum : (A + Aᴴ).PosSemidef := by
    rw [← h2]
    exact hH.smul (by norm_num : (0 : ℂ) ≤ 2)
  have h := hsum.norm_det_le_two_pow_mul (A := A) (by simpa using
    (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef))
  rw [← h2, det_smul, norm_mul, norm_pow] at h
  norm_num only [Complex.norm_ofNat] at h
  exact le_of_mul_le_mul_left h (by positivity : (0 : ℝ) < 2 ^ Fintype.card ι)
