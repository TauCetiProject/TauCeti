/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.NoncommRing
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Frobenius norm and determinant inequalities for positive semidefinite matrices

This file proves three matrix estimates in the Frobenius norm over `ℂ`:

* `TauCeti.exists_unitary_mul_posSemidef`: every invertible complex square matrix factors as
  `k * z` with `k ∈ unitaryGroup X ℂ` and `z.PosSemidef`.
* `TauCeti.norm_sub_one_le_norm_mul_self_sub_one`: a positive semidefinite matrix `z` satisfies
  `‖z - 1‖ ≤ ‖z * z - 1‖` in the Frobenius norm.
* `TauCeti.one_add_norm_sq_le_norm_det_one_add`: every complex square matrix `A` satisfies
  `1 + ‖A‖ ^ 2 ≤ ‖(1 + Aᴴ * A).det‖` in the Frobenius norm.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), files
`src/New/Appendix/DiscreteSeries/SteepParameters.lean`
(`New.DiscreteSeries.exists_unitary_mul_posSemidef`) and
`src/New/Appendix/DiscreteSeries/Localization.lean`
(`New.DiscreteSeries.norm_sub_one_le_norm_mul_self_sub_one`,
`New.DiscreteSeries.one_add_norm_sq_le_norm_det_one_add`).
-/

@[expose] public section

namespace TauCeti

open Matrix
open scoped ComplexOrder

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- An invertible complex matrix factors as a unitary matrix times a positive semidefinite
matrix. -/
theorem exists_unitary_mul_posSemidef {X : Type*} [Fintype X] [DecidableEq X]
    {a : Matrix X X ℂ} (ha : IsUnit a) :
    ∃ k ∈ unitaryGroup X ℂ, ∃ z : Matrix X X ℂ, z.PosSemidef ∧ a = k * z := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨u.polarUnitary, u.polarUnitary.property, CFC.abs (u : Matrix X X ℂ),
    (CFC.abs_nonneg _).posSemidef, u.polarUnitary_mul_sqrt_star_mul.symm⟩

section Frobenius

open Matrix.Norms.Frobenius

/-- A positive semidefinite complex matrix `z` is at least as close to `1` as `z ^ 2` in the
Frobenius norm. -/
theorem norm_sub_one_le_norm_mul_self_sub_one {X : Type*} [Fintype X] [DecidableEq X]
    {z : Matrix X X ℂ} (hz : z.PosSemidef) : ‖z - 1‖ ≤ ‖z * z - 1‖ := by
  have h_tr (B : Matrix X X ℂ) : (Bᴴ * B).trace = (‖B‖ ^ 2 : ℝ) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
      RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum, ← Complex.ofReal_pow]
    rw [Finset.sum_comm]
    simp
  have h_pos : ((z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1)).PosSemidef :=
    ((posSemidef_conjTranspose_mul_self z).add (hz.add hz)).conjTranspose_mul_mul_same _
  have h_diff : (z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1) =
      (z * z - 1)ᴴ * (z * z - 1) - (z - 1)ᴴ * (z - 1) := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_one, hz.isHermitian.eq]
    noncomm_ring
  have h_trace : (0 : ℂ) ≤ (‖z * z - 1‖ ^ 2 : ℝ) - (‖z - 1‖ ^ 2 : ℝ) := by
    rw [← h_tr (z * z - 1), ← h_tr (z - 1), ← trace_sub, ← h_diff]
    exact h_pos.trace_nonneg
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (Complex.real_le_real.mp (sub_nonneg.mp h_trace))

/-- For any complex square matrix `A` with the Frobenius norm,
`1 + ‖A‖ ^ 2 ≤ ‖(1 + Aᴴ * A).det‖`. -/
theorem one_add_norm_sq_le_norm_det_one_add {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℂ) : 1 + ‖A‖ ^ 2 ≤ ‖(1 + Aᴴ * A).det‖ := by
  have h_tr : (Aᴴ * A).trace = (‖A‖ ^ 2 : ℝ) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
      RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum, ← Complex.ofReal_pow]
    rw [Finset.sum_comm]
    simp
  have h_prod (s : Finset X) {μ : X → ℝ} (hμ : ∀ i : X, 0 ≤ μ i) :
      1 + ∑ i ∈ s, μ i ≤ ∏ i ∈ s, (1 + μ i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith [hμ a, s.sum_nonneg fun i _ ↦ hμ i]
  have hA := A.posSemidef_conjTranspose_mul_self
  convert h_prod Finset.univ hA.eigenvalues_nonneg using 2
  · rw [← Complex.ofReal_inj, ← h_tr, hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  · rw [show ‖(1 + Aᴴ * A).det‖ = ‖(Aᴴ * A).charpoly.eval (-1)‖ from by
      rw [eval_charpoly, map_neg, map_one, ← neg_add', det_neg]
      simp, hA.isHermitian.charpoly_eq, Polynomial.eval_prod, norm_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      simpa [← neg_add', ← Complex.ofReal_one, ← Complex.ofReal_add] using
        Complex.norm_of_nonneg (add_nonneg zero_le_one (hA.eigenvalues_nonneg i))

end Frobenius

end TauCeti
