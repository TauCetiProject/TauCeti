/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Positivity and square roots of `2 × 2` matrices

A Hermitian `2 × 2` matrix is positive semidefinite exactly when its trace and
determinant are nonnegative. For a real symmetric matrix, this is equivalent to
nonnegativity of both diagonal entries and of the determinant.

The continuous-functional-calculus square root of a positive-semidefinite `2 × 2` matrix `H` has a
closed form in terms of its trace `t` and determinant `δ`:

`√H = (t + 2 √δ) ^ (-1 / 2) • (H + √δ • 1)`

(`Matrix.PosSemidef.sqrt_fin_two`). By the Cayley–Hamilton theorem `H * H = t • H - δ • 1`, the
positive-semidefinite matrix `H + √δ • 1` squares to `(t + 2 √δ) • H`, and `√H` is the unique
positive-semidefinite square root. For `det H = 1`, as for `H = g * gᴴ` with `g ∈ SL(2, 𝕜)`, this
is the formula `√H = (t + 2) ^ (-1 / 2) • (H + 1)` for the positive polar factor of `g`, which
makes the polar decomposition of `SL(2, 𝕜)` explicit.

## References

* Bernard W. Levinger, *The square root of a `2 × 2` matrix*, Mathematics Magazine **53** (1980),
  222–224.
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A Hermitian `2 × 2` matrix is positive semidefinite exactly when its trace and
determinant are nonnegative. -/
theorem IsHermitian.posSemidef_iff_trace_nonneg_and_det_nonneg
    {H : Matrix (Fin 2) (Fin 2) 𝕜} (hH : H.IsHermitian) :
    H.PosSemidef ↔ 0 ≤ H.trace ∧ 0 ≤ H.det := by
  refine ⟨fun h ↦ ⟨h.trace_nonneg, h.det_nonneg⟩, fun ⟨ht, hd⟩ ↦ ?_⟩
  rw [hH.trace_eq_sum_eigenvalues, Fin.sum_univ_two, ← RCLike.ofReal_add,
    RCLike.ofReal_nonneg] at ht
  rw [hH.det_eq_prod_eigenvalues, Fin.prod_univ_two, ← RCLike.ofReal_mul,
    RCLike.ofReal_nonneg] at hd
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  fin_cases i <;> dsimp <;> nlinarith

/-- The diagonal entries and determinant characterize positivity of a real symmetric
`2 × 2` matrix, also when it is regarded as a complex matrix. -/
theorem posSemidef_fin_two_ofReal_iff (a b c : ℝ) :
    (!![(a : 𝕜), (b : 𝕜); (b : 𝕜), (c : 𝕜)]).PosSemidef ↔
      0 ≤ a ∧ 0 ≤ c ∧ b ^ 2 ≤ a * c := by
  have hH : (!![(a : 𝕜), (b : 𝕜); (b : 𝕜), (c : 𝕜)]).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]
  refine ⟨fun h ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  · have ha := h.diag_nonneg (i := 0)
    have hc := h.diag_nonneg (i := 1)
    have hd := h.det_nonneg
    simp only [of_apply, cons_val_zero, cons_val_one, cons_val_fin_one,
      RCLike.ofReal_nonneg] at ha hc
    rw [det_fin_two] at hd
    simp only [of_apply, cons_val_zero, cons_val_one, cons_val_fin_one, ← RCLike.ofReal_mul,
      ← RCLike.ofReal_sub, RCLike.ofReal_nonneg] at hd
    exact ⟨ha, hc, by nlinarith⟩
  · rw [hH.posSemidef_iff_trace_nonneg_and_det_nonneg, trace_fin_two, det_fin_two]
    simp only [of_apply, cons_val_zero, cons_val_one, cons_val_fin_one, ← RCLike.ofReal_add,
      ← RCLike.ofReal_mul, ← RCLike.ofReal_sub, RCLike.ofReal_nonneg]
    constructor <;> nlinarith

/-- **The square root of a positive-semidefinite `2 × 2` matrix.** If `H` is positive semidefinite
with trace `t` and determinant `δ`, then `√H = (t + 2 √δ) ^ (-1 / 2) • (H + √δ • 1)`. For `H = 0`
both sides vanish, and for `det H = 1` this reads `√H = (t + 2) ^ (-1 / 2) • (H + 1)`. -/
theorem PosSemidef.sqrt_fin_two {H : Matrix (Fin 2) (Fin 2) 𝕜} (hH : H.PosSemidef) :
    CFC.sqrt H = (√(RCLike.re H.trace + 2 * √(RCLike.re H.det)))⁻¹ •
      (H + √(RCLike.re H.det) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  obtain ⟨t, ht0, ht⟩ := RCLike.nonneg_iff_exists_ofReal.mp hH.trace_nonneg
  obtain ⟨δ, hδ0, hδ⟩ := RCLike.nonneg_iff_exists_ofReal.mp hH.det_nonneg
  rw [← ht, ← hδ, RCLike.ofReal_re, RCLike.ofReal_re]
  have hd0 : 0 ≤ √δ := Real.sqrt_nonneg δ
  -- Cayley–Hamilton for `2 × 2` matrices.
  have hCH : H * H = t • H - δ • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
    rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, ← ht, ← hδ,
      RCLike.real_smul_eq_coe_smul (K := 𝕜) t, RCLike.real_smul_eq_coe_smul (K := 𝕜) δ]
  have hsq : (H + √δ • 1) * (H + √δ • 1) = (t + 2 * √δ) • H := calc
    _ = H * H + (2 * √δ) • H + (√δ * √δ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    _ = (t + 2 * √δ) • H := by
      rw [hCH, Real.mul_self_sqrt hδ0]
      module
  have hQ : (H + √δ • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).PosSemidef :=
    hH.add (PosSemidef.one.smul hd0)
  refine CFC.sqrt_unique ?_ (nonneg_iff_posSemidef.mpr (hQ.smul (inv_nonneg.mpr
    (Real.sqrt_nonneg _))))
  rw [smul_mul_smul, hsq, smul_smul]
  rcases (add_nonneg ht0 (mul_nonneg zero_le_two hd0)).eq_or_lt with hs | hs
  · -- A positive-semidefinite matrix with trace `0` is `0`.
    have htd : t = 0 := by linarith [mul_nonneg zero_le_two hd0]
    rw [← hs, mul_zero, zero_smul, eq_comm, ← hH.trace_eq_zero_iff, ← ht, htd,
      RCLike.ofReal_zero]
  · rw [← mul_inv, Real.mul_self_sqrt hs.le, inv_mul_cancel₀ hs.ne', one_smul]

end Matrix
