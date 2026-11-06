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
# The square root of a positive-semidefinite `2 × 2` matrix

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
