/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Arnold's cat map

The integer matrix `P = !![2, 1; 1, 1]` induces Arnold's cat map, a hyperbolic area-preserving
automorphism of the torus `ℝ² / ℤ²`. Being symmetric, `P` is also the matrix of the action of the
cat map on `H¹(T²; ℤ)` in the dual basis. This file records
the numerical data of `P` that enter the zeta function of its iterates:

* `P` is symplectic, so the general results of
  `TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic` apply with genus `g = 1`;
* `det (1 - t P) = 1 - 3 t + t ^ 2` and `det (1 - P) = -1`;
* every iterate is nondegenerate: `det (1 - P ^ n) < 0` for `n ≥ 1`, so `1` is never an eigenvalue
  of `P ^ n`;
* `det (1 - t P) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`;
* this is the homological zeta function `exp (∑ₙ L (φ ^ n) tⁿ / n)` of the cat map `φ`, whose
  Lefschetz numbers `L (φ ^ n) = 2 - tr (P ^ n)` come from its action by `1`, `P` and `det P = 1`
  on `H₀`, `H₁` and `H₂` of the torus.

## Main results

* `TauCeti.catMap`, `TauCeti.catMap_def`: the matrix `!![2, 1; 1, 1]`.
* `TauCeti.reindex_catMap_mem_symplecticGroup`: `P` is symplectic.
* `TauCeti.charpolyRev_catMap`, `TauCeti.det_one_sub_catMap`: `det (1 - t P)` and `det (1 - P)`.
* `TauCeti.det_one_sub_catMap_pow_neg`: `det (1 - P ^ n) < 0` for `n ≠ 0`.
* `TauCeti.coe_charpolyRev_catMap_mul_mk_one_sq`: the expansion of `det (1 - t P) / (1 - t) ^ 2`.
* `TauCeti.subst_exp_two_sub_trace_catMap_pow`: the homological zeta function of the cat map is
  `1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`.
-/

public section

open Polynomial Matrix

namespace TauCeti

/-- The integer matrix `!![2, 1; 1, 1]` of Arnold's cat map, the hyperbolic automorphism of the
torus `ℝ² / ℤ²` that it induces. -/
def catMap : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

/-- The entries of the cat map. -/
theorem catMap_def : catMap = !![2, 1; 1, 1] := (rfl)

/-- The cat map is symplectic, once its two coordinates are indexed by `Fin 1 ⊕ Fin 1`. -/
theorem reindex_catMap_mem_symplecticGroup :
    reindex finSumFinEquiv.symm finSumFinEquiv.symm catMap ∈ symplecticGroup (Fin 1) ℤ := by
  rw [SymplecticGroup.mem_iff]
  decide

/-- The cat map has determinant `1`. -/
@[simp]
theorem det_catMap : catMap.det = 1 := by
  decide

/-- The reversed characteristic polynomial of the cat map is `det (1 - t P) = 1 - 3 t + t ^ 2`. -/
@[simp]
theorem charpolyRev_catMap : catMap.charpolyRev = 1 - 3 * X + X ^ 2 := by
  rw [charpolyRev, det_fin_two]
  simp [catMap_def]
  ring

/-- `det (1 - P) = -1` for the cat map `P`. -/
@[simp]
theorem det_one_sub_catMap : (1 - catMap).det = -1 := by
  decide

/-- Every iterate of the cat map is nondegenerate: `det (1 - P ^ n)` is negative for `n ≠ 0`, so
`1` is not an eigenvalue of `P ^ n`. -/
theorem det_one_sub_catMap_pow_neg {n : ℕ} (hn : n ≠ 0) : (1 - catMap ^ n).det < 0 :=
  det_one_sub_pow_neg_of_two_lt_trace det_catMap (by decide) hn

/-- The coefficient of `t ^ n` in `det (1 - t P) / (1 - t) ^ 2` is `-n` for `n ≠ 0`. This is the
genus-one case `det (1 - P) (n + 1 - g)` of
`SymplecticGroup.coeff_coe_charpolyRev_mul_mk_one_sq`. -/
theorem coeff_coe_charpolyRev_catMap_mul_mk_one_sq {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n ((catMap.charpolyRev : PowerSeries ℤ) * PowerSeries.mk 1 ^ 2) =
      -(n : ℤ) := by
  have h := SymplecticGroup.coeff_coe_charpolyRev_mul_mk_one_sq
    reindex_catMap_mem_symplecticGroup (a := n) (by simp; omega)
  have hdet (e : Fin 2 ≃ Fin 1 ⊕ Fin 1) : (1 - reindex e e catMap).det = (1 - catMap).det := by
    rw [← det_reindex_self e (1 - catMap)]
    simp [submatrix_sub]
  rw [charpolyRev_reindex] at h
  rw [h, hdet, det_one_sub_catMap]
  simp

/-- `det (1 - t P) / (1 - t) ^ 2 = (1 - 3 t + t ^ 2) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`
for the cat map `P`. -/
theorem coe_charpolyRev_catMap_mul_mk_one_sq :
    (catMap.charpolyRev : PowerSeries ℤ) * PowerSeries.mk 1 ^ 2 =
      PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℤ) := by
  ext n
  rw [PowerSeries.coeff_mk]
  split_ifs with hn
  · subst hn
    simp [charpolyRev_catMap]
  · exact coeff_coe_charpolyRev_catMap_mul_mk_one_sq hn

/-- **The homological zeta function of the cat map.** The cat map `φ` acts on `H₀`, `H₁` and `H₂`
of the torus by `1`, `P` and `det P = 1`, so the Lefschetz number of `φ ^ n` is
`L (φ ^ n) = 2 - tr (P ^ n)`. Its homological zeta function `exp (∑ₙ L (φ ^ n) tⁿ / n)` is
`det (1 - t P) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`, by the trace–determinant formula
`Matrix.logOf_charpolyRev`. -/
theorem subst_exp_two_sub_trace_catMap_pow :
    (PowerSeries.exp ℚ).subst
        (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (2 - ((catMap ^ n).trace : ℚ))) =
      PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ) := by
  set P := catMap.map (Int.castRingHom ℚ) with hP
  set L : PowerSeries ℚ := PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (2 - ((catMap ^ n).trace : ℚ))
  have htr (n : ℕ) : (((catMap ^ n).trace : ℤ) : ℚ) = (P ^ n).trace := by
    rw [hP, ← RingHom.mapMatrix_apply, ← map_pow]
    exact AddMonoidHom.map_trace (Int.castRingHom ℚ).toAddMonoidHom _
  have hL : PowerSeries.constantCoeff L = 0 := by simp [L]
  have hX : (1 - PowerSeries.X : PowerSeries ℚ) = 1 - PowerSeries.C 1 * PowerSeries.X := by
    rw [map_one, one_mul]
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries ℚ) = 1 := by simp
  -- `exp L (1 - t) ^ 2 = det (1 - t P)`, comparing logarithms.
  have hkey : (PowerSeries.exp ℚ).subst L * (1 - PowerSeries.X) ^ 2 =
      (P.charpolyRev : PowerSeries ℚ) := by
    rw [← PowerSeries.logOf_inj (by simp [hL]) (Matrix.constantCoeff_coe_charpolyRev P), pow_two,
      PowerSeries.logOf_mul (PowerSeries.constantCoeff_subst_exp hL) (by simp),
      PowerSeries.logOf_mul hc hc, PowerSeries.logOf_subst_exp hL, Matrix.logOf_charpolyRev, hX,
      PowerSeries.logOf_one_sub_C_mul_X]
    ext n
    simp only [L, map_add, PowerSeries.coeff_mk, htr, one_pow]
    rw [← smul_add, ← smul_add]
    congr 1
    ring
  have hone : (1 - PowerSeries.X : PowerSeries ℚ) ^ 2 * PowerSeries.mk 1 ^ 2 = 1 := by
    rw [← mul_pow, mul_comm, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow]
  have hmk : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk 1) = PowerSeries.mk 1 := by
    ext n
    simp
  -- Map the integral expansion of `det (1 - t P) / (1 - t) ^ 2` to `ℚ`.
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) coe_charpolyRev_catMap_mul_mk_one_sq
  rw [map_mul, map_pow, ← Polynomial.polynomial_map_coe, ← charpolyRev_map, ← hP, hmk] at hmap
  rw [← mul_one ((PowerSeries.exp ℚ).subst L), ← hone, ← mul_assoc, hkey, hmap]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs <;> simp

end TauCeti
