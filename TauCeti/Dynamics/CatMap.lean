/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic
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
* `det (1 - t P) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`.

## Main results

* `TauCeti.catMap`, `TauCeti.catMap_def`: the matrix `!![2, 1; 1, 1]`.
* `TauCeti.reindex_catMap_mem_symplecticGroup`: `P` is symplectic.
* `TauCeti.charpolyRev_catMap`, `TauCeti.det_one_sub_catMap`: `det (1 - t P)` and `det (1 - P)`.
* `TauCeti.det_one_sub_catMap_pow_neg`: `det (1 - P ^ n) < 0` for `n ≠ 0`.
* `TauCeti.coe_charpolyRev_catMap_mul_mk_one_sq`: the expansion of `det (1 - t P) / (1 - t) ^ 2`.
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
theorem det_one_sub_catMap_pow_neg {n : ℕ} (hn : n ≠ 0) : (1 - catMap ^ n).det < 0 := by
  -- `1 - P ^ n` is the pencil at `r = s = -1`, so `det (1 - P ^ n) = 2 - tr (P ^ n)`; and
  -- `tr (P ^ n) > 2` since `det P = 1` and `tr P = 3 > 2`.
  have h := Matrix.det_smul_sub_smul_one_fin_two (catMap ^ n) (-1) (-1)
  simp only [neg_smul, one_smul, sub_neg_eq_add, neg_add_eq_sub, det_pow, det_catMap,
    one_pow] at h
  have := two_lt_trace_pow det_catMap (by decide) hn
  linarith

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

end TauCeti
