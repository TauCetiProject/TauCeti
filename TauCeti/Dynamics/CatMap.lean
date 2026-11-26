/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TorusAutomorphism
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
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

The last section studies the actual cat map `φ(x) = P • x` of the torus
`Fin 2 → AddCircle p`, through the general results on linear automorphisms of tori in
`TauCeti.Dynamics.TorusAutomorphism`. Its iterates are `x ↦ Pⁿ • x`, with derivative `Pⁿ` at
every point, so:

* `φ` is nondegenerate up to every period: every periodic point of period `n` is a nondegenerate
  fixed point of `φⁿ`;
* for `n ≥ 1`, `φⁿ` has `|det (1 - Pⁿ)| = tr (Pⁿ) - 2` fixed points, each of Lefschetz sign
  `sgn det (1 - Pⁿ) = -1`, so their signed count is `det (1 - Pⁿ) = 2 - tr (Pⁿ)`, the Lefschetz
  number `L (φⁿ)` above. This checks the Lefschetz fixed-point formula on every iterate of the cat
  map, with the homological side taken from the description above rather than formalized;
* hence the dynamical zeta function `exp (∑ₙ (∑_{φⁿ x = x} sgn det (1 - dφⁿ_x)) tⁿ / n)`, built
  from the actual fixed points of the iterates and their linearizations, is
  `(1 - 3 t + t ^ 2) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`.

## Main results

* `TauCeti.catMap`, `TauCeti.catMap_def`: the matrix `!![2, 1; 1, 1]`.
* `TauCeti.reindex_catMap_mem_symplecticGroup`: `P` is symplectic.
* `TauCeti.charpolyRev_catMap`, `TauCeti.det_one_sub_catMap`: `det (1 - t P)` and `det (1 - P)`.
* `TauCeti.det_one_sub_catMap_pow_neg`: `det (1 - P ^ n) < 0` for `n ≠ 0`.
* `TauCeti.coe_charpolyRev_catMap_mul_mk_one_sq`: the expansion of `det (1 - t P) / (1 - t) ^ 2`.
* `TauCeti.subst_exp_two_sub_trace_catMap_pow`: the homological zeta function of the cat map is
  `1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`.
* `TauCeti.catMapUnit`: the cat map as an element of `GL(2, ℤ)`, acting on the torus.
* `TauCeti.isNondegenerateUpToPeriod_catMapUnit_smul`: the cat map of the torus is nondegenerate up
  to every period.
* `TauCeti.nat_card_fixedPoints_iterate_catMapUnit_smul`: `φⁿ` has `|2 - tr (Pⁿ)|` fixed points.
* `TauCeti.finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul`: their signed count
  is `2 - tr (Pⁿ)`.
* `TauCeti.subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul`: the
  dynamical zeta function of the cat map is `1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`.
-/

public section

open Function Polynomial Matrix
open scoped Manifold

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
case `n det (1 - P)` of `Matrix.coeff_coe_charpolyRev_mul_mk_one_sq_fin_two`, since `det P = 1`. -/
theorem coeff_coe_charpolyRev_catMap_mul_mk_one_sq {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n ((catMap.charpolyRev : PowerSeries ℤ) * PowerSeries.mk 1 ^ 2) =
      -(n : ℤ) := by
  rw [coeff_coe_charpolyRev_mul_mk_one_sq_fin_two det_catMap hn, det_one_sub_catMap, mul_neg_one]

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
`det (1 - t P) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`: the coefficient of `tⁿ` is
`n det (1 - P) = -n` for `n ≠ 0`, by
`Matrix.coeff_subst_exp_det_one_sub_pow_fin_two_of_det_eq_one`. -/
theorem subst_exp_two_sub_trace_catMap_pow :
    (PowerSeries.exp ℚ).subst
        (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (2 - ((catMap ^ n).trace : ℚ))) =
      PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ) := by
  set P := catMap.map (Int.castRingHom ℚ) with hP
  -- The Lefschetz numbers are `2 - tr (P ^ n) = det (1 - P ^ n)`.
  have hL (n : ℕ) : (2 - ((catMap ^ n).trace : ℚ)) = (1 - P ^ n).det := by
    rw [hP, ← Matrix.map_pow, ← intCast_det_one_sub,
      det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, det_catMap, one_pow])]
    push_cast
    ring
  have hP₁ : (1 - P).det = -1 := by
    rw [hP, ← intCast_det_one_sub, det_one_sub_catMap, Int.cast_neg, Int.cast_one]
  simp_rw [hL]
  ext n
  rw [PowerSeries.coeff_mk]
  split_ifs with hn
  · subst hn
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_subst_exp (by simp)]
  · rw [Matrix.coeff_subst_exp_det_one_sub_pow_fin_two_of_det_eq_one
      ((Int.castRingHom ℚ).det_map_eq_one det_catMap) hn, hP₁, mul_neg_one]

/-! ### The cat map of the torus -/

/-- Arnold's cat map as an invertible integer matrix, with inverse `!![1, -1; -1, 2]`. It acts on
the torus `Fin 2 → AddCircle p` by `AddCircle.instDistribMulActionGeneralLinearGroup`. -/
def catMapUnit : GL (Fin 2) ℤ where
  val := catMap
  inv := !![1, -1; -1, 2]
  val_inv := by
    rw [catMap_def]
    decide
  inv_val := by
    rw [catMap_def]
    decide

/-- The underlying matrix of `catMapUnit` is the cat map. -/
@[simp]
theorem coe_catMapUnit : (catMapUnit : Matrix (Fin 2) (Fin 2) ℤ) = catMap :=
  (rfl)

/-- `det (1 - Pⁿ) = 2 - tr (Pⁿ)` for the cat map `P`, since `det Pⁿ = 1`. -/
theorem det_one_sub_catMap_pow (n : ℕ) : (1 - catMap ^ n).det = 2 - (catMap ^ n).trace :=
  det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, det_catMap, one_pow])

/-- `det (1 - Pⁿ) = 2 - tr (Pⁿ)` for the `n`-th power of the cat map as an element of `GL(2, ℤ)`. -/
theorem det_one_sub_coe_catMapUnit_pow (n : ℕ) :
    (1 - ((catMapUnit ^ n : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)).det =
      2 - (catMap ^ n).trace := by
  rw [Units.val_pow_eq_pow_val, coe_catMapUnit, det_one_sub_catMap_pow]

variable (p : ℝ) [Fact (0 < p)]

/-- **Every iterate of the actual cat map is nondegenerate.** The cat map `x ↦ P • x` of the torus
`Fin 2 → AddCircle p` is nondegenerate up to every period `N`: a periodic point of period
`0 < k ≤ N` is a nondegenerate fixed point of the `k`-th iterate. -/
theorem isNondegenerateUpToPeriod_catMapUnit_smul (N : ℕ) :
    IsNondegenerateUpToPeriod (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
      (fun x : Fin 2 → AddCircle p ↦ catMapUnit • x) N :=
  (AddCircle.isNondegenerateUpToPeriod_generalLinearGroup_smul_iff p catMapUnit N).2
    fun _ hk _ ↦ (det_one_sub_catMap_pow_neg hk.ne').ne

omit [Fact (0 < p)] in
/-- **The number of fixed points of the iterates of the cat map.** The `n`-th iterate of the cat
map of the torus has `|2 - tr (Pⁿ)| = |det (1 - Pⁿ)|` fixed points: one for `n = 1`, five for
`n = 2`, sixteen for `n = 3`. For `n = 0` every point is fixed and both sides are `0`. The period
`p` may be any nonzero real number. -/
theorem nat_card_fixedPoints_iterate_catMapUnit_smul (hp : p ≠ 0) (n : ℕ) :
    Nat.card (fixedPoints (fun x : Fin 2 → AddCircle p ↦ catMapUnit • x)^[n]) =
      (2 - (catMap ^ n).trace).natAbs := by
  rw [smul_iterate,
    AddCircle.nat_card_fixedPoints_generalLinearGroup_smul p _ hp,
    det_one_sub_coe_catMapUnit_pow]

/-- **The signed fixed-point counts of the cat map.** The fixed points of the `n`-th iterate `φⁿ`
of the cat map of the torus, each counted with its Lefschetz sign `sgn det (1 - dφⁿ_x)`, add up to
`2 - tr (Pⁿ)`, which is the Lefschetz number `L (φⁿ)` computed from the action of `φ` on the
homology of the torus. For `n ≥ 1`, every sign is `-1`, and there are `tr (Pⁿ) - 2` fixed points;
for `n = 0`, every sign is `0` and both sides are `0`. -/
theorem finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul (n : ℕ) :
    ∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ catMapUnit • y)^[n] x = x},
        (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
          (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ catMapUnit • y)^[n] x)) : ℤ) =
      2 - (catMap ^ n).trace := by
  rw [AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul,
    coe_catMapUnit, det_one_sub_catMap_pow]

/-- **The dynamical zeta function of the cat map.** The zeta function
`exp (∑ₙ (∑_{φⁿ x = x} sgn det (1 - dφⁿ_x)) tⁿ / n)` of the actual cat map `φ` of the torus,
computed from the fixed points of its iterates and their Lefschetz signs, is
`(1 - 3 t + t ^ 2) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯`. It agrees with the homological
zeta function `TauCeti.subst_exp_two_sub_trace_catMap_pow`. -/
theorem subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul :
    (PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ catMapUnit • y)^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ catMapUnit • y)^[n] x)) : ℤ) :
          ℤ) : ℚ)) =
      PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ) := by
  rw [← subst_exp_two_sub_trace_catMap_pow]
  congr 2
  ext n
  rw [finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul, Int.cast_sub,
    Int.cast_ofNat]

end TauCeti
