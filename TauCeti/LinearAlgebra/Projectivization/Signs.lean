/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import TauCeti.LinearAlgebra.Projectivization.AffineChart

/-!
# Sign changes of the homogeneous coordinates

The group `ι → ℤˣ` of sign changes of the coordinates acts on `ι → K` commuting with the scalars
(`TauCeti.instSMulCommClassSigns`), so it acts on the projective space `ℙ K (ι → K)` through
Mathlib's `Projectivization.instMulAction`. The sign changes preserve the standard affine opens
(`TauCeti.signs_smul_mem_affineOpen_iff`), and in the affine chart at `k` the sign change `ε`
changes the signs of the affine coordinates by `TauCeti.chartSigns ε k`
(`TauCeti.affineChart_signs_smul`). The reflection `Pi.mulSingle b (-1)` changes the signs of all
of them when `b = k` (`TauCeti.chartSigns_mulSingle_neg_one_self`) and of exactly one otherwise
(`TauCeti.prod_chartSigns_mulSingle_neg_one_of_ne`). The sign changes fix the coordinate points
`[eₖ]` (`TauCeti.signs_smul_mk_single`), and, away from characteristic two, the only fixed point
of the reflection `Pi.mulSingle k (-1)` negating the `k`-th coordinate in the affine open at `k` is
`[eₖ]` (`TauCeti.eq_mk_single_of_mulSingle_neg_one_smul_eq`): the other fixed points form the
hyperplane `v k = 0`.
-/

public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- The sign changes of the coordinates commute with scalars, so they act on projective space
(`Projectivization.instMulAction`). -/
instance instSMulCommClassSigns {ι K : Type*} [Ring K] : SMulCommClass (ι → ℤˣ) K (ι → K) :=
  SMulCommClass.symm _ _ _

/-- The sign changes preserve the affine open sets of the standard charts. -/
@[simp]
theorem signs_smul_mem_affineOpen_iff {ι K : Type*} [DivisionRing K] (ε : ι → ℤˣ) (k : ι)
    (x : ℙ K (ι → K)) : ε • x ∈ affineOpen k ↔ x ∈ affineOpen k := by
  induction x using ind with | h v hv =>
  rw [smul_mk, mk_mem_affineOpen_iff, mk_mem_affineOpen_iff, Pi.smul_apply',
    smul_ne_zero_iff_ne]

/-- **The sign changes fix the coordinate points.** -/
theorem signs_smul_mk_single {ι K : Type*} [DecidableEq ι] [DivisionRing K] (ε : ι → ℤˣ) (k : ι) :
    ε • mk K ((Pi.single k 1 : ι → K)) (by simp) = mk K ((Pi.single k 1 : ι → K)) (by simp) := by
  rw [smul_mk, mk_eq_mk_iff']
  refine ⟨((ε k : ℤ) : K), funext fun i ↦ ?_⟩
  rcases eq_or_ne i k with rfl | hi <;> simp [Units.smul_def, *]

/-- **Fixed points of a reflection.** Away from characteristic two, a point of the affine open at
`k` fixed by the reflection `Pi.mulSingle k (-1)`, which negates the `k`-th homogeneous
coordinate, is the coordinate point `[eₖ]`. -/
theorem eq_mk_single_of_mulSingle_neg_one_smul_eq {ι K : Type*} [DecidableEq ι] [Field K]
    [NeZero (2 : K)] {k : ι} {x : ℙ K (ι → K)} (h : (Pi.mulSingle k (-1) : ι → ℤˣ) • x = x)
    (hx : x ∈ affineOpen k) : x = mk K ((Pi.single k 1 : ι → K)) (by simp) := by
  induction x using ind with | h v hv =>
  rw [mk_mem_affineOpen_iff] at hx
  rw [smul_mk, mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  -- The scalar is `-1`, read on the `k`-th coordinate.
  have hk := congrFun ha k
  simp only [Pi.smul_apply', Pi.mulSingle_eq_same, Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul, Pi.smul_apply, smul_eq_mul] at hk
  have ha1 : a = -1 := mul_right_cancel₀ hx (by rw [hk, neg_one_mul])
  -- So every other coordinate equals its negative, and vanishes.
  have hv' : v = v k • Pi.single k 1 := funext fun i ↦ by
    rcases eq_or_ne i k with rfl | hi
    · simp
    have hi' := congrFun ha i
    simp only [Pi.smul_apply', Pi.mulSingle_eq_of_ne hi, one_smul, Pi.smul_apply, smul_eq_mul,
      ha1, neg_one_mul] at hi'
    have h2 : (2 : K) * v i = 0 := by linear_combination -hi'
    simp [hi, (mul_eq_zero.1 h2).resolve_left two_ne_zero]
  rw [mk_eq_mk_iff']
  exact ⟨v k, hv'.symm⟩

variable {n : ℕ}

/-- The signs by which a sign change `ε` acts on the affine coordinates of the chart at `k`:
the ratio `v (k.succAbove j) / v k` is multiplied by `ε (k.succAbove j) * ε k`. -/
def chartSigns (ε : Fin (n + 1) → ℤˣ) (k : Fin (n + 1)) : Fin n → ℤˣ :=
  fun j ↦ ε (k.succAbove j) * ε k

/-- The `j`-th sign of `chartSigns ε k` is `ε (k.succAbove j) * ε k`. -/
@[simp]
theorem chartSigns_apply (ε : Fin (n + 1) → ℤˣ) (k : Fin (n + 1)) (j : Fin n) :
    chartSigns ε k j = ε (k.succAbove j) * ε k :=
  (rfl)

/-- In the affine chart at `k`, the reflection negating the `k`-th coordinate changes the sign of
every affine coordinate. -/
@[simp]
theorem chartSigns_mulSingle_neg_one_self (k : Fin (n + 1)) :
    chartSigns (Pi.mulSingle k (-1) : Fin (n + 1) → ℤˣ) k = -1 := by
  ext j
  simp

/-- In the affine chart at `a`, the reflection negating another coordinate `b` changes the sign of
exactly one affine coordinate, so the product of its signs is `-1`. -/
theorem prod_chartSigns_mulSingle_neg_one_of_ne {a b : Fin (n + 1)} (hab : a ≠ b) :
    ∏ j, chartSigns (Pi.mulSingle b (-1) : Fin (n + 1) → ℤˣ) a j = -1 := by
  have h := Fin.prod_univ_succAbove (Pi.mulSingle b (-1) : Fin (n + 1) → ℤˣ) a
  simp only [Finset.prod_pi_mulSingle', Finset.mem_univ, ↓reduceIte, Pi.mulSingle_eq_of_ne hab,
    one_mul] at h
  simp [Pi.mulSingle_eq_of_ne hab, ← h]

/-- In the affine chart at `k`, the sign change `ε` changes the signs of the coordinates by
`chartSigns ε k`. -/
theorem affineChart_signs_smul {K : Type*} [Field K] (ε : Fin (n + 1) → ℤˣ) (k : Fin (n + 1))
    (x : ℙ K (Fin (n + 1) → K)) :
    affineChart k (ε • x) = chartSigns ε k • affineChart k x := by
  induction x using ind with | h v hv =>
  ext j
  have hk : ((ε k : ℤ) : K) * (ε k : ℤ) = 1 := by
    rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  simp only [smul_mk, affineChart_mk, Pi.smul_apply', chartSigns_apply, Units.smul_def,
    zsmul_eq_mul, Units.val_mul, Int.cast_mul]
  rw [mul_div_mul_comm, div_eq_mul_inv ((ε (k.succAbove j) : ℤ) : K),
    inv_eq_of_mul_eq_one_right hk]

end TauCeti
