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
(`TauCeti.affineChart_signs_smul`).
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
