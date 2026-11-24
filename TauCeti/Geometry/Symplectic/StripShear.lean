/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The shear of the strip with twist `c`

Let `R_c(x, y) = (x + c y, y)` be the shear of the plane `ℝ × ℝ` with twist `c`
(`TauCeti.stripShear c`), the transvection `p ↦ p + p.2 • (c, 0)` of Mathlib's
`LinearEquiv.transvection` (`TauCeti.toLinearEquiv_stripShear`). For `c > 0` it is a positive
twist map: writing `X` for the first component of a map, `R_c` has `∂ₓ X = 1 > 0` and
`∂_y X = c > 0`. Its inverse is `R_(-c)` (`TauCeti.stripShear_symm`), shears compose by adding
their twists (`TauCeti.stripShear_trans_stripShear`), and `R_c` has determinant `1`
(`TauCeti.det_stripShear`). It fixes the line `y = 0` pointwise, maps the line `y = 1` into
itself, and commutes with the deck translation `(x, y) ↦ (x + 1, y)` of the strip `ℝ × [0, 1]`
over the closed annulus (`TauCeti.stripShear_add_fst`).

## Main definitions

* `TauCeti.stripShear c`: the shear `(x, y) ↦ (x + c y, y)` as a continuous linear equivalence.
-/

public section

noncomputable section

namespace TauCeti

/-- The **shear** `R_c(x, y) = (x + c y, y)` of the plane `ℝ × ℝ`, with twist `c`: the
transvection `p ↦ p + p.2 • (c, 0)`. -/
def stripShear (c : ℝ) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  (LinearEquiv.transvection (f := LinearMap.snd ℝ ℝ ℝ) (v := (c, (0 : ℝ)))
    (LinearMap.snd_apply _)).toContinuousLinearEquiv

/-- The shear with twist `c` is Mathlib's transvection `p ↦ p + p.2 • (c, 0)`. -/
theorem toLinearEquiv_stripShear (c : ℝ) :
    (stripShear c).toLinearEquiv = LinearEquiv.transvection (f := LinearMap.snd ℝ ℝ ℝ)
      (v := (c, (0 : ℝ))) (LinearMap.snd_apply _) :=
  LinearEquiv.toLinearEquiv_toContinuousLinearEquiv _

@[simp]
theorem stripShear_apply (c : ℝ) (p : ℝ × ℝ) : stripShear c p = (p.1 + c * p.2, p.2) := by
  simp [stripShear, LinearMap.transvection.apply, Prod.ext_iff, mul_comm]

/-- The inverse of the shear with twist `c` is the shear with twist `-c`. -/
theorem stripShear_symm (c : ℝ) : (stripShear c).symm = stripShear (-c) := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [ContinuousLinearEquiv.toLinearEquiv_symm, toLinearEquiv_stripShear, toLinearEquiv_stripShear,
    LinearEquiv.transvection.symm_eq (LinearMap.snd_apply _) (by simp)]
  simp_rw [Prod.neg_mk, neg_zero]

@[simp]
theorem stripShear_symm_apply (c : ℝ) (p : ℝ × ℝ) :
    (stripShear c).symm p = (p.1 - c * p.2, p.2) := by
  simp [stripShear_symm, sub_eq_add_neg]

/-- Shears compose by adding their twists. -/
@[simp]
theorem stripShear_trans_stripShear (a b : ℝ) :
    (stripShear a).trans (stripShear b) = stripShear (a + b) := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [ContinuousLinearEquiv.trans_toLinearEquiv, toLinearEquiv_stripShear, toLinearEquiv_stripShear,
    toLinearEquiv_stripShear, LinearEquiv.transvection.trans_of_left_eq (LinearMap.snd_apply _)
    (LinearMap.snd_apply _) (by simp)]
  simp_rw [Prod.mk_add_mk, add_zero, add_comm b a]

@[simp]
theorem stripShear_zero : stripShear 0 = ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [toLinearEquiv_stripShear]
  exact LinearEquiv.transvection.of_right_eq_zero (LinearMap.snd ℝ ℝ ℝ)

/-- The shear preserves area: like every transvection, it has determinant `1`. -/
@[simp]
theorem det_stripShear (c : ℝ) : (stripShear c : ℝ × ℝ →L[ℝ] ℝ × ℝ).det = 1 := by
  -- Both coercions of `stripShear c` to a linear map agree pointwise.
  have h : ((stripShear c : ℝ × ℝ →L[ℝ] ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) =
      ((stripShear c).toLinearEquiv : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) :=
    LinearMap.ext fun p ↦ by simp
  rw [ContinuousLinearMap.det, h, toLinearEquiv_stripShear, ← LinearEquiv.coe_det,
    LinearEquiv.transvection.det_eq_one, Units.val_one]

/-- The shear commutes with the horizontal translations `(x, y) ↦ (x + a, y)`, in particular with
the deck translation of the strip. -/
theorem stripShear_add_fst (c a : ℝ) (p : ℝ × ℝ) :
    stripShear c (p + (a, 0)) = stripShear c p + (a, 0) := by
  ext <;> simp only [stripShear_apply, Prod.fst_add, Prod.snd_add, add_zero]; ring

end TauCeti
