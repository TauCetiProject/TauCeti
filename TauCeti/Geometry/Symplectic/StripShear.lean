/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The shear of the strip with twist `c`

Let `R_c(x, y) = (x + c y, y)` be the shear of the plane `ℝ × ℝ` with twist `c`
(`TauCeti.stripShear c`). For `c > 0` it is a positive twist map: writing `X` for the first
component of a map, `R_c` has `∂ₓ X = 1 > 0` and `∂_y X = c > 0`. Its inverse is `R_(-c)`
(`TauCeti.stripShear_symm`), shears compose by adding their twists
(`TauCeti.stripShear_trans_stripShear`), and `R_c` has determinant `1`
(`TauCeti.det_stripShear`). It fixes the line `y = 0` pointwise, maps the line `y = 1` into
itself, and commutes with the deck translation `(x, y) ↦ (x + 1, y)` of the strip `ℝ × [0, 1]`
over the closed annulus (`TauCeti.stripShear_add_fst`).

## Main definitions

* `TauCeti.stripShear c`: the shear `(x, y) ↦ (x + c y, y)` as a continuous linear equivalence.
-/

public section

noncomputable section

namespace TauCeti

/-- The **shear** `R_c(x, y) = (x + c y, y)` of the plane `ℝ × ℝ`, with twist `c`. -/
def stripShear (c : ℝ) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ (p.1 + c * p.2, p.2)
      invFun := fun p ↦ (p.1 - c * p.2, p.2)
      map_add' := fun p q ↦ Prod.ext (by simp only [Prod.fst_add, Prod.snd_add]; ring) rfl
      map_smul' := fun a p ↦ Prod.ext
        (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring) rfl
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp }

@[simp]
theorem stripShear_apply (c : ℝ) (p : ℝ × ℝ) : stripShear c p = (p.1 + c * p.2, p.2) :=
  (rfl)

@[simp]
theorem stripShear_symm_apply (c : ℝ) (p : ℝ × ℝ) :
    (stripShear c).symm p = (p.1 - c * p.2, p.2) :=
  (rfl)

/-- The inverse of the shear with twist `c` is the shear with twist `-c`. -/
theorem stripShear_symm (c : ℝ) : (stripShear c).symm = stripShear (-c) := by
  ext p <;> simp [sub_eq_add_neg]

/-- Shears compose by adding their twists. -/
@[simp]
theorem stripShear_trans_stripShear (a b : ℝ) :
    (stripShear a).trans (stripShear b) = stripShear (a + b) := by
  ext p <;> simp only [ContinuousLinearEquiv.trans_apply, stripShear_apply]; ring

@[simp]
theorem stripShear_zero : stripShear 0 = ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) := by
  ext p <;> simp

/-- The shear preserves area: its determinant is `1`. -/
@[simp]
theorem det_stripShear (c : ℝ) : (stripShear c : ℝ × ℝ →L[ℝ] ℝ × ℝ).det = 1 := by
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp

/-- The shear commutes with the horizontal translations `(x, y) ↦ (x + a, y)`, in particular with
the deck translation of the strip. -/
theorem stripShear_add_fst (c a : ℝ) (p : ℝ × ℝ) :
    stripShear c (p + (a, 0)) = stripShear c p + (a, 0) := by
  ext <;> simp only [stripShear_apply, Prod.fst_add, Prod.snd_add, add_zero]; ring

end TauCeti
