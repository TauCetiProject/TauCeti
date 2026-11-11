/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Rotations of the Euclidean plane in coordinates

For `α ^ 2 + β ^ 2 = 1`, the map `(s, t) ↦ (α s + β t, α t - β s)` is a linear isometry of the
Euclidean plane `WithLp 2 (ℝ × ℝ)`, with inverse `(s, t) ↦ (α s - β t, β s + α t)`. Composing it
with the translation taking a point `c` to the origin gives rigid coordinates of the plane
centred at `c`, described here by explicit coordinate formulas in both directions.

## Main declarations

* `TauCeti.prodL2Rotation`: the rotation `(s, t) ↦ (α s + β t, α t - β s)` of the Euclidean plane.
* `TauCeti.prodL2RotationChart`: the rigid coordinates `x ↦ R (x - c)` centred at `c`.
-/

public section

noncomputable section

namespace TauCeti

/-- The rotation `(s, t) ↦ (α s + β t, α t - β s)` of the Euclidean plane `WithLp 2 (ℝ × ℝ)`,
for `α ^ 2 + β ^ 2 = 1`. -/
@[expose] def prodL2Rotation (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (α * x.fst + β * x.snd, α * x.snd - β * x.fst)
  invFun z := WithLp.toLp 2 (α * z.fst - β * z.snd, β * z.fst + α * z.snd)
  map_add' x y := (WithLp.ext_iff 2).2 (Prod.ext (by simp; ring) (by simp; ring))
  map_smul' c x := (WithLp.ext_iff 2).2 (Prod.ext (by simp; ring) (by simp; ring))
  left_inv x := (WithLp.ext_iff 2).2 (Prod.ext
    (by simp only [WithLp.ofLp_fst, WithLp.toLp_fst, WithLp.toLp_snd]
        linear_combination x.fst * hαβ)
    (by simp only [WithLp.ofLp_snd, WithLp.toLp_fst, WithLp.toLp_snd]
        linear_combination x.snd * hαβ))
  right_inv z := (WithLp.ext_iff 2).2 (Prod.ext
    (by simp only [WithLp.ofLp_fst, WithLp.toLp_fst, WithLp.toLp_snd]
        linear_combination z.fst * hαβ)
    (by simp only [WithLp.ofLp_snd, WithLp.toLp_fst, WithLp.toLp_snd]
        linear_combination z.snd * hαβ))
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.toLp_fst,
      WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
    linear_combination (x.fst ^ 2 + x.snd ^ 2) * hαβ

section Rotation

variable (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) (x : WithLp 2 (ℝ × ℝ))

/-- The first coordinate of a rotation. -/
@[simp]
theorem prodL2Rotation_apply_fst : (prodL2Rotation α β hαβ x).fst = α * x.fst + β * x.snd :=
  rfl

/-- The second coordinate of a rotation. -/
@[simp]
theorem prodL2Rotation_apply_snd : (prodL2Rotation α β hαβ x).snd = α * x.snd - β * x.fst :=
  rfl

/-- The first coordinate of the inverse of a rotation. -/
@[simp]
theorem prodL2Rotation_symm_apply_fst :
    ((prodL2Rotation α β hαβ).symm x).fst = α * x.fst - β * x.snd :=
  rfl

/-- The second coordinate of the inverse of a rotation. -/
@[simp]
theorem prodL2Rotation_symm_apply_snd :
    ((prodL2Rotation α β hαβ).symm x).snd = β * x.fst + α * x.snd :=
  rfl

end Rotation

/-- The rigid coordinates `x ↦ R (x - c)` of the plane, centred at `c`, for the rotation
`R = prodL2Rotation α β hαβ`. -/
def prodL2RotationChart (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (AffineIsometryEquiv.vaddConst ℝ c).symm.trans (prodL2Rotation α β hαβ).toAffineIsometryEquiv

section RotationChart

variable (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) (x : WithLp 2 (ℝ × ℝ))

/-- The rotation chart sends its centre to the origin. -/
@[simp]
theorem prodL2RotationChart_apply_self : prodL2RotationChart c α β hαβ c = 0 := by
  simp [prodL2RotationChart]

/-- The first coordinate of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_apply_fst :
    (prodL2RotationChart c α β hαβ x).fst = α * (x.fst - c.fst) + β * (x.snd - c.snd) := by
  simp [prodL2RotationChart]
  ring

/-- The second coordinate of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_apply_snd :
    (prodL2RotationChart c α β hαβ x).snd = α * (x.snd - c.snd) - β * (x.fst - c.fst) := by
  simp [prodL2RotationChart]
  ring

/-- The first coordinate of the inverse of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_symm_apply_fst :
    ((prodL2RotationChart c α β hαβ).symm x).fst = c.fst + (α * x.fst - β * x.snd) :=
  (add_comm ((prodL2Rotation α β hαβ).symm x).fst c.fst).trans
    (congrArg (c.fst + ·) (prodL2Rotation_symm_apply_fst α β hαβ x))

/-- The second coordinate of the inverse of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_symm_apply_snd :
    ((prodL2RotationChart c α β hαβ).symm x).snd = c.snd + (β * x.fst + α * x.snd) :=
  (add_comm ((prodL2Rotation α β hαβ).symm x).snd c.snd).trans
    (congrArg (c.snd + ·) (prodL2Rotation_symm_apply_snd α β hαβ x))

end RotationChart

end TauCeti
