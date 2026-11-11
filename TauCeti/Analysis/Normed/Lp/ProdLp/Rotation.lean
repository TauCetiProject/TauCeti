/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Tactic.LinearCombination

/-!
# Rotations of the Euclidean plane `WithLp 2 (ℝ × ℝ)` in coordinates

For real numbers `α` and `β` with `α ^ 2 + β ^ 2 = 1`, `TauCeti.prodRotation α β h` is the linear
isometry of `WithLp 2 (ℝ × ℝ)` with matrix `!![α, β; -β, α]`, and
`TauCeti.prodRecentredRotation α β h p` is the rigid motion `x ↦ prodRotation α β h (x - p)`,
which moves `p` to the origin. Mathlib's `Orientation.rotation` and `rotation` describe plane
rotations of an oriented two-dimensional inner product space and of `ℂ` by an angle or a unit
complex number; the definitions here record the explicit coordinates on the `L²` product, as
needed to write boundary charts of planar domains.

## Main definitions

* `TauCeti.prodRotation α β h`: the rotation of `WithLp 2 (ℝ × ℝ)` with first row `(α, β)`.
* `TauCeti.prodRecentredRotation α β h p`: the rigid motion `x ↦ prodRotation α β h (x - p)`.
-/

public section

noncomputable section

namespace TauCeti

/-- The rotation of `WithLp 2 (ℝ × ℝ)` with first row `(α, β)`, that is with matrix
`!![α, β; -β, α]`. -/
def prodRotation (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (α * x.fst + β * x.snd, -β * x.fst + α * x.snd)
  invFun z := WithLp.toLp 2 (α * z.fst - β * z.snd, β * z.fst + α * z.snd)
  map_add' x y := WithLp.ofLp_injective 2 <| Prod.ext (by simp; ring) (by simp; ring)
  map_smul' c x := WithLp.ofLp_injective 2 <| Prod.ext (by simp; ring) (by simp; ring)
  left_inv x := WithLp.ofLp_injective 2 <| Prod.ext (by simp; linear_combination x.fst * h)
    (by simp; linear_combination x.snd * h)
  right_inv z := WithLp.ofLp_injective 2 <| Prod.ext (by simp; linear_combination z.fst * h)
    (by simp; linear_combination z.snd * h)
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.prod_norm_eq_of_L2,
      WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
    congr 1
    linear_combination (x.fst ^ 2 + x.snd ^ 2) * h

/-- The first coordinate of `TauCeti.prodRotation α β h x` is `α x₁ + β x₂`. -/
@[simp]
theorem prodRotation_apply_fst (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (x : WithLp 2 (ℝ × ℝ)) :
    (prodRotation α β h x).fst = α * x.fst + β * x.snd :=
  (rfl)

/-- The second coordinate of `TauCeti.prodRotation α β h x` is `-β x₁ + α x₂`. -/
@[simp]
theorem prodRotation_apply_snd (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (x : WithLp 2 (ℝ × ℝ)) :
    (prodRotation α β h x).snd = -β * x.fst + α * x.snd :=
  (rfl)

/-- The first coordinate of the inverse rotation applied to `z` is `α z₁ - β z₂`. -/
@[simp]
theorem prodRotation_symm_apply_fst (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (z : WithLp 2 (ℝ × ℝ)) :
    ((prodRotation α β h).symm z).fst = α * z.fst - β * z.snd :=
  (rfl)

/-- The second coordinate of the inverse rotation applied to `z` is `β z₁ + α z₂`. -/
@[simp]
theorem prodRotation_symm_apply_snd (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (z : WithLp 2 (ℝ × ℝ)) :
    ((prodRotation α β h).symm z).snd = β * z.fst + α * z.snd :=
  (rfl)

/-- The rigid motion `x ↦ prodRotation α β h (x - p)` of `WithLp 2 (ℝ × ℝ)`, which moves `p` to the
origin and then rotates. -/
def prodRecentredRotation (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (p : WithLp 2 (ℝ × ℝ)) :
    WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (AffineIsometryEquiv.constVAdd ℝ _ (-p)).trans (prodRotation α β h).toAffineIsometryEquiv

/-- `TauCeti.prodRecentredRotation α β h p` translates `p` to the origin and then rotates. -/
theorem prodRecentredRotation_apply (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) (p x : WithLp 2 (ℝ × ℝ)) :
    prodRecentredRotation α β h p x = prodRotation α β h (x - p) := by
  simp [prodRecentredRotation, sub_eq_neg_add]

/-- `TauCeti.prodRecentredRotation α β h p` moves `p` to the origin. -/
@[simp]
theorem prodRecentredRotation_apply_self (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p : WithLp 2 (ℝ × ℝ)) : prodRecentredRotation α β h p p = 0 := by
  simp [prodRecentredRotation_apply]

/-- The first coordinate of `TauCeti.prodRecentredRotation α β h p x`. -/
@[simp]
theorem prodRecentredRotation_apply_fst (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p x : WithLp 2 (ℝ × ℝ)) :
    (prodRecentredRotation α β h p x).fst = α * (x.fst - p.fst) + β * (x.snd - p.snd) := by
  rw [prodRecentredRotation_apply, prodRotation_apply_fst, WithLp.sub_fst, WithLp.sub_snd]

/-- The second coordinate of `TauCeti.prodRecentredRotation α β h p x`. -/
@[simp]
theorem prodRecentredRotation_apply_snd (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p x : WithLp 2 (ℝ × ℝ)) :
    (prodRecentredRotation α β h p x).snd = -β * (x.fst - p.fst) + α * (x.snd - p.snd) := by
  rw [prodRecentredRotation_apply, prodRotation_apply_snd, WithLp.sub_fst, WithLp.sub_snd]

/-- The inverse of `TauCeti.prodRecentredRotation α β h p` rotates back and then translates the
origin to `p`. -/
theorem prodRecentredRotation_symm_apply (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p z : WithLp 2 (ℝ × ℝ)) :
    (prodRecentredRotation α β h p).symm z = p + (prodRotation α β h).symm z := by
  rw [AffineIsometryEquiv.symm_apply_eq, prodRecentredRotation_apply, add_sub_cancel_left,
    LinearIsometryEquiv.apply_symm_apply]

/-- The first coordinate of the inverse of `TauCeti.prodRecentredRotation α β h p`. -/
@[simp]
theorem prodRecentredRotation_symm_apply_fst (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p z : WithLp 2 (ℝ × ℝ)) :
    ((prodRecentredRotation α β h p).symm z).fst = p.fst + (α * z.fst - β * z.snd) := by
  simp [prodRecentredRotation_symm_apply]

/-- The second coordinate of the inverse of `TauCeti.prodRecentredRotation α β h p`. -/
@[simp]
theorem prodRecentredRotation_symm_apply_snd (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (p z : WithLp 2 (ℝ × ℝ)) :
    ((prodRecentredRotation α β h p).symm z).snd = p.snd + (β * z.fst + α * z.snd) := by
  simp [prodRecentredRotation_symm_apply]

end TauCeti
