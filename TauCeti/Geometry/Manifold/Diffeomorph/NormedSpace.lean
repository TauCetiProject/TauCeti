/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Elementary diffeomorphisms of a normed space

The map `x ↦ a - x` of a normed space `E` is a diffeomorphism of `E`, of any smoothness, which is
its own inverse (`Diffeomorph.subLeft`, the smooth counterpart of `Equiv.subLeft`). On the real
line, `Diffeomorph.subLeft 1` is the reflection `t ↦ 1 - t` exchanging `0` and `1`.

For a nonzero scalar `a`, the affine map `x ↦ a • x + b` is a diffeomorphism of `E`, of any
smoothness, with inverse `y ↦ a⁻¹ • (y - b)` (`Diffeomorph.smulAdd`). On the real line these are
the affine changes of time `t ↦ a * t + b`.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ∞ω}

variable (𝕜 n) in
/-- The map `x ↦ a - x` of a normed space, as a diffeomorphism. It is its own inverse
(`Diffeomorph.symm_subLeft`). -/
def subLeft (a : E) : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E where
  toFun x := a - x
  invFun x := a - x
  left_inv x := sub_sub_cancel a x
  right_inv x := sub_sub_cancel a x
  contMDiff_toFun := (contDiff_const.sub contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.sub contDiff_id).contMDiff

/-- `Diffeomorph.subLeft 𝕜 n a` sends `x` to `a - x`. -/
@[simp]
theorem subLeft_apply (a x : E) : subLeft 𝕜 n a x = a - x :=
  (rfl)

/-- `Diffeomorph.subLeft 𝕜 n a` is its own inverse. -/
@[simp]
theorem symm_subLeft (a : E) : (subLeft 𝕜 n a).symm = subLeft 𝕜 n a :=
  (rfl)

variable (n) in
/-- The affine map `x ↦ a • x + b` of a normed space, for a nonzero scalar `a`, as a
diffeomorphism. -/
def smulAdd (a : 𝕜) (b : E) (ha : a ≠ 0) : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E where
  toFun x := a • x + b
  invFun y := a⁻¹ • (y - b)
  left_inv x := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv y := by simp [smul_smul, mul_inv_cancel₀ ha]
  contMDiff_toFun := ((contDiff_const_smul a).add contDiff_const).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).const_smul a⁻¹).contMDiff

/-- `Diffeomorph.smulAdd n a b ha` sends `x` to `a • x + b`. -/
@[simp]
theorem smulAdd_apply (a : 𝕜) (b : E) (ha : a ≠ 0) (x : E) : smulAdd n a b ha x = a • x + b :=
  (rfl)

/-- The inverse of `Diffeomorph.smulAdd n a b ha` sends `y` to `a⁻¹ • (y - b)`. -/
@[simp]
theorem smulAdd_symm_apply (a : 𝕜) (b : E) (ha : a ≠ 0) (y : E) :
    (smulAdd n a b ha).symm y = a⁻¹ • (y - b) :=
  (rfl)

end Diffeomorph
