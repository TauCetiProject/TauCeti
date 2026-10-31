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

end Diffeomorph
