/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Action

/-!
# Unit scalars acting on spheres

Mathlib's `Analysis.Normed.Module.Ball.Action`, due to Yury Kudryashov and Heather Macbeth, lets
the unit sphere of a normed field `𝕜` act on every sphere centred at zero in a normed `𝕜`-space.
This file records that the underlying vector of this action is scalar multiplication.

Over a noncommutative normed ring, such as the quaternions, the natural scalar action on a
coordinate space is often on the right. A right action of `𝕜` on `F` is a module structure over
`𝕜ᵐᵒᵖ`, and when it multiplies norms, right multiplication by unit scalars preserves every sphere
centred at zero. This file packages it as a continuous action of the opposite monoid
`(sphere (0 : 𝕜) 1)ᵐᵒᵖ` on the sphere, the right-handed counterpart of Mathlib's action.

## Main declarations

* `TauCeti.Sphere.coe_sphere_smul`: Mathlib's action of unit scalars on a sphere is scalar
  multiplication.
* `TauCeti.Sphere.instMulActionMulOpposite`: unit scalars act on the right on a sphere centred at
  zero, with `TauCeti.Sphere.coe_op_sphere_smul` computing the action.
-/

public section

namespace TauCeti

open Metric MulOpposite
open scoped RightActions

namespace Sphere

/-- The coercion of Mathlib's action of the unit sphere of a normed field `𝕜` on a sphere of a
normed `𝕜`-space is scalar multiplication in the ambient space. -/
@[simp]
theorem coe_sphere_smul {𝕜 F : Type*} [NormedField 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {r : ℝ} (c : sphere (0 : 𝕜) 1) (x : sphere (0 : F) r) :
    ((c • x : sphere (0 : F) r) : F) = (c : 𝕜) • (x : F) :=
  (rfl)

section RightAction

variable {𝕜 F : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup F] [Module 𝕜ᵐᵒᵖ F]
  [NormSMulClass 𝕜ᵐᵒᵖ F] {r : ℝ}

/-- Right multiplication by a unit scalar preserves every sphere centred at zero. -/
instance instSMulMulOpposite : SMul (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) where
  smul c x := ⟨(x : F) <• ((unop c : sphere (0 : 𝕜) 1) : 𝕜), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_op, mem_sphere_zero_iff_norm.1 (unop c).2,
      mem_sphere_zero_iff_norm.1 x.2, one_mul]⟩

/-- The right action of a unit scalar on a sphere is right scalar multiplication in the ambient
space. -/
@[simp]
theorem coe_op_sphere_smul (c : (sphere (0 : 𝕜) 1)ᵐᵒᵖ) (x : sphere (0 : F) r) :
    ((c • x : sphere (0 : F) r) : F) = (x : F) <• ((unop c : sphere (0 : 𝕜) 1) : 𝕜) :=
  (rfl)

/-- Unit scalars act on the right on every sphere centred at zero. -/
instance instMulActionMulOpposite [NormMulClass 𝕜] [NormOneClass 𝕜] :
    MulAction (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) where
  one_smul x := Subtype.ext <| by simp
  mul_smul c d x := Subtype.ext <| by simp [mul_smul]

/-- The right action of unit scalars on a sphere centred at zero is continuous. -/
instance instContinuousSMulMulOpposite :
    ContinuousSMul (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end RightAction

end Sphere

end TauCeti
