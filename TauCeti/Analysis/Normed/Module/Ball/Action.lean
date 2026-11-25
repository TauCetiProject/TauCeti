/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Unit scalars acting on spheres

Mathlib's `Analysis.Normed.Module.Ball.Action`, due to Yury Kudryashov and Heather Macbeth, lets
the unit sphere of a normed field `𝕜` act on every sphere centred at zero in a normed `𝕜`-space.
This file records that the underlying vector of this action is scalar multiplication, and that
the action of the unit sphere on a sphere of nonzero radius is free.

Mathlib's `Circle` is a type synonym for the unit sphere of `ℂ`, carrying the Lie group structure.
Through it, the circle acts on every sphere centred at zero in a normed `ℂ`-space, continuously,
and freely and properly on spheres of nonzero radius. On the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` this is
the action whose orbit space is complex projective space.

Over a noncommutative normed ring, such as the quaternions, the natural scalar action on a
coordinate space is often on the right. A right action of `𝕜` on `F` is an action of `𝕜ᵐᵒᵖ`,
and when it multiplies norms, right multiplication by unit scalars preserves every sphere centred
at zero. This file packages it as an action of the opposite monoid `(sphere (0 : 𝕜) 1)ᵐᵒᵖ` on
the sphere, the right-handed counterpart of Mathlib's action. The action on the sphere is
continuous whenever the ambient action is, for example when `F` is a `𝕜ᵐᵒᵖ`-module.

## Main declarations

* `TauCeti.Sphere.coe_sphere_smul`: Mathlib's action of unit scalars on a sphere is scalar
  multiplication.
* `TauCeti.Sphere.instIsCancelSMul`: unit scalars act freely on a sphere of nonzero radius.
* `TauCeti.Sphere.instMulActionMulOpposite`: unit scalars act on the right on a sphere centred at
  zero, with `TauCeti.Sphere.coe_op_sphere_smul` computing the action.
* `Circle.instMulActionSphere`, `Circle.instContinuousSMulSphere`, `Circle.instIsCancelSMulSphere`,
  `Circle.instProperSMulSphere`: the circle acts continuously on every sphere centred at zero in a
  normed `ℂ`-space, freely and properly when the radius is nonzero, with
  `Circle.coe_smul_sphere` computing the action.
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

/-- Unit scalars act freely on a sphere of nonzero radius centred at zero: `c • x = d • x` forces
`c = d`, because `x ≠ 0`. -/
instance instIsCancelSMul {𝕜 F : Type*} [NormedField 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {r : ℝ} [NeZero r] :
    IsCancelSMul (sphere (0 : 𝕜) 1) (sphere (0 : F) r) where
  right_cancel' _ _ x h := Subtype.ext <|
    smul_left_injective 𝕜 (ne_zero_of_mem_sphere (NeZero.ne r) x) (congrArg Subtype.val h)

section RightAction

variable {𝕜 F : Type*} [SeminormedRing 𝕜] {r : ℝ}

section SMul

variable [SeminormedAddGroup F] [SMul 𝕜ᵐᵒᵖ F] [NormSMulClass 𝕜ᵐᵒᵖ F]

/-- Right multiplication by a unit scalar preserves every sphere centred at zero. -/
instance instSMulMulOpposite : SMul (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) where
  smul c x := ⟨(x : F) <• ((unop c : sphere (0 : 𝕜) 1) : 𝕜), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_op, mem_sphere_zero_iff_norm.1 (unop c).property,
      mem_sphere_zero_iff_norm.1 x.property, one_mul]⟩

/-- The right action of a unit scalar on a sphere is right scalar multiplication in the ambient
space. -/
@[simp]
theorem coe_op_sphere_smul (c : (sphere (0 : 𝕜) 1)ᵐᵒᵖ) (x : sphere (0 : F) r) :
    ((c • x : sphere (0 : F) r) : F) = (x : F) <• ((unop c : sphere (0 : 𝕜) 1) : 𝕜) :=
  (rfl)

/-- The right action of unit scalars on a sphere centred at zero is continuous whenever the
ambient action is. -/
instance instContinuousSMulMulOpposite [ContinuousSMul 𝕜ᵐᵒᵖ F] :
    ContinuousSMul (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end SMul

/-- Unit scalars act on the right on every sphere centred at zero. -/
instance instMulActionMulOpposite [NormMulClass 𝕜] [NormOneClass 𝕜] [SeminormedAddGroup F]
    [MulAction 𝕜ᵐᵒᵖ F] [NormSMulClass 𝕜ᵐᵒᵖ F] :
    MulAction (sphere (0 : 𝕜) 1)ᵐᵒᵖ (sphere (0 : F) r) where
  one_smul x := Subtype.ext <| by simp
  mul_smul c d x := Subtype.ext <| by simp [mul_smul]

end RightAction

end Sphere

end TauCeti

namespace Circle

open Metric

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F] {r : ℝ}

/-- The circle acts on every sphere centred at zero in a normed `ℂ`-space by scalar
multiplication, through its identification with the unit sphere of `ℂ`. -/
noncomputable instance instMulActionSphere : MulAction Circle (sphere (0 : F) r) :=
  inferInstanceAs (MulAction (sphere (0 : ℂ) 1) (sphere (0 : F) r))

/-- The action of the circle on a sphere is scalar multiplication in the ambient space. -/
@[simp]
theorem coe_smul_sphere (c : Circle) (x : sphere (0 : F) r) :
    ((c • x : sphere (0 : F) r) : F) = (c : ℂ) • (x : F) :=
  (rfl)

/-- The circle acts continuously on every sphere centred at zero. -/
instance instContinuousSMulSphere : ContinuousSMul Circle (sphere (0 : F) r) :=
  inferInstanceAs (ContinuousSMul (sphere (0 : ℂ) 1) (sphere (0 : F) r))

/-- The circle acts freely on every sphere of nonzero radius centred at zero. -/
instance instIsCancelSMulSphere [NeZero r] : IsCancelSMul Circle (sphere (0 : F) r) :=
  inferInstanceAs (IsCancelSMul (sphere (0 : ℂ) 1) (sphere (0 : F) r))

/-- The compact circle acts properly on every sphere centred at zero in a normed `ℂ`-space. -/
instance instProperSMulSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ProperSMul Circle (sphere (0 : E) r) :=
  TauCeti.properSMul_of_compactSpace _ _

end Circle
