/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The angle between two vectors of an `RCLike` inner product space

`TauCeti.vectorAngle 𝕜 x y = arccos (re ⟪y, x⟫ / (‖x‖ ‖y‖))`, the angle between
two vectors of a real *or complex* inner product space.

## Real part, not modulus

Over `ℂ` there are two competing normalizations, and they are different numbers:

* the **vector** angle divides by the *real part* of the inner product;
* the **line** angle — the angle between the one-dimensional subspaces `[x]` and
  `[y]`, equivalently `inf {angle u v : u ∈ [x], v ∈ [y]}` — divides by the
  *modulus*.

They disagree already for `y = -x`, where the first is `π` and the second `0`.
Davis and Kahan print both, as equations (1.14) and (1.15) of *The rotation of
eigenvectors by a perturbation. III*; this file is (1.14).  Anything phrased for
individual vectors — the direct rotation moving an angle eigenvector through its
own principal angle, say — is the vector angle.

## Relation to `InnerProductGeometry.angle`

Mathlib's `InnerProductGeometry.angle` is the same normalization, but it is
stated only for a *real* inner product space.  `vectorAngle_real_eq_angle` is
that agreement, and `vectorAngle_eq_angle_rclikeToReal` says that over a general
`RCLike` field this definition is exactly Mathlib's angle read through
`InnerProductSpace.rclikeToReal`, whose real inner product is `re ⟪·,·⟫` by
definition.  So this is not a competing notion of angle: it is the one Mathlib
already has, spelled so that it applies to a complex space without an explicit
scalar-restriction instance at every use site.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written for Davis--Kahan 1970 Proposition 3.5,
  whose eigenvector clause is an assertion about `angle (x, U x)`.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The angle between two vectors**, Davis--Kahan (1.14):
`∠(x, y) = arccos (Re ⟪y, x⟫ / (‖x‖ ‖y‖))`.

The scalar field is explicit because it does not appear in the result type.  If
either vector is zero the quotient is `0` and the angle is `π / 2`, matching
`InnerProductGeometry.angle`. -/
noncomputable def vectorAngle (x y : E) : ℝ :=
  Real.arccos (RCLike.re (inner 𝕜 y x) / (‖x‖ * ‖y‖))

/-- Defining formula for `vectorAngle`.  Private: the body stays unexposed, and
the public characterizations below — agreement with `InnerProductGeometry.angle`
and `vectorAngle_eq_of_re_inner_eq` — are what consumers use. -/
private theorem vectorAngle_def (x y : E) :
    vectorAngle 𝕜 x y = Real.arccos (RCLike.re (inner 𝕜 y x) / (‖x‖ * ‖y‖)) :=
  rfl

variable {𝕜}

/-- The vector angle is symmetric: the real part of the inner product is. -/
theorem vectorAngle_comm (x y : E) : vectorAngle 𝕜 x y = vectorAngle 𝕜 y x := by
  rw [vectorAngle_def, vectorAngle_def, inner_re_symm (𝕜 := 𝕜) y x, mul_comm ‖x‖ ‖y‖]

/-- **The vector angle is Mathlib's `InnerProductGeometry.angle` on a real inner
product space.**  Both are `arccos` of the inner product over the product of the
norms, and the real inner product is symmetric. -/
theorem vectorAngle_real_eq_angle {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x y : F) :
    vectorAngle ℝ x y = InnerProductGeometry.angle x y := by
  rw [vectorAngle_def,
    show InnerProductGeometry.angle x y
        = Real.arccos (inner ℝ x y / (‖x‖ * ‖y‖)) from rfl,
    RCLike.re_to_real, real_inner_comm]

/-- **Over any `RCLike` field the vector angle is Mathlib's angle for the
underlying real inner product space.**

`InnerProductSpace.rclikeToReal` equips `E` with the real inner product
`re ⟪·,·⟫`, which is the numerator of (1.14) up to the symmetry
`re ⟪x, y⟫ = re ⟪y, x⟫`; the norm is untouched by the scalar restriction.  This
is the statement that checks the normalization: Mathlib's angle takes the *real
part*, not the modulus. -/
theorem vectorAngle_eq_angle_rclikeToReal (x y : E) :
    vectorAngle 𝕜 x y =
      @InnerProductGeometry.angle E _ (InnerProductSpace.rclikeToReal 𝕜 E) x y := by
  rw [vectorAngle_def, inner_re_symm (𝕜 := 𝕜) y x]
  rfl

/-- **A real-inner-product upper bound gives a lower bound on vector angle.**

For unit vectors, `Re ⟪y, x⟫ ≤ cos θ` with `θ ∈ [0, π]` implies
`θ ≤ angle(x, y)`.  This is the comparison form used by the compact
principal-vector proof of Davis--Kahan Proposition 4.1. -/
theorem le_vectorAngle_of_unit_norm_of_re_inner_le_cos {x y : E} {θ : ℝ}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hinner : RCLike.re (inner 𝕜 y x) ≤ Real.cos θ) :
    θ ≤ vectorAngle 𝕜 x y := by
  calc
    θ = Real.arccos (Real.cos θ) := (Real.arccos_cos hθ0 hθπ).symm
    _ ≤ Real.arccos (RCLike.re (inner 𝕜 y x)) := Real.arccos_le_arccos hinner
    _ = vectorAngle 𝕜 x y := by
      rw [vectorAngle_def, hxnorm, hynorm]
      norm_num

/-- **The angle is determined by the real part of the inner product.**

The computational form used at call sites: given the two norms and the real part,
the angle is an `arccos`.  Stated with `‖y‖ = ‖x‖` because the direct rotation is
unitary, which is the only case Proposition 3.5 needs. -/
theorem vectorAngle_eq_of_re_inner_eq {x y : E} {θ : ℝ} (hx : x ≠ 0)
    (hnorm : ‖y‖ = ‖x‖) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hinner : RCLike.re (inner 𝕜 y x) = Real.cos θ * ‖x‖ ^ 2) :
    vectorAngle 𝕜 x y = θ := by
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  rw [vectorAngle_def, hinner, hnorm]
  rw [show ‖x‖ * ‖x‖ = ‖x‖ ^ 2 from (sq ‖x‖).symm,
    mul_div_assoc, div_self (by positivity), mul_one, Real.arccos_cos hθ0 hθπ]

end TauCeti
