/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Base change of affine elliptic curves

Mathlib carries ellipticity through `WeierstrassCurve.map`. This module exposes the same instance
for the canonical affine base-change spelling `W⁄A`, so consumers of the point and function-field
base-change APIs do not have to unfold that abbreviation. It also records that base change along
the identity algebra map returns the original curve, together with the resulting identification
`WeierstrassCurve.Affine.Point.equivBaseChangeSelf` of the point groups of `W` and `W⁄F`, the
Weierstrass equation of `W⁄A` written with the coefficients of `W` mapped along `algebraMap`, the
base-change homomorphism `WeierstrassCurve.Affine.pointMap : W(K) →+ W(L)` on points along a
field extension `L/K`, and a coordinate descent lemma for points whose abscissa is already
rational.

`pointMap` is Mathlib's `WeierstrassCurve.Affine.Point.map` and is not a new construction: the
only content is the alignment of `W` with `W⁄K`, which `baseChange_self` supplies and Mathlib's
`AddEquiv.cast` transports along. It and `pointMap_some` were adapted, with the author's proofs,
from the `BaseChange` section of `EllipticCurves/SelmerGroup.lean` in Michael Stoll's
`EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0), together
with the local `2`-descent condition of
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/LocalCondition.lean`.

This is infrastructure for the base-change lane of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0.5.
-/

public section

open Polynomial

open _root_.WeierstrassCurve

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- Base changing along the identity algebra map returns the curve itself. Stated over a
commutative ring: it is a formal `map` identity and uses nothing about `R` beyond its ring
structure. -/
@[simp]
lemma baseChange_self : (W⁄R).toAffine = W := by
  -- `WeierstrassCurve.baseChange` (Weierstrass.lean:236) is a plain `def` and Mathlib exposes no
  -- unfolding lemma for it, so this one definitional step cannot be replaced by an API rewrite.
  -- It must be `change` rather than `show`: the step rewrites the goal rather than restating it,
  -- which is exactly what `linter.style.show` requires. Everything after it is a named rewrite.
  change W.map (algebraMap R R) = W
  rw [show algebraMap R R = RingHom.id R from Algebra.algebraMap_self]
  exact W.map_id

variable {A : Type*} [CommRing A] [Algebra R A]

/-- **The Weierstrass equation of a base change**, with the coefficients of `W` mapped into `A`
along `algebraMap`. -/
lemma equation_baseChange_iff (x y : A) :
    (W⁄A).Equation x y ↔
      y ^ 2 + algebraMap R A W.a₁ * x * y + algebraMap R A W.a₃ * y =
        x ^ 3 + algebraMap R A W.a₂ * x ^ 2 + algebraMap R A W.a₄ * x + algebraMap R A W.a₆ := by
  rw [equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F)

/-- **The points of `W` are the points of its base change along the identity**: the transport of
the point group along `baseChange_self`. Point-group facts stated for `W⁄F`, the form base-change
statements produce, are read on `W` itself through it. -/
noncomputable def equivBaseChangeSelf : W.Point ≃+ (W⁄F).toAffine.Point :=
  AddEquiv.cast (M := fun W' : Affine F ↦ W'.Point) W.baseChange_self.symm

/-- **`equivBaseChangeSelf` keeps the coordinates of an affine point.** -/
@[simp]
theorem equivBaseChangeSelf_some {x y : F} (h : W.Nonsingular x y) :
    equivBaseChangeSelf W (.some x y h) = .some x y (W.baseChange_self.symm ▸ h) := by
  rw [equivBaseChangeSelf, AddEquiv.cast_apply]
  exact Point.cast_some W.baseChange_self.symm h

/-- **`equivBaseChangeSelf` keeps the `x`-coordinate of a point.** -/
@[simp]
theorem xCoord_equivBaseChangeSelf (P : W.Point) :
    xCoord (equivBaseChangeSelf W P) = xCoord P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← zero_def]
  · rw [equivBaseChangeSelf_some, xCoord_some, xCoord_some]

/-- **`equivBaseChangeSelf` keeps the `y`-coordinate of a point.** -/
@[simp]
theorem yCoord_equivBaseChangeSelf (P : W.Point) :
    yCoord (equivBaseChangeSelf W P) = yCoord P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← zero_def]
  · rw [equivBaseChangeSelf_some, yCoord_some, yCoord_some]

/-- **`equivBaseChangeSelf.symm` keeps the `x`-coordinate of a point.** -/
@[simp]
theorem xCoord_equivBaseChangeSelf_symm (P : (W⁄F).toAffine.Point) :
    xCoord ((equivBaseChangeSelf W).symm P) = xCoord P := by
  rw [← xCoord_equivBaseChangeSelf, AddEquiv.apply_symm_apply]

/-- **`equivBaseChangeSelf.symm` keeps the `y`-coordinate of a point.** -/
@[simp]
theorem yCoord_equivBaseChangeSelf_symm (P : (W⁄F).toAffine.Point) :
    yCoord ((equivBaseChangeSelf W).symm P) = yCoord P := by
  rw [← yCoord_equivBaseChangeSelf, AddEquiv.apply_symm_apply]

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K) (L : Type*) [Field L] [Algebra K L]

open scoped Classical in
/-- The base-change homomorphism on points, `W(K) →+ W(L)`: Mathlib's
`WeierstrassCurve.Affine.Point.map`, aligned with the plain base change `W⁄L` via
`baseChange_self`. -/
noncomputable def pointMap : W.Point →+ (W⁄L).toAffine.Point :=
  (Point.map (W' := W) (Algebra.ofId K L)).comp
    (AddEquiv.cast (M := fun W' : Affine K => W'.Point) W.baseChange_self.symm).toAddMonoidHom

open scoped Classical in
/-- The base-change map on an affine point carries its coordinates along `algebraMap K L`. -/
@[simp]
lemma pointMap_some {x y : K} (h : W.Nonsingular x y) : W.pointMap L (Point.some x y h) =
      Point.some (W' := (W⁄L).toAffine) (algebraMap K L x) (algebraMap K L y)
        (show (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) from
          (W.map_nonsingular (algebraMap K L).injective x y).mpr h) := by
  -- The type ascription above is load-bearing: `map_nonsingular` produces the nonsingularity
  -- proof at `W.map (algebraMap K L)`, and although `W⁄L` is a reducible abbreviation for
  -- exactly that, the elaborator does not unfold it at `instances` transparency, so the two
  -- identically-printing types do not unify without being told the target.
  rw [pointMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.cast_apply,
    Point.cast_some W.baseChange_self.symm, Point.map_some]
  rfl

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {R A : Type*} [CommRing R] [CommRing A] [NoZeroDivisors A] [Algebra R A]
  (W : WeierstrassCurve R) {x y : A}

/-- **The `y`-coordinate of a point with rational `x` is rational** whenever the Weierstrass
equation at that `x` has one rational solution: the two roots of the resulting monic quadratic
sum to minus its linear coefficient, so the other one is rational as well. -/
theorem mem_range_y_of_equation_of_mem_range_x_of_exists_point
    (heq : (W.baseChange A).toAffine.Equation x y) {x₀ : R} (hx : algebraMap R A x₀ = x)
    (hex : ∃ y₀ : R, W.toAffine.Equation x₀ y₀) :
    y ∈ Set.range (algebraMap R A) := by
  subst hx
  obtain ⟨y₀, hy₀⟩ := hex
  rw [Affine.equation_iff] at heq hy₀
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  have hy₀' := congrArg (algebraMap R A) hy₀
  simp only [map_add, map_mul, map_pow] at hy₀'
  -- The two roots of the quadratic in `y`, one of which is the image of `y₀`.
  have hroots : (y - algebraMap R A y₀) *
      (y + algebraMap R A y₀ + (algebraMap R A W.a₁ * algebraMap R A x₀ + algebraMap R A W.a₃))
        = 0 := by linear_combination heq - hy₀'
  rcases mul_eq_zero.mp hroots with hk | hk
  · exact ⟨y₀, by linear_combination -hk⟩
  · refine ⟨-y₀ - W.a₁ * x₀ - W.a₃, ?_⟩
    simp only [map_sub, map_neg, map_mul]
    linear_combination -hk

end WeierstrassCurve

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {W : _root_.WeierstrassCurve.Affine R} [W.IsElliptic]

/-- **Base change preserves ellipticity**, in the `(W⁄A).toAffine` spelling used by the affine
point API. -/
instance _root_.WeierstrassCurve.Affine.instIsEllipticBaseChange : (W⁄A).toAffine.IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

end


end
