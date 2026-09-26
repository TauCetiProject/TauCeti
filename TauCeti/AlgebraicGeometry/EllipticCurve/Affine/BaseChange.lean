/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Base change of affine elliptic curves

Mathlib carries ellipticity through `WeierstrassCurve.map`. This module exposes the same instance
for the canonical affine base-change spelling `W⁄A`, so consumers of the point and function-field
base-change APIs do not have to unfold that abbreviation. It also records that base change along
the identity algebra map returns the original curve, together with the resulting identification
`WeierstrassCurve.Affine.Point.equivBaseChangeSelf` of the point groups of `W` and `W⁄F`, and a
coordinate descent lemma for points whose abscissa is already rational.

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

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F)

/-- **The points of `W` are the points of its base change along the identity**: the transport of
the point group along `baseChange_self`. Point-group facts stated for `W⁄F`, the form base-change
statements produce, are read on `W` itself through it. -/
noncomputable def equivBaseChangeSelf : W.Point ≃+ (W⁄F).toAffine.Point :=
  AddEquiv.cast (M := fun W' : Affine F ↦ W'.Point) W.baseChange_self.symm

end WeierstrassCurve.Affine.Point

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
