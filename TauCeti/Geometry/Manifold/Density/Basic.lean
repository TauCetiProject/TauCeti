/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# Rough densities on manifolds and the density of an oriented top form

A rough density of degree `m` on a manifold assigns to each point a density of degree `m` on
its tangent space, with no regularity in the base point; in top degree these are sections of
the density line bundle `TauCeti.DensityBundle`. On an oriented manifold, a top form `φ`
determines the rough density `φ.toDensity o`. At each point it agrees with `φ` on positively
oriented bases of the tangent space and with `-φ` on negatively oriented ones. It is additive
and homogeneous in `φ`, negated by reversing the orientation, and determines `φ` once the
orientation is fixed. This is the comparison through which oriented integration of top forms
becomes a special case of the orientation-free integration of densities.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

noncomputable section

open Module

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- A rough density of degree `m`: a density of degree `m` on each tangent space, with no
regularity in the base point. -/
abbrev RoughDensity (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (m : ℕ) : Type _ :=
  (x : M) → Density (TangentSpace I x) m

variable [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] {m : ℕ}

namespace RoughForm

/-- The density of a top form on an oriented manifold: at each point, the density of the
form with respect to the tangent orientation. -/
def toDensity (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    RoughDensity I M m := fun x ↦
  haveI := o.fact_finrank_tangentSpace x
  (φ x).toAlternatingMap.toDensity (o.orientationAt x)

/-- The density of a top form on a basis of a tangent space: the value of the form, negated
when the basis is negatively oriented. -/
theorem toDensity_apply (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Basis (Fin m) ℝ (TangentSpace I x)) [Decidable (b.orientation = o.orientationAt x)] :
    φ.toDensity o x b = if b.orientation = o.orientationAt x then φ x b else -φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply (φ x).toAlternatingMap (o.orientationAt x) b

/-- On a positively oriented basis of a tangent space, the density of a top form is the form
itself. -/
@[simp]
theorem toDensity_apply_of_orientation_eq (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = o.orientationAt x) : φ.toDensity o x b = φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_of_orientation_eq _ hb

/-- On a negatively oriented basis of a tangent space, the density of a top form is the
negated form. -/
@[simp]
theorem toDensity_apply_of_orientation_eq_neg (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = -o.orientationAt x) : φ.toDensity o x b = -φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_of_orientation_eq_neg _ hb

/-- The density of a top form on an arbitrary tuple of tangent vectors is the absolute
determinant of the tuple in any positively oriented basis, times the value of the form on that
basis. -/
theorem toDensity_apply_eq_abs_det_mul (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = o.orientationAt x) (v : Fin m → TangentSpace I x) :
    φ.toDensity o x v = |b.det v| * φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_eq_abs_det_mul _ hb v

/-- Reversing the orientation negates the density of a top form. -/
@[simp]
theorem toDensity_neg_orientation (φ : RoughForm I M ℝ m)
    (o : Manifold.Orientation I M (Fin m)) : φ.toDensity (-o) = -φ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Manifold.Orientation.orientationAt_neg,
    AlternatingMap.toDensity_neg_orientation, Pi.neg_apply]

/-- The density of a sum of top forms is the sum of their densities. -/
@[simp]
theorem toDensity_add (φ ψ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (φ + ψ).toDensity o = φ.toDensity o + ψ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Pi.add_apply, ContinuousAlternatingMap.toAlternatingMap_add,
    AlternatingMap.toDensity_add]

/-- The density of a scalar multiple of a top form is the scalar multiple of its density. -/
@[simp]
theorem toDensity_smul (c : ℝ) (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (c • φ).toDensity o = c • φ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Pi.smul_apply, ContinuousAlternatingMap.toAlternatingMap_smul,
    AlternatingMap.toDensity_smul]

/-- The density of the zero top form is zero. -/
@[simp]
theorem toDensity_zero (o : Manifold.Orientation I M (Fin m)) :
    (0 : RoughForm I M ℝ m).toDensity o = 0 := by
  rw [← zero_smul ℝ (0 : RoughForm I M ℝ m), toDensity_smul, zero_smul]

/-- The density of a negated top form is the negated density. -/
@[simp]
theorem toDensity_neg (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (-φ).toDensity o = -φ.toDensity o := by
  rw [← neg_one_smul ℝ φ, toDensity_smul, neg_one_smul]

/-- On an oriented manifold, a top form is determined by its density. -/
theorem toDensity_injective (o : Manifold.Orientation I M (Fin m)) :
    Function.Injective fun φ : RoughForm I M ℝ m ↦ φ.toDensity o := by
  intro φ ψ h
  funext x
  have := o.fact_finrank_tangentSpace x
  have hx : (φ x).toAlternatingMap.toDensity (o.orientationAt x) =
      (ψ x).toAlternatingMap.toDensity (o.orientationAt x) := congrFun h x
  rw [← Orientation.densityEquiv_apply, ← Orientation.densityEquiv_apply] at hx
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    ((Orientation.densityEquiv (o.orientationAt x)).injective hx)

end RoughForm

end TauCeti
