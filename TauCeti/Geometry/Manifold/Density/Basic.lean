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

/-- The density of a top form on any basis of a tangent space is the relative orientation sign
times the value of the form on that basis. -/
theorem toDensity_apply_basis (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m))
    (x : M) (b : Basis (Fin m) ℝ (TangentSpace I x)) :
    φ.toDensity o x b = ((o.orientationAt x).signBasis b : ℝ) * φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_basis (φ x).toAlternatingMap (o.orientationAt x) b

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

/-- The density of a difference of top forms is the difference of their densities. -/
@[simp]
theorem toDensity_sub (φ ψ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (φ - ψ).toDensity o = φ.toDensity o - ψ.toDensity o := by
  rw [sub_eq_add_neg, toDensity_add, toDensity_neg, sub_eq_add_neg]

/-- Pointwise scalar multiplication of a top form commutes with `toDensity`. -/
theorem toDensity_fun_smul (f : M → ℝ) (φ : RoughForm I M ℝ m)
    (o : Manifold.Orientation I M (Fin m)) :
    toDensity (fun x ↦ f x • φ x) o = fun x ↦ f x • φ.toDensity o x := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, ContinuousAlternatingMap.toAlternatingMap_smul,
    AlternatingMap.toDensity_smul]

/-- At each point, the density of a top form vanishes exactly when the form vanishes there. -/
@[simp]
theorem toDensity_apply_eq_zero_iff (φ : RoughForm I M ℝ m)
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    φ.toDensity o x = 0 ↔ φ x = 0 := by
  have := o.fact_finrank_tangentSpace x
  rw [toDensity, AlternatingMap.toDensity_eq_zero_iff,
    ← ContinuousAlternatingMap.toAlternatingMap_zero,
    ContinuousAlternatingMap.toAlternatingMap_injective.eq_iff]

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

/-- Taking the absolute value of `φ.toDensity o` at any point and tuple gives `|φ x v|`. -/
@[simp]
theorem abs_toDensity_apply (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m))
    (x : M) (v : Fin m → TangentSpace I x) : |φ.toDensity o x v| = |φ x v| := by
  have := o.fact_finrank_tangentSpace x
  exact (AlternatingMap.abs_toDensity_apply (φ x).toAlternatingMap (o.orientationAt x) v).trans
    (AlternatingMap.absDensity_apply _ _)

section AbsDensity

omit [FiniteDimensional ℝ E] [IsManifold I 1 M]
variable [Fact (Module.finrank ℝ E = m)]

/-- The orientation-free nonnegative rough density `|φ|` of a top-degree rough form `φ`: at each
point `x` and tuple `v`, `(φ.absDensity x) v = |φ x v|`. Neither an orientation nor a smooth
manifold structure is needed. -/
def absDensity (φ : RoughForm I M ℝ m) : RoughDensity I M m := fun x ↦
  haveI : Fact (Module.finrank ℝ (TangentSpace I x) = m) :=
    ⟨(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq.trans Fact.out⟩
  (φ x).toAlternatingMap.absDensity

@[simp]
theorem absDensity_apply (φ : RoughForm I M ℝ m) (x : M) (v : Fin m → TangentSpace I x) :
    φ.absDensity x v = |φ x v| := by
  have : Fact (Module.finrank ℝ (TangentSpace I x) = m) :=
    ⟨(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq.trans Fact.out⟩
  exact AlternatingMap.absDensity_apply (φ x).toAlternatingMap v

/-- The absolute density of a rough top form is everywhere nonnegative. -/
theorem absDensity_nonneg (φ : RoughForm I M ℝ m) (x : M) (v : Fin m → TangentSpace I x) :
    0 ≤ φ.absDensity x v := by
  rw [absDensity_apply]
  exact abs_nonneg (φ x v)

@[simp]
theorem absDensity_zero : (0 : RoughForm I M ℝ m).absDensity = 0 := by
  funext x
  ext v
  simp

@[simp]
theorem absDensity_neg (φ : RoughForm I M ℝ m) : (-φ).absDensity = φ.absDensity := by
  funext x
  ext v
  simp

/-- Pointwise scalar multiplication of a rough top form multiplies `absDensity` by `|f x|`. -/
theorem absDensity_fun_smul (f : M → ℝ) (φ : RoughForm I M ℝ m) :
    absDensity (fun x ↦ f x • φ x) = fun x ↦ |f x| • φ.absDensity x := by
  funext x
  ext v
  simp [abs_mul]

/-- Constant scalar multiplication of a rough top form scales `absDensity` by `|c|`. -/
theorem absDensity_smul (c : ℝ) (φ : RoughForm I M ℝ m) :
    (c • φ).absDensity = |c| • φ.absDensity :=
  absDensity_fun_smul (fun _ ↦ c) φ

/-- At each point, `φ.absDensity` vanishes precisely when `φ` vanishes there. -/
@[simp]
theorem absDensity_apply_eq_zero_iff (φ : RoughForm I M ℝ m) (x : M) :
    φ.absDensity x = 0 ↔ φ x = 0 := by
  have : Fact (Module.finrank ℝ (TangentSpace I x) = m) :=
    ⟨(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq.trans Fact.out⟩
  rw [absDensity, AlternatingMap.absDensity_eq_zero_iff,
    ← ContinuousAlternatingMap.toAlternatingMap_zero,
    ContinuousAlternatingMap.toAlternatingMap_injective.eq_iff]

end AbsDensity

end RoughForm

end TauCeti
