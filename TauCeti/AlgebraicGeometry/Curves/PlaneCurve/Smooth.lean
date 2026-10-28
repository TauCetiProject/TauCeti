/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PlaneCurve.Basic
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
public import TauCeti.RingTheory.Smooth.Hypersurface

/-!
# Smooth projective plane curves

Let `G` be a homogeneous polynomial over a field `k`. If every projective zero of `G` over
an algebraically closed extension has a nonzero partial derivative, then the scheme
`projectivePlaneCurve hG` is smooth of relative dimension one over `k`.

For an irreducible equation this gives a regular proper integral curve, whose function field
is an algebraic function field of one variable. Its codimension-one local rings are DVRs, so
its closed points can be used in the point–place dictionary. No perfectness assumption on `k`
or restriction on the degree or characteristic is needed.

## Main results

* `projectivePlaneCurve.smoothOfRelativeDimension`: nonsingularity of the homogeneous equation
  gives scheme-theoretic smoothness of relative dimension one.
* `projectivePlaneCurve.isCurveOver`: an irreducible nonsingular equation defines a curve.
* `projectivePlaneCurve.isDiscreteValuationRing_stalk`: the codimension-one local rings are DVRs.
* `projectivePlaneCurve.isFunctionField`: the scheme's function field is a function field.

## References

* W. Fulton, *Algebraic Curves*, Chapter 5, Section 1.
* Stacks Project, Tag 00T7.

The chart argument uses `HomogeneousIdeal.awayEquivDehomogenize` and the affine gradient
criterion `TauCeti.span_insert_range_pderiv_dehomogenize_eq_top`.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace TauCeti.AlgebraicGeometry.projectivePlaneCurve

variable {k : Type u} [Field k] {K : Type*} [Field K] [Algebra k K] [IsAlgClosed K]
  {G : MvPolynomial (Fin 3) k} {d : ℕ} (hG : G.IsHomogeneous d)
  (hsm : ∀ b : Fin 3 → K, b ≠ 0 → aeval b G = 0 → ∃ j, aeval b (pderiv j G) ≠ 0)

include hsm

/-- Each standard affine chart of a nonsingular homogeneous plane equation is locally
standard smooth of relative dimension one. -/
theorem locally_isStandardSmoothOfRelativeDimension_away (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (HomogeneousLocalization.Away (ideal hG).quotientGrading
        (Ideal.Quotient.mk (ideal hG).toIdeal (X i)))) := by
  let e := ((ideal hG).awayEquivDehomogenize i).trans
    (Ideal.quotientEquivAlgOfEq k (map_dehomogenize_ideal hG i))
  have hspan := span_insert_range_pderiv_dehomogenize_eq_top (K := K) hG i fun a ha ↦
    hsm (i.insertNth 1 a) (fun h ↦ (one_ne_zero : (1 : K) ≠ 0)
      (by simpa using congrFun h i)) ha
  have h := MvPolynomial.locally_isStandardSmoothOfRelativeDimension_quotient
    (dehomogenize i G) hspan
  have he : e.symm.toRingEquiv.toRingHom.comp (algebraMap k _) = algebraMap k _ :=
    e.symm.toAlgHom.comp_algebraMap
  rw [← he]
  exact (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ e.symm.toRingEquiv
      (by simpa using h)

/-- The chart inclusion followed by the structure morphism of a nonsingular plane curve
is smooth of relative dimension one. -/
private theorem smoothOfRelativeDimension_awayι (i : Fin 3) :
    SmoothOfRelativeDimension 1
      (Proj.awayι _ _ ((ideal hG).mk_X_mem_quotientGrading i) one_pos ≫
        (projectivePlaneCurve hG ↘ Spec (.of k))) := by
  rw [HomogeneousIdeal.over_proj_quotientGrading, Proj.awayι_toSpecCoeff,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmoothOfRelativeDimension_away hG hsm i

/-- **A nonsingular projective plane equation defines a smooth scheme of relative dimension
one.** Nonsingularity is tested over any algebraically closed extension of the base field.
The characteristic may divide the degree. -/
theorem smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (projectivePlaneCurve hG ↘ Spec (.of k)) := by
  let I := ideal hG
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan I.quotientGrading
    (fun i ↦ Ideal.Quotient.mk I.toIdeal (X i)) I.mk_X_mem_quotientGrading
    (fun _ ↦ one_pos) I.irrelevant_le_span_range_mk_X).openCover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  exact HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 1) 𝒰
    fun i ↦ (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension 1)).mp
      (smoothOfRelativeDimension_awayι hG hsm i)

/-- All local rings of a nonsingular projective plane curve over a field are regular. -/
theorem isRegularLocalRing_stalk (x : projectivePlaneCurve hG) :
    IsRegularLocalRing ((projectivePlaneCurve hG).presheaf.stalk x) := by
  have := smoothOfRelativeDimension hG hsm
  have := SmoothOfRelativeDimension.smooth 1 (projectivePlaneCurve hG ↘ Spec (.of k))
  exact isRegularLocalRing_stalk_of_smooth (projectivePlaneCurve hG ↘ Spec (.of k)) x

/-- A nonempty nonsingular projective plane curve has dimension one. -/
theorem topologicalKrullDim_eq_one [Nonempty (projectivePlaneCurve hG)] :
    topologicalKrullDim (projectivePlaneCurve hG) = 1 := by
  have := smoothOfRelativeDimension hG hsm
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (projectivePlaneCurve hG ↘ Spec (.of k))

variable [Fact (Irreducible G)]

/-- An irreducible nonsingular homogeneous plane equation defines an integral proper curve. -/
theorem isCurveOver : (projectivePlaneCurve hG).IsCurveOver k where
  topologicalKrullDim_eq_one := topologicalKrullDim_eq_one hG hsm

/-- At every codimension-one point of a nonsingular integral projective plane curve, the local
ring is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk (x : CodimensionOnePoint (projectivePlaneCurve hG)) :
    IsDiscreteValuationRing ((projectivePlaneCurve hG).presheaf.stalk
      (x : projectivePlaneCurve hG)) := by
  have : ∀ y : projectivePlaneCurve hG,
      IsRegularLocalRing ((projectivePlaneCurve hG).presheaf.stalk y) :=
    isRegularLocalRing_stalk hG hsm
  infer_instance

/-- The function field of the scheme of an irreducible nonsingular plane equation is an
algebraic function field of one variable over the base field. -/
theorem isFunctionField : IsFunctionField k (projectivePlaneCurve hG).functionField := by
  have := isCurveOver hG hsm
  exact Scheme.IsCurveOver.isFunctionField

end TauCeti.AlgebraicGeometry.projectivePlaneCurve
