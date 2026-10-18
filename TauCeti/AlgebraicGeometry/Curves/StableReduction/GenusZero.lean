/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.GenusZero
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NodalReduction

/-!
# Nodal reduction of curves of genus zero with a divisor of degree one

Let `R` be a discrete valuation ring with fraction field `K`. The projective line `ℙ¹_R` is a
smooth proper model over `R` of the projective line `ℙ¹_K`: its generic fibre is `ℙ¹_K`, since the
formation of `ℙ¹` commutes with base change
(`TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`). Consequently `ℙ¹_K`
has nodal reduction, indeed good reduction, over `R`.

A regular proper curve of genus zero over `K` with a divisor of degree one, for instance with a
`K`-rational point, and with `K` integrally closed in its function field, is isomorphic to `ℙ¹_K`
(`AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_genus_eq_zero`). Since nodal reduction only
depends on the curve up to isomorphism over `K`, every such curve has nodal reduction over `R`,
without any extension of `R`. This is the case of a curve of genus zero whose generic fibre already
has a divisor of degree one; in general a curve of genus zero acquires a rational point only after
a finite separable extension of `K`.

## Main definitions

* `TauCeti.Model.projectiveLine R K`: the projective line `ℙ¹_R`, as a model of `ℙ¹_K` over `R`.

## Main results

* `TauCeti.Model.smoothOfRelativeDimension_projectiveLine` and
  `TauCeti.Model.isProper_projectiveLine`: this model is smooth of relative dimension one and
  proper.
* `TauCeti.HasNodalReduction.projectiveLine`: `ℙ¹_K` has nodal reduction over `R`.
* `TauCeti.HasNodalReduction.of_genus_eq_zero`: a regular proper curve of genus zero over `K` with a
  divisor of degree one has nodal reduction over `R`.

## References

* [The Stacks Project, Chapter 55, Semistable Reduction](https://stacks.math.columbia.edu/tag/0C2P)
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Section 10.1: models of curves.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Module (finrank)

namespace TauCeti

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace Model

/-- The identification of the generic fibre of `ℙ¹_R` with `ℙ¹_K`, over `K`. -/
def projectiveLineGenericFiberIso :
    genericFiber R K (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R)) ≅
      Over.mk (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)) :=
  Over.isoMk (AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection R K).isoPullback.symm
    (IsPullback.isoPullback_inv_snd _)

/-- **The projective line `ℙ¹_R` as a model of `ℙ¹_K`**: its generic fibre is identified with
`ℙ¹_K` through the base change of the projective line along `R → K`. -/
def projectiveLine :
    Model R K (AlgebraicGeometry.projectiveLine K)
      (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)) where
  total := AlgebraicGeometry.projectiveLine R
  toBase := AlgebraicGeometry.projectiveLine R ↘ Spec (.of R)
  flat := by
    have := SmoothOfRelativeDimension.smooth 1 (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R))
    infer_instance
  locallyOfFinitePresentation := by
    have := SmoothOfRelativeDimension.smooth 1 (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R))
    infer_instance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  genericFiberIso := projectiveLineGenericFiberIso R K

/-- The chosen generic-fibre identification of the projective-line model is the canonical one. -/
lemma projectiveLine_genericFiberIso :
    HEq (projectiveLine R K).genericFiberIso (projectiveLineGenericFiberIso R K) := by
  rw [projectiveLine]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The inverse of the generic-fibre identification is the canonical pullback isomorphism. -/
lemma projectiveLineGenericFiberIso_inv_left :
    (projectiveLineGenericFiberIso R K).inv.left =
      (AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection R K).isoPullback.hom :=
  (rfl)

/-- The total space of the model `ℙ¹_R` is the projective line over `R`. -/
@[simp]
lemma projectiveLine_total : (projectiveLine R K).total = AlgebraicGeometry.projectiveLine R :=
  (rfl)

/-- The structure morphism of the model `ℙ¹_R` is that of the projective line over `R`. -/
@[simp]
lemma projectiveLine_toBase :
    (projectiveLine R K).toBase =
      eqToHom (projectiveLine_total R K) ≫ (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R)) :=
  (rfl)

/-- The generic fibre of the projective-line model is included by base-change projection. -/
@[simp]
lemma genericι_projectiveLine :
    (projectiveLine R K).genericι =
      AlgebraicGeometry.projectiveLine.baseChangeProjection R K ≫
        eqToHom (projectiveLine_total R K).symm := by
  simp [genericι_def, projectiveLine, projectiveLineGenericFiberIso_inv_left]

/-- The model `ℙ¹_R` of `ℙ¹_K` is smooth of relative dimension one over `R`. -/
instance smoothOfRelativeDimension_projectiveLine :
    SmoothOfRelativeDimension 1 (projectiveLine R K).toBase :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R)))

/-- The model `ℙ¹_R` of `ℙ¹_K` is proper over `R`. -/
lemma isProper_projectiveLine : (projectiveLine R K).IsProper :=
  inferInstanceAs
    (_root_.AlgebraicGeometry.IsProper (AlgebraicGeometry.projectiveLine R ↘ Spec (.of R)))

end Model

namespace HasNodalReduction

/-- **The projective line has nodal reduction**: `ℙ¹_R` is a smooth proper model of `ℙ¹_K`. -/
theorem projectiveLine :
    HasNodalReduction R K (AlgebraicGeometry.projectiveLine K)
      (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)) :=
  of_smooth_model (Model.projectiveLine R K) (Model.isProper_projectiveLine R K)

variable {R K}

/-- **A curve of genus zero with a divisor of degree one has nodal reduction.** Let `C` be a
regular proper curve over the fraction field `K` of a discrete valuation ring `R`, with `K`
integrally closed in `K(C)`. If `dim_K H¹(C, 𝒪_C) = 0` and some divisor on `C` has degree one,
then `C` has a proper at-worst-nodal model over `R`; indeed `C ≅ ℙ¹_K`, which has the smooth proper
model `ℙ¹_R`. -/
theorem of_genus_eq_zero (C : Scheme.{u}) [C.Over (Spec (.of K))] [C.IsCurveOver K]
    [∀ y : AlgebraicGeometry.CodimensionOnePoint C,
      IsDiscreteValuationRing (C.presheaf.stalk (y : C))]
    (hk : IsIntegrallyClosedIn K C.functionField)
    (hg : finrank K (AlgebraicGeometry.Scheme.Modules.Cohomology
      (AlgebraicGeometry.InvertibleSheaf.trivial C).obj 1) = 0)
    {D : AlgebraicGeometry.SchemeWeilDivisor C}
    (hD : AlgebraicGeometry.SchemeWeilDivisor.relativeDegree (C ↘ Spec (.of K)) D = 1) :
    HasNodalReduction R K C (C ↘ Spec (.of K)) := by
  obtain ⟨e, _⟩ := C.exists_iso_projectiveLine_of_genus_eq_zero hk hg hD
  exact (projectiveLine R K).of_iso
    (Over.isoMk (f := Over.mk (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)))
      (g := Over.mk (C ↘ Spec (.of K))) e.symm (by simp))

end HasNodalReduction

end TauCeti
