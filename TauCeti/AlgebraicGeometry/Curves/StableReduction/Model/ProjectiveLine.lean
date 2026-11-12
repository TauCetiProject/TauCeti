/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# The projective line as a model of the projective line

Let `R` be a discrete valuation ring with fraction field `K`. The projective line `ℙ¹_R` is a
smooth proper model over `R` of the projective line `ℙ¹_K`: its generic fibre is `ℙ¹_K`, since the
formation of `ℙ¹` commutes with base change
(`TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`).

## Main definitions

* `TauCeti.Model.projectiveLine R K`: the projective line `ℙ¹_R`, as a model of `ℙ¹_K` over `R`.

## Main results

* `TauCeti.Model.smoothOfRelativeDimension_projectiveLine` and
  `TauCeti.Model.isProper_projectiveLine`: this model is smooth of relative dimension one and
  proper.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Section 10.1: models of curves.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

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

end TauCeti
