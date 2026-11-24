/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Linear

/-!
# Cohomology on the projective line of a direct image from a base change

Let `S` be an `R`-algebra and `p : ℙ¹_S ⟶ ℙ¹_R` the projection, the base change of
`Spec S ⟶ Spec R` (`TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`).
This file computes the cohomology of the direct image `F = p_* 𝒪_{ℙ¹_S}` on `ℙ¹_R`:
`H⁰(ℙ¹_R, F) = S` as an `R`-module and `Hⁿ(ℙ¹_R, F) = 0` for `n ≥ 1`.

The projection is affine, as a base change of a morphism of affine schemes, so the positive
higher direct images of the quasi-coherent sheaf `𝒪_{ℙ¹_S}` along it vanish
(`AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom`) and the cohomology
of `F` is that of `𝒪_{ℙ¹_S}`, `R`-linearly
(`AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage`).
The latter is `S` in degree zero and vanishes in positive degrees
(`TauCeti.AlgebraicGeometry.projectiveLine.cohomologyZeroTrivialLinearEquiv`,
`TauCeti.AlgebraicGeometry.projectiveLine.subsingleton_cohomology_one_trivial`).

For a quotient `S = R ⧸ I` the projection is a closed immersion
(`TauCeti.AlgebraicGeometry.projectiveLine.isClosedImmersion_baseChangeProjection`), and `F` is
the structure sheaf of the closed subscheme `ℙ¹_{R/I}`. For `R = k⟦t⟧` and `I = (t)`, `F` is not
flat over `R`, since its global sections `R ⧸ (t)` are not, although `ℙ¹_R` is flat and proper
over `R`.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLine.cohomologyZeroPushforwardLinearEquiv`:
  `H⁰(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) ≃ₗ[R] S`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.isAffineHom_baseChangeProjection`: the projection
  `ℙ¹_S ⟶ ℙ¹_R` is affine.
* `TauCeti.AlgebraicGeometry.projectiveLine.subsingleton_cohomology_pushforward_succ`:
  `Hⁿ⁺¹(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) = 0`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

open _root_.AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The projection `ℙ¹_S ⟶ ℙ¹_R` is affine, as the base change of `Spec S ⟶ Spec R`. -/
instance isAffineHom_baseChangeProjection : IsAffineHom (baseChangeProjection R S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeProjection R S).flip
    (inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R S)))))

/-- The positive higher direct images of the structure sheaf of `ℙ¹_S` along the projection
`ℙ¹_S ⟶ ℙ¹_R` vanish. -/
theorem isZero_higherDirectImage_succ_baseChangeProjection (q : ℕ) :
    Limits.IsZero (((baseChangeProjection R S).higherDirectImage (q + 1)).obj
      (InvertibleSheaf.trivial (projectiveLine S)).obj) :=
  Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom _ _ q

/-- **Global sections of a direct image from a base change of the projective line.** The zeroth
cohomology on `ℙ¹_R` of the direct image of `𝒪_{ℙ¹_S}` along `ℙ¹_S ⟶ ℙ¹_R` is `S`, as an
`R`-module. -/
noncomputable def cohomologyZeroPushforwardLinearEquiv :
    Cohomology ((pushforward (baseChangeProjection R S)).obj
      (InvertibleSheaf.trivial (projectiveLine S)).obj) 0 ≃ₗ[R] S :=
  letI : (projectiveLine S).Over (Spec (.of R)) :=
    ⟨(projectiveLine S ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  haveI : (baseChangeProjection R S).IsOver (Spec (.of R)) :=
    ⟨(isPullback_baseChangeProjection R S).w⟩
  haveI := isScalarTower_cohomology_of_comp_eq (R := R) (S := S) (X := projectiveLine S) rfl
    (InvertibleSheaf.trivial (projectiveLine S)).obj 0
  (Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage _ R _
    (isZero_higherDirectImage_succ_baseChangeProjection R S) 0).trans
    ((cohomologyZeroTrivialLinearEquiv S).restrictScalars R)

/-- **Higher cohomology of a direct image from a base change of the projective line vanishes.**
`Hⁿ⁺¹(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) = 0` for the projection `p : ℙ¹_S ⟶ ℙ¹_R`. -/
instance subsingleton_cohomology_pushforward_succ (n : ℕ) :
    Subsingleton (Cohomology ((pushforward (baseChangeProjection R S)).obj
      (InvertibleSheaf.trivial (projectiveLine S)).obj) (n + 1)) := by
  suffices Subsingleton (Cohomology (InvertibleSheaf.trivial (projectiveLine S)).obj (n + 1)) from
    ((baseChangeProjection R S).cohomologyPushforwardIsoOfIsZeroHigherDirectImage _
      (isZero_higherDirectImage_succ_baseChangeProjection R S)
        (n + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  rcases n with _ | n
  · exact subsingleton_cohomology_one_trivial S
  · exact (Pi.basisFun S (Fin 2)).subsingleton_cohomology_proj_of_card_le _ (n + 2) (by simp)

end TauCeti.AlgebraicGeometry.projectiveLine
