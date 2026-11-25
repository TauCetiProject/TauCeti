/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.ClosedImmersion

/-!
# Cohomology on the projective line of a direct image from a base change

Let `S` be an `R`-algebra and `p : ℙ¹_S ⟶ ℙ¹_R` the projection, the base change of
`Spec S ⟶ Spec R` (`TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`).
This file computes the cohomology of the direct image `F = p_* 𝒪_{ℙ¹_S}` on `ℙ¹_R`:
`H⁰(ℙ¹_R, F) = S` as an `R`-module and `Hⁿ(ℙ¹_R, F) = 0` for `n ≥ 1`.

The projection is affine, as a base change of a morphism of affine schemes
(`TauCeti.AlgebraicGeometry.projectiveLine.isAffineHom_baseChangeProjection`), so the cohomology
of `F` is that of the quasi-coherent sheaf `𝒪_{ℙ¹_S}`, `R`-linearly
(`AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsAffineHom`).
The latter is `S` in degree zero and vanishes in positive degrees
(`TauCeti.AlgebraicGeometry.projectiveLine.cohomologyZeroTrivialLinearEquiv`,
`TauCeti.AlgebraicGeometry.projectiveLine.subsingleton_cohomology_succ_trivial`).

For a quotient `S = R ⧸ I` the projection is a closed immersion
(`TauCeti.AlgebraicGeometry.projectiveLine.isClosedImmersion_baseChangeProjection`), and `F` is
the structure sheaf of the closed subscheme `ℙ¹_{R/I}`. For `R = k⟦t⟧` and `I = (t)`, `F` is not
flat over `R`, since its global sections `R ⧸ (t)` are not, although `ℙ¹_R` is flat and proper
over `R`.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLine.cohomologyZeroPushforwardLinearEquiv`:
  `H⁰(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) ≃ₗ[R] S`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.cohomologyZeroPushforwardLinearEquiv_symm_apply`: the
  class in `H⁰(ℙ¹_R, p_* 𝒪_{ℙ¹_S})` of an element of `S`.
* `TauCeti.AlgebraicGeometry.projectiveLine.subsingleton_cohomology_pushforward_succ`:
  `Hⁿ⁺¹(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) = 0`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

open _root_.AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

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
  ((baseChangeProjection R S).cohomologyPushforwardBaseLinearEquivOfIsAffineHom R _ 0).trans
    ((cohomologyZeroTrivialLinearEquiv S).restrictScalars R)

/-- Under `cohomologyZeroPushforwardLinearEquiv`, an element `s` of `S` is the class of the
constant function `s` on `ℙ¹_S`, transported along the projection. -/
theorem cohomologyZeroPushforwardLinearEquiv_symm_apply (s : S) :
    (cohomologyZeroPushforwardLinearEquiv R S).symm s =
      ((baseChangeProjection R S).cohomologyPushforwardIsoOfIsAffineHom _ 0).inv
        ((cohomologyZeroTrivialLinearEquiv S).symm s) := by
  simp only [cohomologyZeroPushforwardLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsAffineHom_symm_apply,
    LinearEquiv.restrictScalars_symm_apply]

/-- **Higher cohomology of a direct image from a base change of the projective line vanishes.**
`Hⁿ⁺¹(ℙ¹_R, p_* 𝒪_{ℙ¹_S}) = 0` for the projection `p : ℙ¹_S ⟶ ℙ¹_R`. -/
instance subsingleton_cohomology_pushforward_succ (n : ℕ) :
    Subsingleton (Cohomology ((pushforward (baseChangeProjection R S)).obj
      (InvertibleSheaf.trivial (projectiveLine S)).obj) (n + 1)) := by
  suffices Subsingleton (Cohomology (InvertibleSheaf.trivial (projectiveLine S)).obj (n + 1)) from
    ((baseChangeProjection R S).cohomologyPushforwardIsoOfIsAffineHom _
      (n + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  infer_instance

end TauCeti.AlgebraicGeometry.projectiveLine
