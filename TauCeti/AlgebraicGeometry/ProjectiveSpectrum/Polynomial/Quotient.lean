/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Dehomogenization

/-!
# The projective scheme of a homogeneous ideal of a polynomial ring

Let `I` be a homogeneous ideal of `R[X₀, …, Xₙ]`, graded by total degree, and let
`A = R[X₀, …, Xₙ] ⧸ I` with the induced grading (`HomogeneousIdeal.quotientGrading`). This file
makes the closed subscheme `Proj A` of projective `n`-space a scheme over `Spec R`, through the
coefficient morphism `AlgebraicGeometry.Proj.toSpecCoeff`, and shows that it is proper over `R`
and covered by the standard affine charts `D₊(Xⱼ)`. The charts themselves are computed in
`HomogeneousIdeal.awayEquivDehomogenize`.

## Main results

* the instance `IsProper (Proj I.quotientGrading ↘ Spec (.of R))`: `Proj A` is proper over `R`.
* `HomogeneousIdeal.iSup_basicOpen_eq_top`: the standard charts `D₊(Xⱼ)` cover `Proj A`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.4.9 and
  Proposition II.2.5.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace HomogeneousIdeal

variable {R : Type u} [CommRing R] {n : ℕ}
  (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) R))

/-- The `Proj` of the quotient of `R[X₀, …, Xₙ]` by a homogeneous ideal is a scheme over `Spec R`
through the coefficient morphism `Proj.toSpecCoeff`. -/
noncomputable instance : (Proj I.quotientGrading).Over (Spec (.of R)) where
  hom := Proj.toSpecCoeff _

/-- The structure morphism of `Proj (R[X₀, …, Xₙ] ⧸ I)` as a scheme over `Spec R` is the
coefficient morphism `Proj.toSpecCoeff`. -/
theorem over_proj_quotientGrading :
    Proj I.quotientGrading ↘ Spec (.of R) = Proj.toSpecCoeff _ :=
  (rfl)

/-- **`Proj` of a quotient of a polynomial ring by a homogeneous ideal is proper.** -/
instance : IsProper (Proj I.quotientGrading ↘ Spec (.of R)) :=
  inferInstanceAs (IsProper (Proj.toSpecCoeff _))

/-- **The standard charts `D₊(Xⱼ)` cover `Proj (R[X₀, …, Xₙ] ⧸ I)`.** -/
theorem iSup_basicOpen_eq_top :
    ⨆ j, Proj.basicOpen I.quotientGrading (Ideal.Quotient.mk I.toIdeal (X j)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ I.irrelevant_le_span_range_mk_X

end HomogeneousIdeal
