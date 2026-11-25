/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# The projective line over a quotient ring

For an `R`-algebra `S`, the projection `ℙ¹_S ⟶ ℙ¹_R` is, up to the coordinate identification
`S² = S ⊗[R] R²`, the coefficient projection `Proj (S ⊗[R] Sym_R R²) ⟶ Proj (Sym_R R²)`
(`TauCeti.AlgebraicGeometry.projectiveLine.baseChangeProjection_def`). That projection is the base
change of `Spec S ⟶ Spec R`, so it is affine
(`AlgebraicGeometry.Proj.isAffineHom_baseChangeProjection`), and when `R → S` is surjective, for
instance for a quotient `S = R ⧸ I`, it is a closed immersion
(`AlgebraicGeometry.Proj.isClosedImmersion_baseChangeProjection`): the projective line over
`R ⧸ I` is the closed subscheme of `ℙ¹_R` cut out by `I`. In particular, for a ring `A` and an
element `t`, the special fibre `ℙ¹_{A/(t)}` is a closed subscheme of `ℙ¹_A`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.isAffineHom_baseChangeProjection`: the projection
  `ℙ¹_S ⟶ ℙ¹_R` is affine.
* `TauCeti.AlgebraicGeometry.projectiveLine.isClosedImmersion_baseChangeProjection`: for a
  surjective `R → S`, the projection `ℙ¹_S ⟶ ℙ¹_R` is a closed immersion.
-/
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The projection `ℙ¹_S ⟶ ℙ¹_R` is affine, as the base change of `Spec S ⟶ Spec R`. -/
instance isAffineHom_baseChangeProjection : IsAffineHom (baseChangeProjection R S) := by
  rw [baseChangeProjection_def]
  infer_instance

/-- **The projective line over a quotient is a closed subscheme.** If `R → S` is surjective, the
projection `ℙ¹_S ⟶ ℙ¹_R`, the base change of the closed immersion `Spec S ⟶ Spec R`, is a closed
immersion. -/
theorem isClosedImmersion_baseChangeProjection (h : Function.Surjective (algebraMap R S)) :
    IsClosedImmersion (baseChangeProjection R S) := by
  have := Proj.isClosedImmersion_baseChangeProjection
    (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) S h
  rw [baseChangeProjection_def]
  infer_instance

/-- The projection from the projective line over a quotient ring is a closed immersion. -/
instance isClosedImmersion_baseChangeProjection_quotient (I : Ideal R) :
    IsClosedImmersion (baseChangeProjection R (R ⧸ I)) :=
  isClosedImmersion_baseChangeProjection R (R ⧸ I) Ideal.Quotient.mk_surjective

end TauCeti.AlgebraicGeometry.projectiveLine
