/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# The projective line over a quotient ring

For an `R`-algebra `S`, the projective line `ℙ¹_S` is the base change of `ℙ¹_R` along
`Spec S ⟶ Spec R` (`TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`).
When `R → S` is surjective, for instance for a quotient `S = R ⧸ I`, the morphism
`Spec S ⟶ Spec R` is a closed immersion, and so is its base change, the projection
`ℙ¹_S ⟶ ℙ¹_R`: the projective line over `R ⧸ I` is the closed subscheme of `ℙ¹_R` cut out by
`I`. In particular, for a ring `A` and an element `t`, the special fibre `ℙ¹_{A/(t)}` is a closed
subscheme of `ℙ¹_A`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.isClosedImmersion_baseChangeProjection`: for a
  surjective `R → S`, the projection `ℙ¹_S ⟶ ℙ¹_R` is a closed immersion.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- **The projective line over a quotient is a closed subscheme.** If `R → S` is surjective, the
projection `ℙ¹_S ⟶ ℙ¹_R`, the base change of the closed immersion `Spec S ⟶ Spec R`, is a closed
immersion. -/
theorem isClosedImmersion_baseChangeProjection (h : Function.Surjective (algebraMap R S)) :
    IsClosedImmersion (baseChangeProjection R S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeProjection R S).flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R S)) h)

/-- The projection from the projective line over a quotient ring is a closed immersion. -/
instance isClosedImmersion_baseChangeProjection_quotient (I : Ideal R) :
    IsClosedImmersion (baseChangeProjection R (R ⧸ I)) :=
  isClosedImmersion_baseChangeProjection R (R ⧸ I) Ideal.Quotient.mk_surjective

end TauCeti.AlgebraicGeometry.projectiveLine
