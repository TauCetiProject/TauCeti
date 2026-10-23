/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.ClosedImmersion

/-!
# Higher direct images along closed immersions

All positive higher direct images of a module sheaf along a closed immersion vanish. The
coefficient need not be quasi-coherent, and neither the coefficient nor the immersion needs to be
flat over any base. For quasi-coherent coefficients on a locally Noetherian scheme this is also a
case of the vanishing along affine morphisms
(`AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom`), which gives the
coherence of the higher direct images of a coherent sheaf along a finite morphism.

The proof uses exactness of closed-embedding pushforward of abelian sheaves, reflected
through the exact faithful functor forgetting module structures. Mathlib's injective
resolution comparison then computes the higher direct images.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10 and Proposition 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Positive higher direct images along a closed immersion vanish, for arbitrary
module sheaves. -/
theorem isZero_higherDirectImage_succ_of_isClosedImmersion (M : X.Modules) (q : ℕ) :
    IsZero ((f.higherDirectImage (q + 1)).obj M) := by
  have := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  exact (Scheme.Modules.pushforward f).isZero_rightDerived_succ M q

end AlgebraicGeometry.Scheme.Hom
