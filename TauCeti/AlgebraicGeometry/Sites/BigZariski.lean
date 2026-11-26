/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Affine hypercovers in the big Zariski site

This file complements `Mathlib.AlgebraicGeometry.Sites.BigZariski` by providing spectrum
witnesses for the components of `AlgebraicGeometry.Scheme.affineCover` and
`AlgebraicGeometry.Scheme.affineOneHypercover`.

## Main results

* `AlgebraicGeometry.Scheme.exists_spec_affineCover_X`: every component `X.affineCover.X i` is
  `Spec R` for some commutative ring `R`.
* `AlgebraicGeometry.Scheme.exists_spec_affineOneHypercover_X`: every base component
  `X.affineOneHypercover.X i` is `Spec R` for some commutative ring `R`.
* `AlgebraicGeometry.Scheme.exists_spec_affineOneHypercover_Y`: every overlap component
  `X.affineOneHypercover.Y k` is `Spec R` for some commutative ring `R`.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every component `X.affineCover.X i` of the canonical affine open cover of a scheme `X` is
`Spec R` for some commutative ring `R`. -/
lemma exists_spec_affineCover_X (X : Scheme.{u}) (i : X.affineCover.I₀) :
    ∃ R : CommRingCat.{u}, X.affineCover.X i = Spec R := by
  revert i
  rw [← openCover_affineOpenCover]
  intro i
  exact ⟨_, AffineOpenCover.openCover_X X.affineOpenCover i⟩

/-- Every base component `X.affineOneHypercover.X i` of the canonical affine `1`-hypercover of a
scheme `X` is `Spec R` for some commutative ring `R`. -/
lemma exists_spec_affineOneHypercover_X (X : Scheme.{u}) (i : X.affineOneHypercover.I₀) :
    ∃ R : CommRingCat.{u}, X.affineOneHypercover.X i = Spec R := by
  revert i
  rw [Scheme.affineOneHypercover_toPreOneHypercover_toPreZeroHypercover]
  exact exists_spec_affineCover_X X

/-- Every overlap component `X.affineOneHypercover.Y k` of the canonical affine `1`-hypercover of
a scheme `X` is `Spec R` for some commutative ring `R`. -/
lemma exists_spec_affineOneHypercover_Y (X : Scheme.{u}) {i j : X.affineOneHypercover.I₀}
    (k : X.affineOneHypercover.I₁ i j) :
    ∃ R : CommRingCat.{u}, X.affineOneHypercover.Y k = Spec R := by
  dsimp only [Scheme.affineOneHypercover,
    GrothendieckTopology.OneHypercover.mk'_toPreOneHypercover,
    PreZeroHypercover.refineOneHypercover_Y]
  exact exists_spec_affineCover_X _ k

end AlgebraicGeometry.Scheme
