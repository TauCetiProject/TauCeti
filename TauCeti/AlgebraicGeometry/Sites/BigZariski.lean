/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Affine hypercovers in the big Zariski site

This file complements `Mathlib.AlgebraicGeometry.Sites.BigZariski` by providing a spectrum witness
for the overlap components of `AlgebraicGeometry.Scheme.affineOneHypercover`.

## Main results

* `AlgebraicGeometry.Scheme.exists_spec_affineOneHypercover_Y`: every overlap component
  `X.affineOneHypercover.Y k` is `Spec R` for some commutative ring `R`.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every overlap component `X.affineOneHypercover.Y k` of the canonical affine `1`-hypercover of
a scheme `X` is `Spec R` for some commutative ring `R`. -/
lemma exists_spec_affineOneHypercover_Y (X : Scheme.{u}) {i j : X.affineOneHypercover.I₀}
    (k : X.affineOneHypercover.I₁ i j) :
    ∃ R : CommRingCat.{u}, X.affineOneHypercover.Y k = Spec R := by
  dsimp only [Scheme.affineOneHypercover,
    GrothendieckTopology.OneHypercover.mk'_toPreOneHypercover,
    PreZeroHypercover.refineOneHypercover_Y]
  exact ⟨_, AffineOpenCover.openCover_X
    (Limits.pullback (X.affineCover.f i) (X.affineCover.f j)).affineOpenCover k⟩

end AlgebraicGeometry.Scheme
