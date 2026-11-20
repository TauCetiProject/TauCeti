/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Cubical
public import TauCeti.AlgebraicTopology.Singular.Circle

/-!
# The cubical class of the standard loop of the circle

For the circle `S¹`, oriented by the standard loop `t ↦ (cos 2πt, sin 2πt)`, the
cubical–simplicial comparison `TauCeti.singularCubicalHomologyIso` sends the cubical class of the
standard loop to minus the fundamental class `TauCeti.circleFundamentalClass`
(`TauCeti.singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop`). The sign comes from the
two boundary conventions: the cubical boundary of a `1`-cube `c` is `c(0) - c(1)`, while the
simplicial boundary of a `1`-simplex `σ` is `σ(1) - σ(0)`, and the fundamental class of the circle
is the class of the standard loop read as a singular simplex.

## Main results

* `TauCeti.singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop`: the cubical class of the
  standard loop of the circle is minus its fundamental class.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace TauCeti

variable (k : Type) [Ring k]

/-- **The cubical class of the standard loop of the circle is minus its fundamental class**: over
every ring `k`, the cubical–simplicial comparison carries the class of the `1`-cube
`t ↦ (cos 2πt, sin 2πt)` in normalized cubical homology to `-[S¹]`, the negative of
`TauCeti.circleFundamentalClass`. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop :
    (singularCubicalHomologyIso k (TopCat.of Sphere1) 1).inv
        (GenLoop.cubicalHurewicz k circleGenLoop) =
      -(circleFundamentalClass (ModuleCat.of k k)).hom 1 := by
  rw [GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz, hurewicz_circleGenLoop,
    ModuleCat.hom_neg, LinearMap.neg_apply]

end TauCeti
