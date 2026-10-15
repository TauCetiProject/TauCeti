/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance

/-!
# Homotopy invariance of singular cohomology with local coefficients

Let `H` be a homotopy from `f : X ⟶ Y` to `g : X ⟶ Y` and let `L` be a local coefficient system
on `Y`. The maps induced by `f` and `g` on twisted singular cochains land in the cochains twisted
by the two pullback systems `f⁎L` and `g⁎L`, which `LocalCoefficientSystem.pullbackHomotopyIso`
identifies by transport along the homotopy. Applying `Hom(-, M)` to the chain homotopy
`TopCat.Homotopy.twistedChainComplexHomotopy` of twisted chains shows that after this
identification the two cochain maps are cochain homotopic, so that they agree on twisted
cohomology.

## Main declarations

* `TopCat.Homotopy.twistedCochainComplexHomotopy`: the cochain homotopy of twisted cochain
  complexes.
* `TopCat.Homotopy.twistedCohomologyMap_eq_comp`: homotopic maps induce the same map on twisted
  cohomology, up to the identification of the two pullback systems.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Opposite TauCeti.LocalCoefficientSystem

universe u v w

namespace TopCat.Homotopy

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R Y)

/-- A homotopy `H` from `f` to `g` induces a cochain homotopy from the map of twisted cochain
complexes induced by `f` to the map induced by `g`, followed by the identification of the pullback
systems along `H`. -/
def twistedCochainComplexHomotopy :
    _root_.Homotopy (twistedCochainComplexMap k M f L)
      (twistedCochainComplexMap k M g L ≫
        twistedCochainComplexCoefficientMap k M ((pullbackHomotopyIso H).hom.app L)) :=
  ((H.twistedChainComplexHomotopy L).linearYonedaFunctorMap k M).trans
    (.ofEq (by
      rw [op_comp, Functor.map_comp]
      -- The two sides are the same composite, the right one written with the abbreviations
      -- `twistedCochainComplexMap` and `twistedCochainComplexCoefficientMap`.
      rfl))

/-- **Homotopy invariance of cohomology with local coefficients**: homotopic maps induce the same
map on twisted singular cohomology, after the identification of the two pullback systems by
transport along the homotopy. -/
lemma twistedCohomologyMap_eq_comp (n : ℕ) :
    twistedCohomologyMap k M f L n =
      twistedCohomologyMap k M g L n ≫
        twistedCohomologyCoefficientMap k M ((pullbackHomotopyIso H).hom.app L) n :=
  ((H.twistedCochainComplexHomotopy k M L).homologyMap_eq n).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

end TopCat.Homotopy
