/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
import TauCeti.CategoryTheory.EpiMono

/-!
# Homotopy invariance of singular cohomology with local coefficients

Let `H` be a homotopy from `f : X ⟶ Y` to `g : X ⟶ Y` and let `L` be a local coefficient system
on `Y`. The maps induced by `f` and `g` on twisted singular cochains land in the cochains twisted
by the two pullback systems `f⁎L` and `g⁎L`, which `LocalCoefficientSystem.pullbackHomotopyIso`
identifies by transport along the homotopy. Applying `Hom(-, M)` to the chain homotopy
`TopCat.Homotopy.twistedChainComplexHomotopy` of twisted chains shows that after this
identification the two cochain maps are cochain homotopic, so that they agree on twisted
cohomology.

Consequently a homotopy equivalence induces isomorphisms on twisted cohomology, for every local
coefficient system and every module of values. Unlike the comparison for weak homotopy
equivalences, `ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedCohomologyMap`, this needs no
projectivity of the fibres of the system: the cochain homotopies come from actual homotopies.

## Main declarations

* `TopCat.Homotopy.twistedCochainComplexHomotopy`: the cochain homotopy of twisted cochain
  complexes.
* `TopCat.Homotopy.twistedCohomologyMap_eq_comp`: homotopic maps induce the same map on twisted
  cohomology, up to the identification of the two pullback systems.
* `ContinuousMap.HomotopyEquiv.isIso_twistedCohomologyMap`: a homotopy equivalence induces
  isomorphisms on twisted cohomology.

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

namespace TopCat.Homotopy

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {a : X ⟶ Y} {b : Y ⟶ X}
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)

/-- If `a ≫ b` is homotopic to the identity, then the composite of the maps induced by `b` and `a`
on twisted cohomology, followed by the identification of `a⁎(b⁎L)` with `(a ≫ b)⁎L`, is an
isomorphism. -/
private lemma isIso_twistedCohomologyMap_comp (H : TopCat.Homotopy (a ≫ b) (𝟙 X))
    (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R X) (n : ℕ) :
    IsIso (twistedCohomologyMap k M b L n ≫ twistedCohomologyMap k M a ((pullback b.hom).obj L) n ≫
      twistedCohomologyCoefficientMap k M ((pullbackCompIso a.hom b.hom).hom.app L) n) := by
  rw [← twistedCohomologyMap_comp, H.twistedCohomologyMap_eq_comp, twistedCohomologyMap_id]
  infer_instance

end TopCat.Homotopy

namespace ContinuousMap.HomotopyEquiv

variable {R : Type u} [Ring R] {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)

/-- **A homotopy equivalence induces isomorphisms on singular cohomology with local
coefficients**: for a homotopy equivalence `e : X ≃ₕ Y`, a local coefficient system `L` on `Y`
and a module of values `M`, the map `Hⁿ(Y; L, M) ⟶ Hⁿ(X; e⁎L, M)` is an isomorphism. -/
theorem isIso_twistedCohomologyMap (e : X ≃ₕ Y)
    (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R (TopCat.of Y)) (n : ℕ) :
    IsIso (twistedCohomologyMap k M (TopCat.ofHom e.toFun) L n) := by
  let f := TopCat.ofHom e.toFun
  let g := TopCat.ofHom e.invFun
  -- `g ≫ f ≃ 𝟙` and `f ≫ g ≃ 𝟙` make the composites of the map of `g` on `Hⁿ(X; f⁎L)` with the
  -- maps of `f` on either side isomorphisms. So it is an isomorphism, and then so is the map
  -- of `f`.
  have h₁ := TopCat.Homotopy.isIso_twistedCohomologyMap_comp (a := g) (b := f) k M
    e.right_inv.some L n
  have h₂ := TopCat.Homotopy.isIso_twistedCohomologyMap_comp (a := f) (b := g) k M
    e.left_inv.some ((pullback f.hom).obj L) n
  rw [← Category.assoc] at h₁
  have h₃ : IsIso (twistedCohomologyMap k M f L n ≫
      twistedCohomologyMap k M g ((pullback f.hom).obj L) n) :=
    IsIso.of_isIso_comp_right _
      (twistedCohomologyCoefficientMap k M ((pullbackCompIso g.hom f.hom).hom.app L) n)
  have := IsIso.of_isIso_comp_of_isIso_comp h₃ h₂
  exact IsIso.of_isIso_comp_right _ (twistedCohomologyMap k M g ((pullback f.hom).obj L) n)

end ContinuousMap.HomotopyEquiv
