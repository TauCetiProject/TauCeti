/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PeripheralLoops

/-!
# Peripheral conjugacy classes at arbitrary basepoints

The loops at `0` and `1`, together with the product-one element `periphInf`, determine conjugacy
classes in the fundamental group at every basepoint. Starting with these elements at `1/2`, this
file transports their classes along a path to an arbitrary point. Different paths give conjugate
elements, so the resulting class is independent of the path.

The element-level transports are `FundamentalGroup.fundamentalGroupMulEquivOfPath γ periph0` and
its companions; transport along any path realizes the canonical classes defined here, by the
`simp` lemma `FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt` followed by the
folding lemmas below.

## Main declarations

* `periph0ConjClass`, `periph1ConjClass`, `periphInfConjClass`: the conjugacy classes of the
  three peripheral elements at an arbitrary basepoint.
* `conjClassAt_basePt_periph0`, `conjClassAt_basePt_periph1`, `conjClassAt_basePt_periphInf`:
  `simp` lemmas folding the generic `FundamentalGroup.conjClassAt` into these classes.
* `periph0ConjClass_basePt`, `periph1ConjClass_basePt`, `periphInfConjClass_basePt`: at the
  standard basepoint these are the classes of `periph0`, `periph1`, and `periphInf`.
* `map_periph0ConjClass`, `map_periph1ConjClass`, `map_periphInfConjClass`: the classes are
  natural under basepoint change along any path.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7.
-/

public section

namespace TauCeti.ThricePuncturedSphere

variable {x : ThricePuncturedSphere}

/-- The conjugacy class of a positive peripheral loop around `0` at `x`. -/
noncomputable def periph0ConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  FundamentalGroup.conjClassAt basePt x periph0

/-- The conjugacy class of a positive peripheral loop around `1` at `x`. -/
noncomputable def periph1ConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  FundamentalGroup.conjClassAt basePt x periph1

/-- The conjugacy class transported from the product-one element `periphInf` at `x`. -/
noncomputable def periphInfConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  FundamentalGroup.conjClassAt basePt x periphInf

/-- The path-independent class of `periph0` at `x` is `periph0ConjClass x`. -/
@[simp] theorem conjClassAt_basePt_periph0 :
    FundamentalGroup.conjClassAt basePt x periph0 = periph0ConjClass x :=
  (rfl)

/-- The path-independent class of `periph1` at `x` is `periph1ConjClass x`. -/
@[simp] theorem conjClassAt_basePt_periph1 :
    FundamentalGroup.conjClassAt basePt x periph1 = periph1ConjClass x :=
  (rfl)

/-- The path-independent class of `periphInf` at `x` is `periphInfConjClass x`. -/
@[simp] theorem conjClassAt_basePt_periphInf :
    FundamentalGroup.conjClassAt basePt x periphInf = periphInfConjClass x :=
  (rfl)

/-- At the standard basepoint, the peripheral class at `0` is the class of `periph0`. -/
@[simp] theorem periph0ConjClass_basePt : periph0ConjClass basePt = ConjClasses.mk periph0 :=
  FundamentalGroup.conjClassAt_self basePt periph0

/-- At the standard basepoint, the peripheral class at `1` is the class of `periph1`. -/
@[simp] theorem periph1ConjClass_basePt : periph1ConjClass basePt = ConjClasses.mk periph1 :=
  FundamentalGroup.conjClassAt_self basePt periph1

/-- At the standard basepoint, the class of the product-one element is the class of `periphInf`. -/
@[simp] theorem periphInfConjClass_basePt :
    periphInfConjClass basePt = ConjClasses.mk periphInf :=
  FundamentalGroup.conjClassAt_self basePt periphInf

/-- The class at `0` is natural under transport between any two basepoints. -/
@[simp] theorem map_periph0ConjClass {y : ThricePuncturedSphere} (δ : Path x y) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath δ :
        FundamentalGroup ThricePuncturedSphere x →* FundamentalGroup ThricePuncturedSphere y)
      (periph0ConjClass x) = periph0ConjClass y :=
  FundamentalGroup.map_conjClassAt δ periph0

/-- The class at `1` is natural under transport between any two basepoints. -/
@[simp] theorem map_periph1ConjClass {y : ThricePuncturedSphere} (δ : Path x y) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath δ :
        FundamentalGroup ThricePuncturedSphere x →* FundamentalGroup ThricePuncturedSphere y)
      (periph1ConjClass x) = periph1ConjClass y :=
  FundamentalGroup.map_conjClassAt δ periph1

/-- The class of the product-one element is natural under transport between basepoints. -/
@[simp] theorem map_periphInfConjClass {y : ThricePuncturedSphere} (δ : Path x y) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath δ :
        FundamentalGroup ThricePuncturedSphere x →* FundamentalGroup ThricePuncturedSphere y)
      (periphInfConjClass x) = periphInfConjClass y :=
  FundamentalGroup.map_conjClassAt δ periphInf

end TauCeti.ThricePuncturedSphere
