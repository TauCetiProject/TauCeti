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

The three punctures of `ℂ ∖ {0, 1}` determine conjugacy classes in the fundamental group at every
basepoint. Starting with the fixed peripheral loops at `1/2`, this file transports their classes
along a path to an arbitrary point. Different paths give conjugate elements, so the resulting
class is independent of the path.

The element-level transports are retained because a path is needed to compare fundamental groups
at different basepoints. The canonical `ConjClasses` values are the path-independent invariants
used when only a puncture, rather than a chosen based loop, matters.

## Main declarations

* `periph0At`, `periph1At`, `periphInfAt`: the three peripheral elements transported along a
  specified path from the standard basepoint.
* `periph0ConjClass`, `periph1ConjClass`, `periphInfConjClass`: their conjugacy classes at an
  arbitrary basepoint.
* `map_mk_periph0_eq_periph0ConjClass`, `map_mk_periph1_eq_periph1ConjClass`, and
  `map_mk_periphInf_eq_periphInfConjClass`: transport along any path realizes the corresponding
  canonical conjugacy class.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7.
-/

public section

namespace TauCeti.ThricePuncturedSphere

variable {x : ThricePuncturedSphere}

/-- The peripheral element at `0`, transported from the standard basepoint along `γ`. -/
noncomputable def periph0At (γ : Path basePt x) : FundamentalGroup ThricePuncturedSphere x :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath γ periph0

/-- The peripheral element at `1`, transported from the standard basepoint along `γ`. -/
noncomputable def periph1At (γ : Path basePt x) : FundamentalGroup ThricePuncturedSphere x :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath γ periph1

/-- The peripheral element at `∞`, transported from the standard basepoint along `γ`. -/
noncomputable def periphInfAt (γ : Path basePt x) : FundamentalGroup ThricePuncturedSphere x :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath γ periphInf

/-- Two paths to the same basepoint give conjugate transported peripheral elements at `0`. -/
theorem isConj_periph0At_of_paths (γ δ : Path basePt x) :
    IsConj (periph0At γ) (periph0At δ) :=
  FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths γ δ periph0

/-- Two paths to the same basepoint give conjugate transported peripheral elements at `1`. -/
theorem isConj_periph1At_of_paths (γ δ : Path basePt x) :
    IsConj (periph1At γ) (periph1At δ) :=
  FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths γ δ periph1

/-- Two paths to the same basepoint give conjugate transported peripheral elements at `∞`. -/
theorem isConj_periphInfAt_of_paths (γ δ : Path basePt x) :
    IsConj (periphInfAt γ) (periphInfAt δ) :=
  FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths γ δ periphInf

private noncomputable def basepointPath (x : ThricePuncturedSphere) : Path basePt x :=
  PathConnectedSpace.somePath basePt x

/-- The conjugacy class of a positive peripheral loop around `0` at `x`. -/
noncomputable def periph0ConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  ConjClasses.mk (periph0At (basepointPath x))

/-- The conjugacy class of a positive peripheral loop around `1` at `x`. -/
noncomputable def periph1ConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  ConjClasses.mk (periph1At (basepointPath x))

/-- The conjugacy class of a peripheral loop around `∞` at `x`, with the orientation fixed by
the product-one convention `periphInf * periph1 * periph0 = 1`. -/
noncomputable def periphInfConjClass (x : ThricePuncturedSphere) :
    ConjClasses (FundamentalGroup ThricePuncturedSphere x) :=
  ConjClasses.mk (periphInfAt (basepointPath x))

/-- Transport along any path from the standard basepoint realizes the canonical peripheral class
at `0`. -/
theorem mk_periph0At_eq_periph0ConjClass (γ : Path basePt x) :
    ConjClasses.mk (periph0At γ) = periph0ConjClass x := by
  rw [periph0ConjClass, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_periph0At_of_paths γ (basepointPath x)

/-- Transport along any path from the standard basepoint realizes the canonical peripheral class
at `1`. -/
theorem mk_periph1At_eq_periph1ConjClass (γ : Path basePt x) :
    ConjClasses.mk (periph1At γ) = periph1ConjClass x := by
  rw [periph1ConjClass, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_periph1At_of_paths γ (basepointPath x)

/-- Transport along any path from the standard basepoint realizes the canonical peripheral class
at `∞`. -/
theorem mk_periphInfAt_eq_periphInfConjClass (γ : Path basePt x) :
    ConjClasses.mk (periphInfAt γ) = periphInfConjClass x := by
  rw [periphInfConjClass, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_periphInfAt_of_paths γ (basepointPath x)

/-- Transport of the standard peripheral class at `0` along any path produces the canonical
class at its endpoint. -/
theorem map_mk_periph0_eq_periph0ConjClass (γ : Path basePt x) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
      (ConjClasses.mk periph0) = periph0ConjClass x := by
  rw [ConjClasses.map_mk]
  exact mk_periph0At_eq_periph0ConjClass γ

/-- Transport of the standard peripheral class at `1` along any path produces the canonical
class at its endpoint. -/
theorem map_mk_periph1_eq_periph1ConjClass (γ : Path basePt x) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
      (ConjClasses.mk periph1) = periph1ConjClass x := by
  rw [ConjClasses.map_mk]
  exact mk_periph1At_eq_periph1ConjClass γ

/-- Transport of the standard peripheral class at `∞` along any path produces the canonical
class at its endpoint. -/
theorem map_mk_periphInf_eq_periphInfConjClass (γ : Path basePt x) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
      (ConjClasses.mk periphInf) = periphInfConjClass x := by
  rw [ConjClasses.map_mk]
  exact mk_periphInfAt_eq_periphInfConjClass γ

end TauCeti.ThricePuncturedSphere
