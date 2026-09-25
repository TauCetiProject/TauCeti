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

/-- The product-one element `periphInf`, transported from the standard basepoint along `γ`. -/
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

/-- Two paths to the same basepoint give conjugate transports of `periphInf`. -/
theorem isConj_periphInfAt_of_paths (γ δ : Path basePt x) :
    IsConj (periphInfAt γ) (periphInfAt δ) :=
  FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths γ δ periphInf

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

/-- At the standard basepoint, the peripheral class at `0` is the class of `periph0`. -/
-- Not `@[simp]` (nor are the two companions below): simp rewrites subterms first, so it would
-- turn `ConjClasses.map _ (periph0ConjClass basePt)` into
-- `FundamentalGroup.conjClassAt basePt x periph0` instead of letting `map_periph0ConjClass`
-- produce the canonical `periph0ConjClass x`.
theorem periph0ConjClass_basePt : periph0ConjClass basePt = ConjClasses.mk periph0 :=
  FundamentalGroup.conjClassAt_self basePt periph0

/-- At the standard basepoint, the peripheral class at `1` is the class of `periph1`. -/
theorem periph1ConjClass_basePt : periph1ConjClass basePt = ConjClasses.mk periph1 :=
  FundamentalGroup.conjClassAt_self basePt periph1

/-- At the standard basepoint, the class of the product-one element is the class of `periphInf`. -/
theorem periphInfConjClass_basePt :
    periphInfConjClass basePt = ConjClasses.mk periphInf :=
  FundamentalGroup.conjClassAt_self basePt periphInf

/-- The three transported elements retain the defining product-one relation. -/
theorem periphInfAt_mul_periph1At_mul_periph0At (γ : Path basePt x) :
    periphInfAt γ * periph1At γ * periph0At γ = 1 := by
  simp only [periphInfAt, periph1At, periph0At, ← map_mul,
    periphInf_mul_periph1_mul_periph0, map_one]

/-- Transport along any path from the standard basepoint realizes the canonical peripheral class
at `0`. -/
@[simp] theorem mk_periph0At_eq_periph0ConjClass (γ : Path basePt x) :
    ConjClasses.mk (periph0At γ) = periph0ConjClass x := by
  exact FundamentalGroup.mk_transport_eq_conjClassAt γ periph0

/-- Transport along any path from the standard basepoint realizes the canonical peripheral class
at `1`. -/
@[simp] theorem mk_periph1At_eq_periph1ConjClass (γ : Path basePt x) :
    ConjClasses.mk (periph1At γ) = periph1ConjClass x := by
  exact FundamentalGroup.mk_transport_eq_conjClassAt γ periph1

/-- Transport along any path from the standard basepoint realizes the class of `periphInf`. -/
@[simp] theorem mk_periphInfAt_eq_periphInfConjClass (γ : Path basePt x) :
    ConjClasses.mk (periphInfAt γ) = periphInfConjClass x := by
  exact FundamentalGroup.mk_transport_eq_conjClassAt γ periphInf

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

/-- Transport of the standard product-one class along any path produces its class at the
endpoint. -/
theorem map_mk_periphInf_eq_periphInfConjClass (γ : Path basePt x) :
    ConjClasses.map (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
      (ConjClasses.mk periphInf) = periphInfConjClass x := by
  rw [ConjClasses.map_mk]
  exact mk_periphInfAt_eq_periphInfConjClass γ

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
