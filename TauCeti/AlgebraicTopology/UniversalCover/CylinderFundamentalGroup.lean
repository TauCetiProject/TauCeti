/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupProduct
public import TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# The fundamental group of a cylinder

Multiplying a space by a simply connected factor does not change its fundamental group.
Combining the product formula for fundamental groups
(`TauCeti.FundamentalGroup.prodMulEquiv`) with the fact that a simply connected space has
trivial fundamental group gives, for a simply connected `Y`, the projection isomorphisms
`π₁(X × Y, (x, y)) ≃* π₁(X, x)` and `π₁(Y × X, (y, x)) ≃* π₁(X, x)`.

Feeding the circle computation `π₁(AddCircle p) ≃* Multiplicative ℤ`
(`TauCeti.AddCircle.fundamentalGroupMulEquiv`) into the first of these gives the fundamental
group of a cylinder over any simply connected base. The standard infinite cylinder
`AddCircle p × ℝ` is the case `Y = ℝ`, which is contractible and hence simply connected; its
fundamental group is infinite cyclic, `π₁(AddCircle p × ℝ) ≃* Multiplicative ℤ`.

This advances the universal-covers roadmap Stage 4 "applications"
(`TauCetiRoadmap/UniversalCovers/README.md`), extending the circle computation (item 12,
`π₁(S¹) ≅ ℤ`) and the torus computation to cylinders: the cylinder is `S¹` times a
contractible line, so its fundamental group agrees with that of the circle.

## Main declarations

* `TauCeti.FundamentalGroup.prodMulEquivRight`: for simply connected `Y`, the projection
  `π₁(X × Y, (x, y)) ≃* π₁(X, x)`.
* `TauCeti.FundamentalGroup.prodMulEquivLeft`: for simply connected `X`, the projection
  `π₁(X × Y, (x, y)) ≃* π₁(Y, y)`.
* `TauCeti.AddCircle.cylinderFundamentalGroupMulEquiv`: for a nonzero real period and any
  simply connected `Y`, `π₁(AddCircle p × Y, (x, y)) ≃* Multiplicative ℤ`.
* `TauCeti.AddCircle.realCylinderFundamentalGroupMulEquiv`: the standard infinite cylinder
  `π₁(AddCircle p × ℝ, (0, 0)) ≃* Multiplicative ℤ`.
* `TauCeti.UnitAddCircle.cylinderFundamentalGroupMulEquiv`: the unit-circle cylinder
  `π₁(UnitAddCircle × ℝ, (0, 0)) ≃* Multiplicative ℤ`.
-/

public section

namespace TauCeti

open Path.Homotopic

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- When the second factor `Y` is simply connected, the projection to `X` induces an
isomorphism `π₁(X × Y, (x, y)) ≃* π₁(X, x)`: the fundamental group of a product with a
simply connected space is that of the remaining factor. -/
@[expose] def FundamentalGroup.prodMulEquivRight [SimplyConnectedSpace Y] (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup X x :=
  haveI : Unique (FundamentalGroup Y y) := uniqueOfSubsingleton 1
  (FundamentalGroup.prodMulEquiv x y).trans MulEquiv.prodUnique

@[simp]
theorem FundamentalGroup.prodMulEquivRight_apply [SimplyConnectedSpace Y] (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquivRight x y γ =
      FundamentalGroup.map (ContinuousMap.fst : C(X × Y, X)) (x, y) γ :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquivRight_symm_apply [SimplyConnectedSpace Y] (x : X) (y : Y)
    (γ : FundamentalGroup X x) :
    (FundamentalGroup.prodMulEquivRight x y).symm γ =
      (FundamentalGroup.prodMulEquiv x y).symm (γ, 1) :=
  rfl

/-- When the first factor `X` is simply connected, the projection to `Y` induces an
isomorphism `π₁(X × Y, (x, y)) ≃* π₁(Y, y)`. -/
@[expose] def FundamentalGroup.prodMulEquivLeft [SimplyConnectedSpace X] (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup Y y :=
  haveI : Unique (FundamentalGroup X x) := uniqueOfSubsingleton 1
  (FundamentalGroup.prodMulEquiv x y).trans MulEquiv.uniqueProd

@[simp]
theorem FundamentalGroup.prodMulEquivLeft_apply [SimplyConnectedSpace X] (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    FundamentalGroup.prodMulEquivLeft x y γ =
      FundamentalGroup.map (ContinuousMap.snd : C(X × Y, Y)) (x, y) γ :=
  rfl

@[simp]
theorem FundamentalGroup.prodMulEquivLeft_symm_apply [SimplyConnectedSpace X] (x : X) (y : Y)
    (γ : FundamentalGroup Y y) :
    (FundamentalGroup.prodMulEquivLeft x y).symm γ =
      (FundamentalGroup.prodMulEquiv x y).symm (1, γ) :=
  rfl

namespace AddCircle

variable {p : ℝ}

/-- The fundamental group of a cylinder `AddCircle p × Y` over a simply connected space `Y`,
based at any point `(x, y)` with a chosen lift `e` of `x`, is infinite cyclic:
`FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ`. The isomorphism records the
integer that the circle-projected loop winds around `AddCircle p`. -/
def cylinderFundamentalGroupMulEquiv (hp : p ≠ 0) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {x : AddCircle p} (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y) :
    FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivRight x y).trans (fundamentalGroupMulEquiv p hp e)

/-- Characterization of the integer assigned by `cylinderFundamentalGroupMulEquiv`: a loop
class maps to `n` exactly when the circle-projected loop's monodromy translates the chosen
lift by `n • p`. -/
lemma cylinderFundamentalGroupMulEquiv_apply_eq_iff (hp : p ≠ 0) {Y : Type*}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y)
    (γ : FundamentalGroup (AddCircle p × Y) (x, y)) (n : Multiplicative ℤ) :
    cylinderFundamentalGroupMulEquiv hp e y γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y) γ) e :
          ℝ) = (e : ℝ) + n.toAdd • p := by
  simp only [cylinderFundamentalGroupMulEquiv, MulEquiv.trans_apply,
    FundamentalGroup.prodMulEquivRight_apply]
  exact fundamentalGroupMulEquiv_apply_eq_iff p hp e _ n

/-- The circle projection of `cylinderFundamentalGroupMulEquiv.symm n` is the circle loop
class the circle equivalence sends to `n`. -/
@[simp]
lemma cylinderFundamentalGroupMulEquiv_symm_fst (hp : p ≠ 0) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {x : AddCircle p} (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y)
    (n : Multiplicative ℤ) :
    FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y)
        ((cylinderFundamentalGroupMulEquiv hp e y).symm n) =
      (fundamentalGroupMulEquiv p hp e).symm n := by
  rw [cylinderFundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    ← FundamentalGroup.prodMulEquivRight_apply, MulEquiv.apply_symm_apply]

/-- The inverse of the cylinder equivalence has circle-projected monodromy translation
`n • p`. -/
lemma cylinderFundamentalGroupMulEquiv_symm_monodromy (hp : p ≠ 0) {Y : Type*}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y) (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy
      (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y)
        ((cylinderFundamentalGroupMulEquiv hp e y).symm n)) e : ℝ) = (e : ℝ) + n.toAdd • p := by
  rw [cylinderFundamentalGroupMulEquiv_symm_fst]
  exact fundamentalGroupMulEquiv_symm_monodromy p hp e n

/-- A cylinder loop class maps to `1` exactly when the circle-projected loop's monodromy fixes
the chosen lift. -/
lemma cylinderFundamentalGroupMulEquiv_eq_one_iff (hp : p ≠ 0) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {x : AddCircle p} (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y)
    (γ : FundamentalGroup (AddCircle p × Y) (x, y)) :
    cylinderFundamentalGroupMulEquiv hp e y γ = 1 ↔
      (AddCircle.isCoveringMap_coe p).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y) γ)
          e = e := by
  simp only [cylinderFundamentalGroupMulEquiv, MulEquiv.trans_apply,
    FundamentalGroup.prodMulEquivRight_apply]
  exact fundamentalGroupMulEquiv_eq_one_iff p hp e _

/-- The fundamental group of the standard infinite cylinder `AddCircle p × ℝ`, based at
`(0, 0)` with the lift `0 : ℝ`, is `Multiplicative ℤ`. Here the second factor `ℝ` is
contractible, hence simply connected, so the cylinder's fundamental group is that of the
circle. -/
def realCylinderFundamentalGroupMulEquiv (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p × ℝ) (0, 0) ≃* Multiplicative ℤ :=
  cylinderFundamentalGroupMulEquiv hp ⟨0, by simp⟩ 0

end AddCircle

namespace UnitAddCircle

/-- The fundamental group of the unit-circle cylinder `UnitAddCircle × ℝ = (ℝ ⧸ ℤ) × ℝ`,
based at `(0, 0)`, is `ℤ`: `FundamentalGroup (UnitAddCircle × ℝ) (0, 0) ≃* Multiplicative ℤ`. -/
def cylinderFundamentalGroupMulEquiv :
    FundamentalGroup (UnitAddCircle × ℝ) (0, 0) ≃* Multiplicative ℤ :=
  AddCircle.realCylinderFundamentalGroupMulEquiv one_ne_zero

end UnitAddCircle

end

end TauCeti
