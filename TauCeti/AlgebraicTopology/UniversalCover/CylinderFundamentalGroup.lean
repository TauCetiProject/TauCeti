/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupProduct
public import TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup

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

namespace AddCircle

variable {p : ℝ}

/-- The fundamental group of a cylinder `AddCircle p × Y` over a simply connected space `Y`,
based at any point `(x, y)` with a chosen lift `e` of `x`, is infinite cyclic:
`FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ`. The isomorphism records the
integer that the circle-projected loop winds around `AddCircle p`. -/
def cylinderFundamentalGroupMulEquiv (hp : p ≠ 0) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {x : AddCircle p} (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y) :
    FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivFst x y).trans (fundamentalGroupMulEquiv p hp e)

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
    FundamentalGroup.prodMulEquivFst_apply]
  exact fundamentalGroupMulEquiv_apply_eq_iff p hp e _ n

/-- The circle projection of `cylinderFundamentalGroupMulEquiv.symm n` is the circle loop
class the circle equivalence sends to `n`. -/
lemma cylinderFundamentalGroupMulEquiv_symm_fst (hp : p ≠ 0) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {x : AddCircle p} (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (y : Y)
    (n : Multiplicative ℤ) :
    FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y)
        ((cylinderFundamentalGroupMulEquiv hp e y).symm n) =
      (fundamentalGroupMulEquiv p hp e).symm n := by
  rw [cylinderFundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    ← FundamentalGroup.prodMulEquivFst_apply, MulEquiv.apply_symm_apply]

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
    FundamentalGroup.prodMulEquivFst_apply]
  exact fundamentalGroupMulEquiv_eq_one_iff p hp e _

/-- The fundamental group of the standard infinite cylinder `AddCircle p × ℝ`, based at
`(0, 0)` with the lift `0 : ℝ`, is `Multiplicative ℤ`. Here the second factor `ℝ` is
contractible, hence simply connected, so the cylinder's fundamental group is that of the
circle. -/
def realCylinderFundamentalGroupMulEquiv (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p × ℝ) (0, 0) ≃* Multiplicative ℤ :=
  cylinderFundamentalGroupMulEquiv hp (zeroLift p) 0

/-- Characterization of the integer assigned by the standard infinite-cylinder
specialization. -/
lemma realCylinderFundamentalGroupMulEquiv_apply_eq_iff (hp : p ≠ 0)
    (γ : FundamentalGroup (AddCircle p × ℝ) (0, 0)) (n : Multiplicative ℤ) :
    realCylinderFundamentalGroupMulEquiv hp γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × ℝ, AddCircle p)) (0, 0) γ)
          (zeroLift p) : ℝ) = n.toAdd • p := by
  rw [realCylinderFundamentalGroupMulEquiv]
  simpa using cylinderFundamentalGroupMulEquiv_apply_eq_iff hp (zeroLift p) 0 γ n

@[simp]
lemma realCylinderFundamentalGroupMulEquiv_apply (hp : p ≠ 0)
    (γ : FundamentalGroup (AddCircle p × ℝ) (0, 0)) :
    realCylinderFundamentalGroupMulEquiv hp γ =
      cylinderFundamentalGroupMulEquiv hp (zeroLift p) 0 γ := by
  apply (realCylinderFundamentalGroupMulEquiv_apply_eq_iff hp γ _).2
  simpa using (cylinderFundamentalGroupMulEquiv_apply_eq_iff hp (zeroLift p) 0 γ _).1 rfl

@[simp]
lemma realCylinderFundamentalGroupMulEquiv_symm_apply (hp : p ≠ 0) (n : Multiplicative ℤ) :
    (realCylinderFundamentalGroupMulEquiv hp).symm n =
      (cylinderFundamentalGroupMulEquiv hp (zeroLift p) 0).symm n := by
  apply (realCylinderFundamentalGroupMulEquiv hp).injective
  rw [MulEquiv.apply_symm_apply, realCylinderFundamentalGroupMulEquiv_apply,
    MulEquiv.apply_symm_apply]

/-- The inverse of the standard infinite-cylinder specialization has monodromy translation
`n • p`. -/
lemma realCylinderFundamentalGroupMulEquiv_symm_monodromy (hp : p ≠ 0)
    (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy
      (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × ℝ, AddCircle p)) (0, 0)
        ((realCylinderFundamentalGroupMulEquiv hp).symm n)) (zeroLift p) : ℝ) =
      n.toAdd • p := by
  rw [realCylinderFundamentalGroupMulEquiv]
  simpa using cylinderFundamentalGroupMulEquiv_symm_monodromy hp (zeroLift p) 0 n

/-- A loop class maps to `1` under the standard infinite-cylinder specialization exactly when
the circle-projected loop's monodromy fixes the zero lift. -/
lemma realCylinderFundamentalGroupMulEquiv_eq_one_iff (hp : p ≠ 0)
    (γ : FundamentalGroup (AddCircle p × ℝ) (0, 0)) :
    realCylinderFundamentalGroupMulEquiv hp γ = 1 ↔
      (AddCircle.isCoveringMap_coe p).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × ℝ, AddCircle p)) (0, 0) γ)
          (zeroLift p) = zeroLift p := by
  rw [realCylinderFundamentalGroupMulEquiv]
  exact cylinderFundamentalGroupMulEquiv_eq_one_iff hp (zeroLift p) 0 γ

end AddCircle

namespace UnitAddCircle

/-- The fundamental group of the unit-circle cylinder `UnitAddCircle × ℝ = (ℝ ⧸ ℤ) × ℝ`,
based at `(0, 0)`, is `ℤ`: `FundamentalGroup (UnitAddCircle × ℝ) (0, 0) ≃* Multiplicative ℤ`. -/
def cylinderFundamentalGroupMulEquiv :
    FundamentalGroup (UnitAddCircle × ℝ) (0, 0) ≃* Multiplicative ℤ :=
  AddCircle.realCylinderFundamentalGroupMulEquiv one_ne_zero

/-- Characterization of the integer assigned by the unit-circle cylinder equivalence. -/
lemma cylinderFundamentalGroupMulEquiv_apply_eq_iff
    (γ : FundamentalGroup (UnitAddCircle × ℝ) (0, 0)) (n : Multiplicative ℤ) :
    cylinderFundamentalGroupMulEquiv γ = n ↔
      ((AddCircle.isCoveringMap_coe 1).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(UnitAddCircle × ℝ, UnitAddCircle)) (0, 0)
          γ) (AddCircle.zeroLift 1) : ℝ) = n.toAdd := by
  simpa [cylinderFundamentalGroupMulEquiv] using
    AddCircle.realCylinderFundamentalGroupMulEquiv_apply_eq_iff one_ne_zero γ n

@[simp]
lemma cylinderFundamentalGroupMulEquiv_apply
    (γ : FundamentalGroup (UnitAddCircle × ℝ) (0, 0)) :
    cylinderFundamentalGroupMulEquiv γ =
      AddCircle.realCylinderFundamentalGroupMulEquiv one_ne_zero γ := by
  apply (cylinderFundamentalGroupMulEquiv_apply_eq_iff γ _).2
  simpa using
    (AddCircle.realCylinderFundamentalGroupMulEquiv_apply_eq_iff one_ne_zero γ _).1 rfl

@[simp]
lemma cylinderFundamentalGroupMulEquiv_symm_apply (n : Multiplicative ℤ) :
    cylinderFundamentalGroupMulEquiv.symm n =
      (AddCircle.realCylinderFundamentalGroupMulEquiv one_ne_zero).symm n := by
  apply cylinderFundamentalGroupMulEquiv.injective
  rw [MulEquiv.apply_symm_apply, cylinderFundamentalGroupMulEquiv_apply,
    MulEquiv.apply_symm_apply]

/-- The inverse of the unit-circle cylinder equivalence has monodromy translation by `n`. -/
lemma cylinderFundamentalGroupMulEquiv_symm_monodromy (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe 1).monodromy
      (FundamentalGroup.map (ContinuousMap.fst : C(UnitAddCircle × ℝ, UnitAddCircle)) (0, 0)
        (cylinderFundamentalGroupMulEquiv.symm n)) (AddCircle.zeroLift 1) : ℝ) = n.toAdd := by
  rw [cylinderFundamentalGroupMulEquiv]
  simpa using AddCircle.realCylinderFundamentalGroupMulEquiv_symm_monodromy one_ne_zero n

/-- A unit-circle cylinder loop class maps to `1` exactly when the circle-projected loop's
monodromy fixes the zero lift. -/
lemma cylinderFundamentalGroupMulEquiv_eq_one_iff
    (γ : FundamentalGroup (UnitAddCircle × ℝ) (0, 0)) :
    cylinderFundamentalGroupMulEquiv γ = 1 ↔
      (AddCircle.isCoveringMap_coe 1).monodromy
        (FundamentalGroup.map (ContinuousMap.fst : C(UnitAddCircle × ℝ, UnitAddCircle)) (0, 0)
          γ) (AddCircle.zeroLift 1) = AddCircle.zeroLift 1 := by
  simpa [cylinderFundamentalGroupMulEquiv] using
    AddCircle.realCylinderFundamentalGroupMulEquiv_eq_one_iff one_ne_zero γ

end UnitAddCircle

end

end TauCeti
