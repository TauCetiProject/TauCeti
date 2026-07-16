/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupProduct
public import TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup

/-!
# The fundamental group of a cylinder

Combining the collapse of a simply connected product factor
(`TauCeti.FundamentalGroup.prodMulEquivOfSimplyConnectedRight`, `…Left`) with the circle
computation `π₁(AddCircle p) ≃* Multiplicative ℤ`
(`TauCeti.AddCircle.fundamentalGroupMulEquiv`) gives the fundamental group of a **cylinder**:
a product of a circle with any simply connected space. The simply connected factor does not
change `π₁`, so

  `π₁(AddCircle p × Y, (x, y)) ≃* Multiplicative ℤ`

for every nonzero real period `p` and every simply connected `Y`. The standard cylinder
`AddCircle p × ℝ` (the real line being contractible, hence simply connected) is the concrete
instance `π₁(cylinder) ≅ ℤ`; the same holds with the factors swapped.

Unlike the torus `Π i, AddCircle (p i)`
(`TauCeti.AddCircle.piFundamentalGroupMulEquiv`), whose factors are all nontrivial circles,
the cylinder mixes one nontrivial circle factor with a trivial (simply connected) one, and is
the canonical example where the product formula collapses.

## Main declarations

* `TauCeti.AddCircle.cylinderFundamentalGroupMulEquiv`:
  `π₁(AddCircle p × Y, (x, y)) ≃* Multiplicative ℤ` for simply connected `Y`.
* `TauCeti.AddCircle.cylinderFundamentalGroupMulEquiv'`:
  `π₁(Y × AddCircle p, (y, x)) ≃* Multiplicative ℤ` for simply connected `Y`.
* `TauCeti.AddCircle.realCylinderFundamentalGroupMulEquiv`:
  `π₁(AddCircle p × ℝ, (0, 0)) ≃* Multiplicative ℤ`, the standard cylinder.
* `TauCeti.AddCircle.nontrivial_fundamentalGroup_cylinder`,
  `TauCeti.AddCircle.not_simplyConnectedSpace_cylinder`: the cylinder has nontrivial
  fundamental group, hence is not simply connected.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 "applications"
(`TauCetiRoadmap/UniversalCovers/README.md`), extending the circle computation (item 12,
`π₁(S¹) ≅ ℤ`) and the torus computation (item 13, `π_n(Tᵏ)` at `n = 1`) to the fundamental
group of a cylinder. It consumes the Tau Ceti product formula
(`TauCeti.FundamentalGroup.prodMulEquiv`) and its simply connected collapse, the circle
computation, and Mathlib's contractibility of a real topological vector space
(`RealTopologicalVectorSpace.contractibleSpace`, giving `SimplyConnectedSpace ℝ`). No Mathlib
code is vendored.
-/

public section

namespace TauCeti

namespace AddCircle

noncomputable section

variable {p : ℝ} {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y]

/-- The fundamental group of the cylinder `AddCircle p × Y`, based at any point `(x, y)` with a
chosen lift `e` of `x` and a simply connected second factor `Y`, is infinite cyclic:
`FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ`, for a nonzero real period `p`.
The forward map records the winding integer of the loop's projection to the circle factor. -/
def cylinderFundamentalGroupMulEquiv (hp : p ≠ 0) {x : AddCircle p} {y : Y}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p × Y) (x, y) ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivOfSimplyConnectedRight x y).trans
    (fundamentalGroupMulEquiv p hp e)

@[simp]
theorem cylinderFundamentalGroupMulEquiv_apply (hp : p ≠ 0) {x : AddCircle p} {y : Y}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p × Y) (x, y)) :
    cylinderFundamentalGroupMulEquiv hp e γ =
      fundamentalGroupMulEquiv p hp e
        (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y) γ) := by
  simp [cylinderFundamentalGroupMulEquiv, MulEquiv.trans_apply]

/-- Characterization of the integer assigned by `cylinderFundamentalGroupMulEquiv`: a loop
class maps to `n` exactly when the monodromy of its projection to the circle translates the
chosen lift by `n • p`. -/
theorem cylinderFundamentalGroupMulEquiv_apply_eq_iff (hp : p ≠ 0) {x : AddCircle p} {y : Y}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p × Y) (x, y)) (n : Multiplicative ℤ) :
    cylinderFundamentalGroupMulEquiv hp e γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy
          (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × Y, AddCircle p)) (x, y) γ)
          e : ℝ) = (e : ℝ) + n.toAdd • p := by
  rw [cylinderFundamentalGroupMulEquiv_apply]
  exact fundamentalGroupMulEquiv_apply_eq_iff p hp e _ n

/-- The fundamental group of the cylinder `Y × AddCircle p`, based at any point `(y, x)` with a
chosen lift `e` of `x` and a simply connected first factor `Y`, is infinite cyclic:
`FundamentalGroup (Y × AddCircle p) (y, x) ≃* Multiplicative ℤ`, for a nonzero real period `p`.
This is the previous equivalence with the two factors swapped. -/
def cylinderFundamentalGroupMulEquiv' (hp : p ≠ 0) {x : AddCircle p} {y : Y}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (Y × AddCircle p) (y, x) ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivOfSimplyConnectedLeft y x).trans
    (fundamentalGroupMulEquiv p hp e)

@[simp]
theorem cylinderFundamentalGroupMulEquiv'_apply (hp : p ≠ 0) {x : AddCircle p} {y : Y}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (Y × AddCircle p) (y, x)) :
    cylinderFundamentalGroupMulEquiv' hp e γ =
      fundamentalGroupMulEquiv p hp e
        (FundamentalGroup.map (ContinuousMap.snd : C(Y × AddCircle p, AddCircle p)) (y, x) γ) := by
  simp [cylinderFundamentalGroupMulEquiv', MulEquiv.trans_apply]

end

section Real

variable (p : ℝ)

/-- The fundamental group of the standard cylinder `AddCircle p × ℝ`, based at `(0, 0)`, is
infinite cyclic: `FundamentalGroup (AddCircle p × ℝ) (0, 0) ≃* Multiplicative ℤ`, for a nonzero
real period `p`. The real line is contractible, hence simply connected, so it contributes no
loops. -/
noncomputable def realCylinderFundamentalGroupMulEquiv (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p × ℝ) (0, 0) ≃* Multiplicative ℤ :=
  cylinderFundamentalGroupMulEquiv hp ⟨0, by simp⟩

/-- The fundamental group of the standard cylinder is nontrivial. -/
theorem nontrivial_fundamentalGroup_cylinder (hp : p ≠ 0) :
    Nontrivial (FundamentalGroup (AddCircle p × ℝ) (0, 0)) :=
  (realCylinderFundamentalGroupMulEquiv p hp).toEquiv.nontrivial

/-- The standard cylinder is not simply connected: its fundamental group is nontrivial, while a
simply connected space has a subsingleton fundamental group. -/
theorem not_simplyConnectedSpace_cylinder (hp : p ≠ 0) :
    ¬ SimplyConnectedSpace (AddCircle p × ℝ) := by
  intro h
  haveI := h
  haveI := nontrivial_fundamentalGroup_cylinder p hp
  exact false_of_nontrivial_of_subsingleton (FundamentalGroup (AddCircle p × ℝ) (0, 0))

end Real

end AddCircle

end TauCeti
