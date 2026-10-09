/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Orbit
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The compact real Spin unit level as a Euclidean sphere

The positive-definite quadratic form defining the compact real Spin group is the squared
Euclidean norm in Euclidean coordinates. This file packages the resulting homeomorphism between
the Spin action's unit level and the standard Euclidean unit sphere. The resulting
path-connectedness theorem supplies paths between points of the unit level in dimensions at least
two.

## Main declarations

* `CliffordAlgebra.realCliffordUnitLevelAntipode` is negation on the compact unit level and is
  equivariant for the Spin action.
* `CliffordAlgebra.realCliffordUnitLevelHomeomorphSubtype` identifies the action carrier with the
  same unit level viewed as a raw quadratic-form subtype.
* `CliffordAlgebra.realCliffordUnitLevelHomeomorphSphere` identifies the unit level with the
  Euclidean unit sphere through `EuclideanSpace.equiv`.
* `CliffordAlgebra.pathConnectedSpace_realCliffordUnitLevel_add_two` transfers the standard
  path-connectedness theorem for spheres to the unit level in dimensions at least two.

-/

public section

namespace CliffordAlgebra

open Metric TauCeti

noncomputable section

/-- The antipode of a point in the compact real Clifford unit level. -/
def realCliffordUnitLevelAntipode {n : ℕ} (x : realCliffordUnitLevel n) :
    realCliffordUnitLevel n :=
  ⟨-x, by
    apply (mem_realCliffordUnitLevel n _).2
    rw [QuadraticMap.map_neg]
    exact (mem_realCliffordUnitLevel n _).1 x.2⟩

/-- The compact real Clifford unit-level antipode is negation on the underlying vector. -/
@[simp]
theorem coe_realCliffordUnitLevelAntipode {n : ℕ} (x : realCliffordUnitLevel n) :
    (realCliffordUnitLevelAntipode x : Fin n → ℝ) = -x :=
  (rfl)

/-- The compact real Clifford unit-level antipode is an involution. -/
@[simp]
theorem realCliffordUnitLevelAntipode_antipode {n : ℕ} (x : realCliffordUnitLevel n) :
    realCliffordUnitLevelAntipode (realCliffordUnitLevelAntipode x) = x := by
  apply Subtype.ext
  simp only [coe_realCliffordUnitLevelAntipode, neg_neg]

/-- A point of the compact real Clifford unit level differs from its antipode. -/
theorem ne_realCliffordUnitLevelAntipode {n : ℕ} (x : realCliffordUnitLevel n) :
    x ≠ realCliffordUnitLevelAntipode x := by
  intro h
  have hx : (x : Fin n → ℝ) = -x := congrArg Subtype.val h
  have hx0 : (x : Fin n → ℝ) = 0 := self_eq_neg.mp hx
  have hxone := (mem_realCliffordUnitLevel n _).1 x.2
  rw [hx0, map_zero] at hxone
  exact zero_ne_one hxone

/-- The compact Spin action commutes with the unit-level antipode. -/
@[simp]
theorem smul_realCliffordUnitLevelAntipode {n : ℕ} (g : realCliffordSpinGroupZero n)
    (x : realCliffordUnitLevel n) :
    g • realCliffordUnitLevelAntipode x = realCliffordUnitLevelAntipode (g • x) := by
  apply Subtype.ext
  simp only [SubMulAction.val_smul, spinGroup_smul_apply,
    coe_realCliffordUnitLevelAntipode, map_neg]

/-- The compact real Spin unit level is homeomorphic to the Euclidean unit sphere. -/
def realCliffordUnitLevelHomeomorphSphere (n : ℕ) :
    realCliffordUnitLevel n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.subtype fun v => by
    rw [mem_realCliffordUnitLevel, mem_sphere, dist_zero_right]
    constructor
    · exact norm_euclideanSpaceEquiv_symm_eq_one_of_realCliffordForm_zero_eq_one
    · intro hv
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (realCliffordForm_zero_euclideanSpaceEquiv_eq_one
          ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm v, by
            simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
              ContinuousLinearEquiv.coe_symm_toHomeomorph, mem_sphere,
              dist_zero_right] using hv⟩)

/-- The compact real Spin unit level is the raw quadratic level with its canonical action subtype
    structure forgotten. -/
def realCliffordUnitLevelHomeomorphSubtype (n : ℕ) :
    realCliffordUnitLevel n ≃ₜ {x : Fin n → ℝ // realCliffordForm n 0 x = 1} :=
  Homeomorph.ofEqSubtypes (by
    funext x
    exact propext (mem_realCliffordUnitLevel n x))

/-- The carrier homeomorphism does not change the underlying vector. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSubtype_apply (n : ℕ)
    (x : realCliffordUnitLevel n) :
    (realCliffordUnitLevelHomeomorphSubtype n x : Fin n → ℝ) = x :=
  by
    rw [realCliffordUnitLevelHomeomorphSubtype]
    rfl

/-- The inverse carrier homeomorphism does not change the underlying vector. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSubtype_symm_apply (n : ℕ)
    (x : {x : Fin n → ℝ // realCliffordForm n 0 x = 1}) :
    ((realCliffordUnitLevelHomeomorphSubtype n).symm x : Fin n → ℝ) = x :=
  by
    rw [realCliffordUnitLevelHomeomorphSubtype]
    rfl

/-- The forward map of `realCliffordUnitLevelHomeomorphSphere` is Euclidean coordinate
conversion. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSphere_apply (n : ℕ)
    (x : realCliffordUnitLevel n) :
    (realCliffordUnitLevelHomeomorphSphere n x : EuclideanSpace ℝ (Fin n)) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm x.1 :=
  (rfl)

/-- The inverse map of `realCliffordUnitLevelHomeomorphSphere` returns function coordinates. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSphere_symm_apply (n : ℕ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ((realCliffordUnitLevelHomeomorphSphere n).symm u : Fin n → ℝ) =
      EuclideanSpace.equiv (Fin n) ℝ u :=
  (rfl)

/-- The compact real Spin unit level is path-connected in dimensions at least two. -/
theorem pathConnectedSpace_realCliffordUnitLevel_add_two (n : ℕ) :
    PathConnectedSpace (realCliffordUnitLevel (n + 2)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  let _ : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 2))) zero_le_one)
  exact (realCliffordUnitLevelHomeomorphSphere (n + 2)).symm.pathConnectedSpace

end

end CliffordAlgebra
