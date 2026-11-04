/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Instances.AddCircle.Real

import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The quotient map from `d → ℝ` onto the unit torus

The unit torus `UnitAddTorus d = (ℝ / ℤ)^d` is the image of `d → ℝ` under the map
`x ↦ fun i ↦ (x i : UnitAddCircle)` reducing each coordinate modulo one. This file records that
this map is a surjective open quotient map whose fibres are the cosets of the integer vectors, so
that functions on the torus are the same as `ℤ^d`-periodic functions on `d → ℝ`, and continuous
functions on the torus are the same as continuous `ℤ^d`-periodic functions on `d → ℝ`.

## Main results

* `UnitAddTorus.surjective_coe`: every point of the torus comes from a point of `d → ℝ`.
* `UnitAddTorus.isOpenQuotientMap_coe`: the map `d → ℝ → UnitAddTorus d` is an open quotient
  map.
* `UnitAddTorus.coe_eq_coe_iff`: two points have the same image exactly when they differ by an
  integer vector.
* `UnitAddTorus.periodic_comp_coe`: the lift of a function on the torus is `ℤ^d`-periodic.
* `UnitAddTorus.exists_continuous_comp_coe_eq`: a continuous `ℤ^d`-periodic function on `d → ℝ`
  descends to a continuous function on the torus.
-/

public section

namespace UnitAddTorus

variable {d : Type*}

/-- Every point of the torus is the image of a point of `d → ℝ`. -/
theorem surjective_coe :
    Function.Surjective fun x : d → ℝ ↦ fun i ↦ (x i : UnitAddCircle) := fun z ↦
  ⟨fun i ↦ (z i).out, by ext i; simp⟩

/-- Reducing each coordinate modulo one is an open quotient map from `d → ℝ` onto the torus. -/
theorem isOpenQuotientMap_coe :
    IsOpenQuotientMap fun x : d → ℝ ↦ fun i ↦ (x i : UnitAddCircle) :=
  IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

/-- Two points of `d → ℝ` have the same image on the torus exactly when they differ by an integer
vector. -/
theorem coe_eq_coe_iff {x y : d → ℝ} :
    ((fun i ↦ (x i : UnitAddCircle)) : UnitAddTorus d) = (fun i ↦ (y i : UnitAddCircle)) ↔
      ∃ m : d → ℤ, y = x + fun i ↦ (m i : ℝ) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose m hm using fun i ↦ AddSubgroup.mem_zmultiples_iff.1
      (QuotientAddGroup.eq_iff_sub_mem.1 (congr_fun h i).symm)
    refine ⟨m, funext fun i ↦ ?_⟩
    simp only [Pi.add_apply]
    have := hm i
    simp only [zsmul_eq_mul, mul_one] at this
    linarith
  · rintro ⟨m, rfl⟩
    ext i
    simp

/-- The lift `x ↦ f (fun i ↦ (x i : UnitAddCircle))` of a function on the torus is periodic with
every integer vector as a period. -/
theorem periodic_comp_coe {X : Type*} (f : UnitAddTorus d → X) (m : d → ℤ) :
    Function.Periodic (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) fun i ↦ (m i : ℝ) :=
  fun _ ↦ congrArg f (coe_eq_coe_iff.2 ⟨m, rfl⟩).symm

/-- A continuous function on `d → ℝ` with every integer vector as a period descends to a
continuous function on the torus. -/
theorem exists_continuous_comp_coe_eq {X : Type*} [TopologicalSpace X] {G : (d → ℝ) → X}
    (hG : Continuous G) (hper : ∀ m : d → ℤ, Function.Periodic G fun i ↦ (m i : ℝ)) :
    ∃ g : UnitAddTorus d → X, Continuous g ∧ ∀ x, g (fun i ↦ (x i : UnitAddCircle)) = G x := by
  have hq := (isOpenQuotientMap_coe (d := d)).isQuotientMap
  have hfac : Function.FactorsThrough G fun x : d → ℝ ↦ fun i ↦ (x i : UnitAddCircle) :=
    fun x y h ↦ by
      obtain ⟨m, rfl⟩ := coe_eq_coe_iff.1 h
      exact (hper m x).symm
  refine ⟨hq.lift (f := ⟨_, hq.continuous⟩) ⟨G, hG⟩ hfac, ContinuousMap.continuous _,
    fun x ↦ ?_⟩
  exact DFunLike.congr_fun (hq.lift_comp (f := ⟨_, hq.continuous⟩) ⟨G, hG⟩ hfac) x

end UnitAddTorus
