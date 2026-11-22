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

* `TauCeti.UnitAddTorus.surjective_coe`: every point of the torus comes from a point of `d → ℝ`.
* `TauCeti.UnitAddTorus.isOpenQuotientMap_coe`: the map `d → ℝ → UnitAddTorus d` is an open
  quotient map.
* `TauCeti.UnitAddTorus.coe_eq_coe_iff`: two points have the same image exactly when they differ by
  an integer vector.
* `TauCeti.UnitAddTorus.periodic_comp_coe`: the lift of a function on the torus is `ℤ^d`-periodic.
* `TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq`: a continuous `ℤ^d`-periodic function on
  `d → ℝ` descends to a continuous function on the torus.
* `TauCeti.UnitAddTorus.pairing`, `TauCeti.UnitAddTorus.continuous_pairing`: the biadditive
  integer pairing `(k, α) ↦ ∑ i, k i • α i` and its continuity in `α`.
* `TauCeti.UnitAddTorus.exists_addOrderOf_eq_zero_of_forall_pairing`: non-annihilation of a finite
  family of torus points implies existence of an infinite-order pairing for every nonzero frequency.
* `TauCeti.TorusIrrational`: irrationality on `UnitAddTorus d` via non-annihilation by nonzero
  integer frequency vectors, with singleton, empty-type, and nonzero-scaling characterizations.
-/

public section

namespace TauCeti

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

section Pairing

variable [Fintype d]

/-- The integer pairing `(k, α) ↦ ∑ i, k i • α i` between frequency vectors `k : d → ℤ` and
torus points `α : UnitAddTorus d`, packaged as a biadditive map. -/
def pairing : (d → ℤ) →+ UnitAddTorus d →+ UnitAddCircle where
  toFun k :=
    { toFun := fun α ↦ ∑ i, k i • α i
      map_zero' := by simp
      map_add' := fun α β ↦ by simp [smul_add, Finset.sum_add_distrib] }
  map_zero' := by ext α; simp
  map_add' k l := by ext α; simp [add_zsmul, Finset.sum_add_distrib]

/-- Evaluating the biadditive integer pairing `pairing k α` gives `∑ i, k i • α i`. -/
@[simp] theorem pairing_apply (k : d → ℤ) (α : UnitAddTorus d) :
    pairing k α = ∑ i, k i • α i := (rfl)

/-- For each fixed integer frequency vector `k`, the pairing `α ↦ pairing k α` is continuous on
`UnitAddTorus d`. -/
@[continuity, fun_prop] theorem continuous_pairing (k : d → ℤ) : Continuous (pairing k) := by
  have h : (pairing k : UnitAddTorus d → UnitAddCircle) = fun α ↦ ∑ i, k i • α i :=
    funext (pairing_apply k)
  rw [h]; fun_prop

/-- If no nonzero integer frequency annihilates all points of a finite family `α` over `S`, then
every nonzero frequency produces an infinite-order pairing at some `j ∈ S`. -/
theorem exists_addOrderOf_eq_zero_of_forall_pairing {ι : Type*} (S : Finset ι)
    (α : ι → UnitAddTorus d) (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ S, ∑ i, k i • α j i ≠ 0) :
    ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ S, addOrderOf (∑ i, k i • α j i) = 0 := by
  intro k hk; by_contra hfin; push Not at hfin
  have hpi : IsOfFinAddOrder (fun j : S ↦ ∑ i, k i • α j.val i) :=
    IsOfFinAddOrder.pi fun j ↦ addOrderOf_pos_iff.mp (Nat.pos_of_ne_zero (hfin j.val j.property))
  obtain ⟨M, hMpos, hM⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hpi
  obtain ⟨j, hj, hne⟩ := h ((M : ℤ) • k) (smul_ne_zero (Int.natCast_ne_zero.mpr hMpos.ne') hk)
  refine hne ?_
  rw [← pairing_apply, map_zsmul, AddMonoidHom.zsmul_apply, pairing_apply, natCast_zsmul]
  exact congrFun hM ⟨j, hj⟩

end Pairing

end UnitAddTorus

section TorusIrrational

variable {d : Type*} [Fintype d]

/-- A point `α : UnitAddTorus d` is irrational if no nonzero integer frequency vector annihilates
it under the pairing `k ↦ ∑ i, k i • α i`. -/
def TorusIrrational (α : UnitAddTorus d) : Prop := ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0

/-- Unfolding characterization of `TorusIrrational`. -/
theorem torusIrrational_def {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0 := Iff.rfl

/-- On a one-dimensional torus, `TorusIrrational` coincides with having infinite additive order. -/
theorem torusIrrational_unique_iff [Unique d] {α : UnitAddTorus d} :
    TorusIrrational α ↔ addOrderOf (α default) = 0 := by
  rw [torusIrrational_def, addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_zsmul_eq_zero]
  simp only [Fintype.sum_unique, not_exists, not_and]
  refine ⟨fun h n hn ↦ h (fun _ ↦ n) (fun hk ↦ hn (congrFun hk default)),
    fun h k hk ↦ h (k default) (fun h0 ↦ hk (funext fun i ↦ Unique.eq_default i ▸ h0))⟩

/-- On an empty coordinate type, every torus point is vacuously irrational. -/
theorem torusIrrational_of_isEmpty [IsEmpty d] (α : UnitAddTorus d) : TorusIrrational α :=
  fun k hk ↦ (hk (Subsingleton.elim k 0)).elim

/-- Scaling a torus point by a nonzero integer preserves and reflects irrationality. -/
@[simp] theorem torusIrrational_zsmul_iff {α : UnitAddTorus d} {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  refine ⟨fun h k hk hsum ↦ h k hk ?_, fun h k hk hsum ↦ h (m • k) (smul_ne_zero hm hk) ?_⟩
  · rw [← UnitAddTorus.pairing_apply, map_zsmul, UnitAddTorus.pairing_apply, hsum, smul_zero]
  · rw [← UnitAddTorus.pairing_apply, map_zsmul, AddMonoidHom.zsmul_apply, ← map_zsmul,
      UnitAddTorus.pairing_apply]; exact hsum

/-- A nonzero integer multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.zsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) := (torusIrrational_zsmul_iff hm).mpr hα

/-- Scaling a torus point by a nonzero natural number preserves and reflects irrationality. -/
@[simp] theorem torusIrrational_nsmul_iff {α : UnitAddTorus d} {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  simpa [natCast_zsmul] using
    torusIrrational_zsmul_iff (α := α) (m := (m : ℤ)) (Int.natCast_ne_zero.mpr hm)

/-- A nonzero natural-number multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.nsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) := (torusIrrational_nsmul_iff hm).mpr hα

end TorusIrrational

end TauCeti
