/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Cyclic successor, fixed points, and semiconjugacy for periodic orbits

`Function.periodicOrbit f x` packages the forward orbit of a periodic point `x` as a duplicate-free
`Cycle α`. When periodic orbits represent oriented boundary walks or closed circuits, one needs to
step around the cycle via `Cycle.next`, recognize singleton cycles corresponding to fixed points,
and transport orbits along maps intertwining the dynamics. This file provides those cycle-level
lemmas for `Function.periodicOrbit`:

* `Function.periodicOrbit_eq_singleton_iff_isFixedPt` and `Function.IsFixedPt.periodicOrbit_eq`:
  the periodic orbit of `x` under `f` is the singleton cycle `[x]` if and only if `f x = x`.
* `Function.next_periodicOrbit`: stepping to the next element along `Function.periodicOrbit f x`
  with `Cycle.next` applies `f`.
* `Function.Semiconj.periodicOrbit_apply`: an injective map intertwining `f₁` with `f₂` transports
  periodic orbits via `Cycle.map`.
-/

public section

namespace Function

section PeriodicOrbit

variable {α : Type*} {f : α → α} {x : α}

/-- The periodic orbit of `x` under `f` equals the singleton cycle `[x]` if and only if `x` is a
fixed point of `f`. -/
@[simp]
theorem periodicOrbit_eq_singleton_iff_isFixedPt :
    periodicOrbit f x = ([x] : List α) ↔ IsFixedPt f x := by
  refine ⟨fun h ↦ minimalPeriod_eq_one_iff_isFixedPt.mp ?_, fun hx ↦ ?_⟩
  · simpa [periodicOrbit_length] using congrArg Cycle.length h
  · rw [periodicOrbit_def, minimalPeriod_eq_one_iff_isFixedPt.mpr hx]
    rfl

/-- The periodic orbit of a fixed point `x` of `f` is the singleton cycle `[x]`. -/
theorem IsFixedPt.periodicOrbit_eq (hx : IsFixedPt f x) :
    periodicOrbit f x = ([x] : List α) :=
  periodicOrbit_eq_singleton_iff_isFixedPt.mpr hx

/-- Stepping along `Function.periodicOrbit f x` via `Cycle.next` applies `f`. -/
@[simp]
theorem next_periodicOrbit [DecidableEq α] {y : α} (hy : y ∈ periodicOrbit f x) :
    (periodicOrbit f x).next nodup_periodicOrbit y hy = f y := by
  set l : List α := (List.range (minimalPeriod f x)).map fun n ↦ f^[n] x
  have hn : l.Nodup := Cycle.nodup_coe_iff.mp (nodup_periodicOrbit (f := f) (x := x))
  have hyl : y ∈ l := Cycle.mem_coe_iff.mp hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hyl
  have hnext : (periodicOrbit f x).next nodup_periodicOrbit l[i] hy =
      l[(i + 1) % l.length]'(Nat.mod_lt _ ((Nat.zero_le i).trans_lt hi)) :=
    List.next_getElem l hn i hi
  rw [hnext]
  simp only [l, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
  rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']

end PeriodicOrbit

/-- An injective map intertwining `f₁` with `f₂` transports periodic orbits of `f₁` to periodic
orbits of `f₂`. -/
theorem Semiconj.periodicOrbit_apply {α β : Type*} {g : α → β} {f₁ : α → α} {f₂ : β → β}
    (h : Semiconj g f₁ f₂) (hg : Injective g) (x : α) :
    periodicOrbit f₂ (g x) = (periodicOrbit f₁ x).map g := by
  have hiter : ∀ n, f₂^[n] (g x) = g (f₁^[n] x) := fun n ↦ (h.iterate_right n x).symm
  have hper : minimalPeriod f₂ (g x) = minimalPeriod f₁ x :=
    minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
      simp [IsPeriodicPt, IsFixedPt, hiter, hg.eq_iff]
  rw [periodicOrbit_def, periodicOrbit_def, hper, Cycle.map_coe, List.map_map]
  exact congrArg Cycle.ofList (List.map_congr_left fun n _ ↦ hiter n)

end Function
