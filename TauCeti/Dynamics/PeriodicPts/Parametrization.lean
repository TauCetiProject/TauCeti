/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Parametrizing periodic points by orbit representatives

Let `f : α → α` be a map, and let `x : ι → α` list one point on each periodic orbit of `f`: every
periodic point is `f^[j] (x i)` for exactly one `i`. The `i`-th orbit has least period
`d i = minimalPeriod f (x i)`. The pairs `(n, y)` of a positive period `n` and a point `y` with
`f^[n] y = y` are then parametrized by triples `(i, k, j)` with `j < d i`, via

`(i, k, j) ↦ ((k + 1) d i, f^[j] (x i))`

(`Function.periodicPtsParam`, `Function.bijective_periodicPtsParam`). Indeed `y` lies on exactly
one orbit `i`, at exactly one position `j < d i`, and its periods are the positive multiples of
`d i`. This reindexing turns sums over the periodic points with a chosen period into sums over
the primitive orbits, their iterates and the points of each orbit.

## Main definitions

* `Function.periodicPtsParam`: the map `(i, k, j) ↦ ((k + 1) d i, f^[j] (x i))`, `j < d i`.

## Main results

* `Function.bijective_periodicPtsParam`: when `x` lists one point on each periodic orbit, this
  map is a bijection onto the periodic points with a chosen positive period.
-/

public section

namespace Function

variable {α ι : Type*} {f : α → α} {x : ι → α}

/-- The point `f^[j] (x i)` has the positive period `(k + 1) d i`, where `d i` is the least period
of `x i`. -/
theorem isPeriodicPt_succ_mul_minimalPeriod_iterate (hx : ∀ i, x i ∈ periodicPts f) (i : ι)
    (k j : ℕ) :
    0 < (k + 1) * minimalPeriod f (x i) ∧
      IsPeriodicPt f ((k + 1) * minimalPeriod f (x i)) (f^[j] (x i)) :=
  ⟨Nat.mul_pos k.succ_pos (minimalPeriod_pos_of_mem_periodicPts (hx i)),
    ((isPeriodicPt_minimalPeriod f (x i)).apply_iterate j).const_mul (k + 1)⟩

/-- The parametrization `(i, k, j) ↦ ((k + 1) d i, f^[j] (x i))`, `j < d i`, of the periodic
points with a chosen positive period, where `d i` is the least period of `x i`. -/
noncomputable def periodicPtsParam (hx : ∀ i, x i ∈ periodicPts f) :
    {q : (ι × ℕ) × ℕ // q.2 < minimalPeriod f (x q.1.1)} →
      {p : ℕ × α // 0 < p.1 ∧ IsPeriodicPt f p.1 p.2} := fun q ↦
  ⟨((q.1.1.2 + 1) * minimalPeriod f (x q.1.1.1), f^[q.1.2] (x q.1.1.1)),
    isPeriodicPt_succ_mul_minimalPeriod_iterate hx _ _ _⟩

/-- The periodic point `f^[j] (x i)` with period `(k + 1) d i` parametrized by `(i, k, j)`. -/
@[simp]
theorem coe_periodicPtsParam (hx : ∀ i, x i ∈ periodicPts f)
    (q : {q : (ι × ℕ) × ℕ // q.2 < minimalPeriod f (x q.1.1)}) :
    (periodicPtsParam hx q : ℕ × α) =
      ((q.1.1.2 + 1) * minimalPeriod f (x q.1.1.1), f^[q.1.2] (x q.1.1.1)) := by
  rw [periodicPtsParam]

/-- When `x` lists one point on each periodic orbit, every periodic point with a chosen positive
period is parametrized exactly once. -/
theorem bijective_periodicPtsParam (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) :
    Bijective (periodicPtsParam hx) := by
  constructor
  · rintro ⟨⟨⟨i, k⟩, j⟩, hj⟩ ⟨⟨⟨i', k'⟩, j'⟩, hj'⟩ h
    have h := congrArg Subtype.val h
    simp only [coe_periodicPtsParam, Prod.mk.injEq] at h
    obtain ⟨hn, hy⟩ := h
    have hper : f^[j] (x i) ∈ periodicPts f :=
      mk_mem_periodicPts (isPeriodicPt_succ_mul_minimalPeriod_iterate hx i k j).1
        (isPeriodicPt_succ_mul_minimalPeriod_iterate hx i k j).2
    -- The two points lie on the same orbit, at the same position, with the same period.
    obtain rfl : i = i' := (hrep _ hper).unique ⟨j, rfl⟩ ⟨j', hy.symm⟩
    obtain rfl : j = j' := iterate_injOn_Iio_minimalPeriod hj hj' hy
    obtain rfl : k = k' := by
      have := Nat.eq_of_mul_eq_mul_right (minimalPeriod_pos_of_mem_periodicPts (hx i)) hn
      omega
    rfl
  · rintro ⟨⟨n, y⟩, hn, hy⟩
    simp only at hn hy
    obtain ⟨i, ⟨j, hj⟩, -⟩ := hrep y (mk_mem_periodicPts hn hy)
    have hd : minimalPeriod f y = minimalPeriod f (x i) := by
      rw [← hj, minimalPeriod_apply_iterate (hx i)]
    -- The period `n` is a multiple `m d i` of the least period, with `m ≥ 1`.
    obtain ⟨m, rfl⟩ := hy.minimalPeriod_dvd
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    refine ⟨⟨⟨⟨i, m - 1⟩, j % minimalPeriod f (x i)⟩,
      Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts (hx i))⟩, Subtype.ext ?_⟩
    simp only [coe_periodicPtsParam, Prod.mk.injEq]
    exact ⟨by rw [hd, Nat.sub_add_cancel hm, mul_comm], by rw [iterate_mod_minimalPeriod_eq, hj]⟩

end Function
