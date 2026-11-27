/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Fixed points of the iterates of a map, sorted by periodic orbit

Let `f : α → α` and let `x i` be points of least periods `d i > 0`, one on each periodic orbit of
`f`. The pairs `(n, y)` with `n > 0` and `f^[n] y = y` are then the pairs
`(d i * (k + 1), f^[j] (x i))` with `k : ℕ` and `j < d i`, each exactly once
(`Function.periodicPairEquiv`). Indeed the least period of a point `y` on the orbit of `x i` is
`d i`, which divides every period of `y`, and the points `f^[j] (x i)`, `j < d i`, are distinct.
Such a choice of representatives is automatically injective
(`Function.injective_of_existsUnique_iterate`), and one always exists: choosing a point on each
periodic orbit `Function.periodicOrbit f y` gives one
(`Function.exists_forall_mem_periodicPts_and_existsUnique_iterate`).

This is the reindexing by which a sum over the fixed points of the iterates of `f`, such as the
fixed-point form of a zeta function, becomes a sum over periodic orbits and their iterates.
-/

public section

universe u

namespace Function

variable {α : Type u} {ι : Type*} {f : α → α} {x : ι → α} {d : ι → ℕ}

/-- If the `x i` are periodic points of `f` and every periodic point lies on the orbit of exactly
one `x i`, then the `x i` are pairwise distinct. -/
theorem injective_of_existsUnique_iterate (hper : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) : Injective x :=
  fun i _ h ↦ (hrep _ (hper i)).unique ⟨0, rfl⟩ ⟨0, h.symm⟩

/-- **The fixed points of the iterates, sorted by orbit.** If `x i` has least period `d i > 0` and
every periodic point of `f` lies on the orbit of exactly one `x i`, then
`(i, k, j) ↦ (d i * (k + 1), f^[j] (x i))`, `j < d i`, is an equivalence onto the pairs `(n, y)`
with `n > 0` and `f^[n] y = y`. -/
noncomputable def periodicPairEquiv (hmin : ∀ i, minimalPeriod f (x i) = d i)
    (hd : ∀ i, 0 < d i) (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) :
    ((p : ι × ℕ) × Fin (d p.1)) ≃ {q : ℕ × α // 0 < q.1 ∧ IsPeriodicPt f q.1 q.2} :=
  Equiv.ofBijective (fun q ↦ ⟨(d q.1.1 * (q.1.2 + 1), f^[q.2] (x q.1.1)),
      Nat.mul_pos (hd q.1.1) q.1.2.succ_pos,
      (((hmin q.1.1).symm ▸ isPeriodicPt_minimalPeriod f _ :
        IsPeriodicPt f (d q.1.1) (x q.1.1)).mul_const _).apply_iterate _⟩) <| by
    have hxd (i : ι) : IsPeriodicPt f (d i) (x i) := hmin i ▸ isPeriodicPt_minimalPeriod f (x i)
    have hper (i : ι) : x i ∈ periodicPts f := mk_mem_periodicPts (hd i) (hxd i)
    constructor
    · rintro ⟨⟨i, k⟩, j⟩ ⟨⟨i', k'⟩, j'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨hn, hy⟩ := h
      -- The common point lies on the orbits of `x i` and of `x i'`, so `i = i'`.
      have hii : i = i' := (hrep _ (mk_mem_periodicPts (hd i) ((hxd i).apply_iterate j))).unique
        ⟨j, rfl⟩ ⟨j', hy.symm⟩
      subst hii
      have hkk : k = k' := by
        have := Nat.eq_of_mul_eq_mul_left (hd i) hn
        omega
      subst hkk
      -- Distinct iterates below the least period give distinct points.
      have hj : (j : ℕ) < minimalPeriod f (x i) := by rw [hmin]; exact j.isLt
      have hj' : (j' : ℕ) < minimalPeriod f (x i) := by rw [hmin]; exact j'.isLt
      have hjj : (j : ℕ) = j' := iterate_injOn_Iio_minimalPeriod hj hj' hy
      rw [Fin.ext hjj]
    · rintro ⟨⟨n, y⟩, hn, hy⟩
      obtain ⟨i, ⟨j, hj⟩, -⟩ := hrep y (mk_mem_periodicPts hn hy)
      -- The least period of `y` is `d i`, which divides `n`.
      have hmy : minimalPeriod f y = d i := by
        rw [← hj, minimalPeriod_apply_iterate (hper i), hmin]
      obtain ⟨m, rfl⟩ : d i ∣ n := hmy ▸ hy.minimalPeriod_dvd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      refine ⟨⟨(i, m - 1), ⟨j % d i, Nat.mod_lt _ (hd i)⟩⟩, ?_⟩
      simp only [Subtype.mk.injEq, Prod.mk.injEq]
      refine ⟨by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)], ?_⟩
      rw [← hj, ← hmin i, iterate_mod_minimalPeriod_eq]

/-- The pair `(n, y)` that `Function.periodicPairEquiv` assigns to `(i, k, j)` is
`(d i * (k + 1), f^[j] (x i))`. -/
@[simp]
theorem coe_periodicPairEquiv_apply (hmin : ∀ i, minimalPeriod f (x i) = d i)
    (hd : ∀ i, 0 < d i) (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y)
    (q : (p : ι × ℕ) × Fin (d p.1)) :
    (periodicPairEquiv hmin hd hrep q : ℕ × α) = (d q.1.1 * (q.1.2 + 1), f^[q.2] (x q.1.1)) :=
  (rfl)

variable (f) in
/-- **Representatives of the periodic orbits.** Every map `f : α → α` has a family of periodic
points `x i`, one on each periodic orbit: every periodic point of `f` lies on the orbit of exactly
one `x i`. The index type is the set of periodic orbits `Function.periodicOrbit f y` of the
periodic points `y`, and `x i` is a point of the orbit `i`. Their least periods
`minimalPeriod f (x i)` are then positive. -/
theorem exists_forall_mem_periodicPts_and_existsUnique_iterate :
    ∃ (ι : Type u) (x : ι → α), (∀ i, x i ∈ periodicPts f) ∧
      ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y := by
  let ι := {c : Cycle α // ∃ y ∈ periodicPts f, periodicOrbit f y = c}
  choose x hx horb using fun i : ι ↦ i.property
  refine ⟨ι, x, hx, fun y hy ↦ ⟨⟨periodicOrbit f y, y, hy, rfl⟩, ?_, ?_⟩⟩
  · -- `y` lies on its own orbit, which is the orbit of the chosen point.
    refine (mem_periodicOrbit_iff (hx _)).1 ?_
    rw [horb]
    exact self_mem_periodicOrbit hy
  · -- An orbit through `y` is the orbit of `y`.
    rintro i ⟨j, rfl⟩
    exact Subtype.ext ((periodicOrbit_apply_iterate_eq (hx i) j).trans (horb i)).symm

end Function
