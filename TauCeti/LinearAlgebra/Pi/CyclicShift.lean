/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Abel

/-!
# Cyclic shifts with a wraparound scalar on finite tuples

For a map `φ : M → M` and a scalar `c : R`, `TauCeti.cyclicShift φ c` acts on `Fin r → M` by
applying `φ` coordinatewise, rotating indices by `finRotate r`, and scaling coordinate `0` by `c`.
When `φ` is semilinear over a ring endomorphism `σ : R →+* R` fixing `c`, the `k`-th iterate
(`TauCeti.cyclicShift_iterate_apply`) and the full-cycle `r`-th iterate
(`TauCeti.cyclicShift_iterate_rank_apply`) simplify to `c • φ^[r]` on each coordinate.

## Main definitions

* `TauCeti.cyclicShift φ c`: coordinatewise `φ` composed with cyclic rotation and scaling of
  coordinate `0` by `c`.

## Main results

* `TauCeti.cyclicShift_apply`: coordinate formula for `TauCeti.cyclicShift`.
* `TauCeti.cyclicShift_iterate_apply`: coordinate formula for the `k`-th iterate of
  `TauCeti.cyclicShift`.
* `TauCeti.cyclicShift_iterate_rank_apply`: after a full cycle of length `r`,
  `(TauCeti.cyclicShift φ c)^[r] x i = c • φ^[r] (x i)`.
-/

public section

open Finset Function

namespace TauCeti

open Fin.NatCast

/-- Cyclic shift on `Fin r → M` applying `φ` coordinatewise and scaling coordinate `0` by `c`. -/
def cyclicShift {R M : Type*} [SMul R M] [One R] {r : ℕ}
    (φ : M → M) (c : R) (x : Fin r → M) (i : Fin r) : M :=
  (if (i : ℕ) = 0 then c else 1) • φ (x ((finRotate r).symm i))

/-- Coordinate formula for `TauCeti.cyclicShift`. -/
@[simp]
theorem cyclicShift_apply {R M : Type*} [SMul R M] [One R] {r : ℕ}
    (φ : M → M) (c : R) (x : Fin r → M) (i : Fin r) :
    cyclicShift φ c x i = (if (i : ℕ) = 0 then c else 1) • φ (x ((finRotate r).symm i)) := by
  rfl

/-- The `k`-th iterate of a cyclic shift with wraparound scalar `c` and coordinate map `φ`
satisfying `φ (a • m) = σ a • φ m` and `σ c = c`. -/
theorem cyclicShift_iterate_apply {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {σ : R →+* R} (φ : M → M) (hφ_smul : ∀ (a : R) (m : M), φ (a • m) = σ a • φ m)
    (c : R) (hφc : σ c = c) {r : ℕ} [NeZero r] (k : ℕ) (x : Fin r → M) (i : Fin r) :
    (cyclicShift φ c)^[k] x i =
      (∏ t ∈ range k, if ((i - (t : Fin r) : Fin r) : ℕ) = 0 then c else 1) •
        φ^[k] (x (i - (k : Fin r))) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hσw (j : Fin r) :
        σ (if (j : ℕ) = 0 then c else 1) = if (j : ℕ) = 0 then c else 1 := by
      split_ifs <;> simp [hφc]
    have hidx (t : ℕ) : i - 1 - (t : Fin r) = i - ((t + 1 : ℕ) : Fin r) := by
      push_cast
      abel
    rw [iterate_succ_apply', cyclicShift_apply, finRotate_symm_apply, ih, hφ_smul, map_prod,
      prod_range_succ', ← iterate_succ_apply' φ, ← smul_assoc, smul_eq_mul, mul_comm]
    simp only [hσw, hidx, Nat.cast_zero, sub_zero]

/-- After a full cycle of length `r`, a cyclic shift with wraparound scalar `c` and coordinate map
`φ` acts as `c • φ^[r]` on each coordinate. -/
theorem cyclicShift_iterate_rank_apply {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {σ : R →+* R} (φ : M → M)
    (hφ_smul : ∀ (a : R) (m : M), φ (a • m) = σ a • φ m)
    (c : R) (hφc : σ c = c) {r : ℕ} (x : Fin r → M) (i : Fin r) :
    (cyclicShift φ c)^[r] x i = c • φ^[r] (x i) := by
  have := i.neZero
  rw [cyclicShift_iterate_apply φ hφ_smul c hφc, Fin.natCast_self, sub_zero,
    prod_eq_single (i : ℕ)]
  · simp
  · intro t ht hti
    rw [ite_eq_right_iff]
    intro h
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h
    exact (hti (by rw [h, Fin.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ht)])).elim
  · simp

end TauCeti
