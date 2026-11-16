/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal shifted `q`-Pochhammer power series

`TauCeti.qPochhammerSeries N c x` is the formal product `∏_{n ≥ 0} (1 - x X^{N n + c})` in `R⟦X⟧`,
with `m`-th coefficient taken from the partial product over `n < m` (`coeff_qPochhammerSeries`,
`constantCoeff_qPochhammerSeries`, `map_qPochhammerSeries`, `qPochhammerSeries_zero_right`). For
`0 < N` and `0 < c`, the partial products stabilize (`coeff_qPochhammerSeries_eq_coeff_prod_range`)
and satisfy `qPochhammerSeries_eq_one_sub_mul` and `qPochhammerSeries_eq_prod_range_mul`.
-/

public noncomputable section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The formal shifted `q`-Pochhammer power series `∏_{n ≥ 0} (1 - x X^{N n + c})` over a
commutative ring `R`, defined so that its `m`-th coefficient is that of the partial product over
`n < m`. For `0 < N` and `0 < c`, the partial products stabilize in each degree. -/
def qPochhammerSeries (N c : ℕ) (x : R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m
    (∏ n ∈ Finset.range m, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c)))

/-- The `m`-th coefficient of `qPochhammerSeries N c x` is that of the partial product over
`n < m`. -/
theorem coeff_qPochhammerSeries (N c : ℕ) (x : R) (m : ℕ) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range m, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) :=
  PowerSeries.coeff_mk m _

/-- The constant coefficient of `qPochhammerSeries N c x` is `1`. -/
@[simp]
theorem constantCoeff_qPochhammerSeries (N c : ℕ) (x : R) :
    PowerSeries.constantCoeff (qPochhammerSeries N c x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_qPochhammerSeries]; simp

/-- Mapping coefficients along a ring homomorphism commutes with `qPochhammerSeries`. -/
@[simp]
theorem map_qPochhammerSeries (f : R →+* S) (N c : ℕ) (x : R) :
    (qPochhammerSeries N c x).map f = qPochhammerSeries N c (f x) := by
  ext m
  rw [PowerSeries.coeff_map, coeff_qPochhammerSeries, coeff_qPochhammerSeries,
    ← PowerSeries.coeff_map]; simp

/-- At `x = 0`, `qPochhammerSeries N c 0 = 1`. -/
@[simp]
theorem qPochhammerSeries_zero_right (N c : ℕ) : qPochhammerSeries N c (0 : R) = 1 := by
  ext m; simp [coeff_qPochhammerSeries]

/-- For `0 < N` and `0 < c`, the `m`-th coefficient of `qPochhammerSeries N c x` agrees with that
of the partial product of any length `K ≥ m`. -/
theorem coeff_qPochhammerSeries_eq_coeff_prod_range {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (x : R)
    {m K : ℕ} (hmK : m ≤ K) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range K, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK
  induction d with
  | zero => rw [add_zero, coeff_qPochhammerSeries]
  | succ d ih =>
    rw [← add_assoc, Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      ← ih (Nat.le_add_right m d), mul_comm _ (PowerSeries.C x * _), mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp [(by have := Nat.mul_le_mul hN (Nat.le_add_right m d); omega : m < N * (m + d) + c).not_ge]

/-- **Shift recurrence for `qPochhammerSeries`.** For `0 < N` and `0 < c`, splitting off the `n = 0`
factor gives `qPochhammerSeries N c x = (1 - C x * X ^ c) * qPochhammerSeries N (N + c) x`. -/
theorem qPochhammerSeries_eq_one_sub_mul {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (x : R) :
    qPochhammerSeries N c x =
      (1 - PowerSeries.C x * PowerSeries.X ^ c) * qPochhammerSeries N (N + c) x := by
  ext m
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN hc x (Nat.le_succ m),
    Finset.prod_range_succ', mul_zero, zero_add, mul_comm, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp only [show ∀ n, N * (n + 1) + c = N * n + (N + c) from fun _ ↦ by ring]
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN (by omega) x
    (by have := Finset.mem_antidiagonal.mp hp; omega : p.2 ≤ m)]

/-- Splitting off the first `k` factors of `qPochhammerSeries N c x` for `0 < N` and `0 < c`. -/
theorem qPochhammerSeries_eq_prod_range_mul {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (k : ℕ) (x : R) :
    qPochhammerSeries N c x =
      (∏ n ∈ Finset.range k, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) *
        qPochhammerSeries N (N * k + c) x := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [qPochhammerSeries_eq_one_sub_mul hN hc x, ih (by omega),
      Finset.prod_range_succ', mul_zero, zero_add]
    simp only [show ∀ n, N * n + (N + c) = N * (n + 1) + c from fun _ ↦ by ring]; ring

end TauCeti
