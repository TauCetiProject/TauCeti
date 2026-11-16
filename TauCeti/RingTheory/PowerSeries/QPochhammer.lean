/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal shifted `q`-Pochhammer power series

For natural numbers `N` and `c` and a scalar `x` in a commutative ring `R`, the formal shifted
`q`-Pochhammer series `TauCeti.qPochhammerSeries N c x` represents the infinite product
`∏_{n ≥ 0} (1 - x X^{N n + c})` in `R⟦X⟧`.

When `0 < N` and `0 < c`, the factor `1 - x X^{N n + c}` has degree `N n + c > m` once `n ≥ m`, so
the `m`-th coefficient stabilizes at the finite partial product over `n < m`. This gives a
ring-homomorphism-compatible formal power series over any commutative ring `R` satisfying the shift
recurrence `qPochhammerSeries N c x = (1 - C x * X ^ c) * qPochhammerSeries N (N + c) x`.

## Main results

* `TauCeti.qPochhammerSeries`: the formal power series `∏_{n ≥ 0} (1 - x X^{N n + c})`.
* `TauCeti.coeff_qPochhammerSeries`: the defining coefficient formula.
* `TauCeti.constantCoeff_qPochhammerSeries`: the constant coefficient is `1`.
* `TauCeti.map_qPochhammerSeries`: compatibility with ring homomorphisms.
* `TauCeti.qPochhammerSeries_zero_right`: at `x = 0`, the series is `1`.
* `TauCeti.coeff_qPochhammerSeries_eq_coeff_prod_range`: for `0 < N` and `0 < c`, the `m`-th
  coefficient agrees with that of any partial product of length `K ≥ m`.
* `TauCeti.qPochhammerSeries_eq_one_sub_mul` and `TauCeti.qPochhammerSeries_eq_prod_range_mul`:
  the shift recurrence and splitting off the first `k` factors for `0 < N` and `0 < c`.
-/

public noncomputable section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The formal shifted `q`-Pochhammer power series `∏_{n ≥ 0} (1 - x X^{N n + c})` over a
commutative ring `R`, defined so that its `m`-th coefficient is that of the partial product over
`n < m`. For `0 < N` and `0 < c`, the partial products stabilize in each degree and satisfy the
infinite-product recurrences. -/
def qPochhammerSeries (N c : ℕ) (x : R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m
    (∏ n ∈ Finset.range m, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c)))

/-- The `m`-th coefficient of `qPochhammerSeries N c x` is the `m`-th coefficient of the partial
product over `n < m`. -/
theorem coeff_qPochhammerSeries (N c : ℕ) (x : R) (m : ℕ) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range m, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) :=
  PowerSeries.coeff_mk m _

/-- The constant coefficient of `qPochhammerSeries N c x` is `1`. -/
@[simp]
theorem constantCoeff_qPochhammerSeries (N c : ℕ) (x : R) :
    PowerSeries.constantCoeff (qPochhammerSeries N c x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_qPochhammerSeries]
  simp

/-- Mapping coefficients along a ring homomorphism commutes with `qPochhammerSeries`. -/
@[simp]
theorem map_qPochhammerSeries (f : R →+* S) (N c : ℕ) (x : R) :
    (qPochhammerSeries N c x).map f = qPochhammerSeries N c (f x) := by
  ext m
  rw [PowerSeries.coeff_map, coeff_qPochhammerSeries, coeff_qPochhammerSeries,
    ← PowerSeries.coeff_map]
  simp

/-- At `x = 0`, `qPochhammerSeries N c 0 = 1`. -/
@[simp]
theorem qPochhammerSeries_zero_right (N c : ℕ) :
    qPochhammerSeries N c (0 : R) = 1 := by
  ext m
  simp [coeff_qPochhammerSeries]

/-- For `0 < N` and `0 < c`, the `m`-th coefficient of `qPochhammerSeries N c x` agrees with that
of the partial product of any length `K ≥ m`. -/
theorem coeff_qPochhammerSeries_eq_coeff_prod_range {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (x : R)
    {m K : ℕ} (hmK : m ≤ K) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range K, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK
  clear hmK
  induction d with
  | zero =>
    rw [add_zero, coeff_qPochhammerSeries]
  | succ d ih =>
    rw [← add_assoc, Finset.prod_range_succ, mul_sub, mul_one, map_sub, ← ih]
    have hlt : m < N * (m + d) + c := by
      have : 1 * m ≤ N * (m + d) := Nat.mul_le_mul hN (Nat.le_add_right m d)
      omega
    have hzero : PowerSeries.coeff m
        ((∏ n ∈ Finset.range (m + d), (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) *
          (PowerSeries.C x * PowerSeries.X ^ (N * (m + d) + c))) = 0 := by
      rw [mul_comm _ (PowerSeries.C x * _), mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul']
      simp [hlt.not_ge]
    rw [hzero, sub_zero]

/-- **Shift recurrence for `qPochhammerSeries`.** For `0 < N` and `0 < c`, splitting off the `n = 0`
factor gives `qPochhammerSeries N c x = (1 - C x * X ^ c) * qPochhammerSeries N (N + c) x`. -/
theorem qPochhammerSeries_eq_one_sub_mul {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (x : R) :
    qPochhammerSeries N c x =
      (1 - PowerSeries.C x * PowerSeries.X ^ c) * qPochhammerSeries N (N + c) x := by
  ext m
  have hexp (n : ℕ) : N * (n + 1) + c = N * n + (N + c) := by ring
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN hc x (Nat.le_succ m),
    Finset.prod_range_succ', mul_zero, zero_add, mul_comm, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp2 : p.2 ≤ m := by
    have := Finset.mem_antidiagonal.mp hp
    omega
  simp only [hexp]
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN (by omega) x hp2]

/-- Splitting off the first `k` factors of `qPochhammerSeries N c x` for `0 < N` and `0 < c`. -/
theorem qPochhammerSeries_eq_prod_range_mul {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (k : ℕ) (x : R) :
    qPochhammerSeries N c x =
      (∏ n ∈ Finset.range k, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) *
        qPochhammerSeries N (N * k + c) x := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have hexp (n : ℕ) : N * n + (N + c) = N * (n + 1) + c := by ring
    rw [qPochhammerSeries_eq_one_sub_mul hN hc x, ih (by omega),
      Finset.prod_range_succ', mul_zero, zero_add]
    simp only [hexp]
    ring

end TauCeti
