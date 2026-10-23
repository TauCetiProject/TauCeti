/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# Truncations and finite expansions of power series

This file collects facts used to compare power series to a finite order `m`:
* the truncation `trunc m φ` vanishes exactly when `φ` has order at least `m`,
* two power series have equal `m`-truncations if and only if their coefficients agree below `m`,
* the `m`-truncations of `inv.aux a φ`, `invOfUnit φ u`, `φ⁻¹`, integer powers `u ^ k`,
  and products `(u ^ k) * d⁄dX u` of a unit `u : R⟦X⟧ˣ` depend only on a finite truncation of the
  input,
* the coefficients of a finite expansion `∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, read as zero from degree
  `m` on, and
* the coefficients of a polynomial times a power series expand along the polynomial monomials.

## Main results

* `PowerSeries.trunc_eq_zero_iff_le_order`: `trunc m φ = 0 ↔ m ≤ order φ`.
* `PowerSeries.trunc_eq_trunc_iff`: `trunc m φ = trunc m ψ ↔ ∀ n < m, coeff n φ = coeff n ψ`.
* `PowerSeries.trunc_inv_aux_eq_of_trunc_eq`, `PowerSeries.trunc_invOfUnit_eq_of_trunc_eq`,
  `PowerSeries.trunc_inv_eq_of_trunc_eq`, `PowerSeries.trunc_val_inv_eq_of_trunc_eq`: the `m`-th
  truncation of an inverse power series depends only on `trunc m`.
* `PowerSeries.trunc_val_zpow_eq_of_trunc_eq` and
  `PowerSeries.trunc_val_zpow_mul_derivative_eq_of_trunc_eq`: the finite jets of `u ^ k` and
  `(u ^ k) * d⁄dX u` for a unit `u : R⟦X⟧ˣ` depend only on `trunc m u` and `trunc (m + 1) u`.
* `PowerSeries.coeff_sum_C_mul_X_pow`: the coefficients of `∑ i : Fin m, C (a i) * X ^ i`.
* `PowerSeries.coeff_coe_mul_eq_sum`: `coeff n (p * g) = ∑_{i < N} pᵢ coeff n (Xⁱ g)` for a
  polynomial `p` of degree less than `N`.
-/

public section

namespace PowerSeries

section Semiring

variable {R : Type*} [Semiring R]

/-- The truncation below degree `m` of a power series vanishes exactly when the series has
order at least `m`. -/
theorem trunc_eq_zero_iff_le_order {m : ℕ} {φ : R⟦X⟧} : trunc m φ = 0 ↔ (m : ℕ∞) ≤ φ.order := by
  rw [nat_le_order_iff]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ Polynomial.ext fun i ↦ ?_⟩
  · simpa [coeff_trunc, hi] using congrArg (Polynomial.coeff · i) h
  · rw [coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hi
    exacts [h i hi, rfl]

/-- Two power series with the same `m`-truncation have the same `n`-th coefficient for every
`n < m`. -/
theorem coeff_eq_of_trunc_eq {n m : ℕ} {φ ψ : R⟦X⟧} (h : trunc m φ = trunc m ψ) (hn : n < m) :
    coeff n φ = coeff n ψ := by
  have hc := congrArg (Polynomial.coeff · n) h
  rwa [coeff_trunc, coeff_trunc, ite_eq_left hn, ite_eq_left hn] at hc

/-- Two power series have the same `m`-truncation if and only if their coefficients agree in all
degrees `< m`. -/
theorem trunc_eq_trunc_iff {m : ℕ} {φ ψ : R⟦X⟧} :
    trunc m φ = trunc m ψ ↔ ∀ n < m, coeff n φ = coeff n ψ := by
  refine ⟨fun h n hn ↦ coeff_eq_of_trunc_eq h hn, fun h ↦ Polynomial.ext fun n ↦ ?_⟩
  rw [coeff_trunc, coeff_trunc]
  split_ifs with hn
  exacts [h n hn, rfl]

/-- Equality of truncations at `m` implies equality of truncations at any `n ≤ m`. -/
theorem trunc_eq_of_trunc_eq_of_le {n m : ℕ} {φ ψ : R⟦X⟧} (h : trunc m φ = trunc m ψ)
    (hnm : n ≤ m) : trunc n φ = trunc n ψ :=
  trunc_eq_trunc_iff.mpr fun _ hi ↦ coeff_eq_of_trunc_eq h (hi.trans_le hnm)

/-- The `m`-truncation of a product depends only on the `m`-truncations of the factors. -/
theorem trunc_mul_eq_of_trunc_eq {m : ℕ} {f₁ f₂ g₁ g₂ : R⟦X⟧} (hf : trunc m f₁ = trunc m f₂)
    (hg : trunc m g₁ = trunc m g₂) : trunc m (f₁ * g₁) = trunc m (f₂ * g₂) := by
  rw [trunc_eq_trunc_iff]
  intro n hn
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_eq_of_trunc_eq hf ((Nat.le_add_right x.1 x.2).trans_lt (hx ▸ hn)),
    coeff_eq_of_trunc_eq hg ((Nat.le_add_left x.2 x.1).trans_lt (hx ▸ hn))]

/-- The `m`-truncation of a power depends only on the `m`-truncation of the base. -/
theorem trunc_pow_eq_of_trunc_eq {m : ℕ} {f g : R⟦X⟧} (h : trunc m f = trunc m g) (k : ℕ) :
    trunc m (f ^ k) = trunc m (g ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, trunc_mul_eq_of_trunc_eq ih h]

/-- The coefficients of the finite expansion `∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, and vanish from
degree `m` on. -/
theorem coeff_sum_C_mul_X_pow {m : ℕ} (a : Fin m → R) (n : ℕ) :
    coeff n (∑ i : Fin m, C (a i) * X ^ (i : ℕ)) = if h : n < m then a ⟨n, h⟩ else 0 := by
  simp only [map_sum, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨n, h⟩ fun i hi ↦ by
      have hni : n ≠ (i : ℕ) := fun hn ↦ hi (Fin.ext hn.symm)
      simp [hni]]
    simp
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hni : n ≠ (i : ℕ) := (i.2.trans_le (not_lt.mp h)).ne'
    simp [hni]

/-- The coefficients of the product of a polynomial `p` and a power series `g`, expanded along the
monomials of `p` below any bound `N` on its degree. -/
theorem coeff_coe_mul_eq_sum (p : Polynomial R) (g : R⟦X⟧) {N : ℕ} (hN : p.natDegree < N)
    (n : ℕ) : coeff n ((p : R⟦X⟧) * g) = ∑ i ∈ Finset.range N, p.coeff i * coeff n (X ^ i * g) := by
  rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_eq_sum_range' _ hN, Finset.sum_mul,
    map_sum]
  simp [mul_assoc, coeff_C_mul]

end Semiring

section Ring

variable {R : Type*} [Ring R]

/-- For `n < m`, the `n`-th coefficient of `PowerSeries.inv.aux a φ` depends only on `trunc m φ`. -/
theorem coeff_inv_aux_eq_of_trunc_eq {n m : ℕ} (a : R) {φ ψ : R⟦X⟧} (h : trunc m φ = trunc m ψ)
    (hn : n < m) : coeff n (PowerSeries.inv.aux a φ) = coeff n (PowerSeries.inv.aux a ψ) := by
  induction n using Nat.strong_induction_on with | h n ih =>
  rw [coeff_inv_aux, coeff_inv_aux]
  split_ifs with hn0
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_antidiagonal] at hx
    split_ifs with hlt
    · have hx1 : x.1 < m := (Nat.le_add_right x.1 x.2).trans_lt (hx ▸ hn)
      rw [coeff_eq_of_trunc_eq h hx1, ih x.2 hlt (hlt.trans hn)]
    · rfl

/-- The `m`-truncation of `PowerSeries.inv.aux a φ` depends only on `trunc m φ`. -/
theorem trunc_inv_aux_eq_of_trunc_eq {m : ℕ} (a : R) {φ ψ : R⟦X⟧} (h : trunc m φ = trunc m ψ) :
    trunc m (PowerSeries.inv.aux a φ) = trunc m (PowerSeries.inv.aux a ψ) :=
  trunc_eq_trunc_iff.mpr fun _ hn ↦ coeff_inv_aux_eq_of_trunc_eq a h hn

/-- The `m`-truncation of `invOfUnit φ u` depends only on `trunc m φ`. -/
theorem trunc_invOfUnit_eq_of_trunc_eq {m : ℕ} {φ ψ : R⟦X⟧} (u : Rˣ) (h : trunc m φ = trunc m ψ) :
    trunc m (invOfUnit φ u) = trunc m (invOfUnit ψ u) :=
  trunc_inv_aux_eq_of_trunc_eq (↑u⁻¹ : R) h

/-- The `m`-truncation of the inverse of a unit power series depends only on the `m`-truncation of
the unit. -/
theorem trunc_val_inv_eq_of_trunc_eq {m : ℕ} {u v : R⟦X⟧ˣ}
    (h : trunc m (u : R⟦X⟧) = trunc m (v : R⟦X⟧)) :
    trunc m (↑u⁻¹ : R⟦X⟧) = trunc m (↑v⁻¹ : R⟦X⟧) := by
  rcases m with _ | m
  · simp
  · have h0 : constantCoeff (u : R⟦X⟧) = constantCoeff (v : R⟦X⟧) := by
      simpa using coeff_eq_of_trunc_eq h (Nat.zero_lt_succ m)
    have hu : Units.map (constantCoeff (R := R)).toMonoidHom u =
        Units.map (constantCoeff (R := R)).toMonoidHom v := Units.ext h0
    rw [val_inv_eq_invOfUnit, val_inv_eq_invOfUnit, hu]
    exact trunc_invOfUnit_eq_of_trunc_eq _ h

/-- The `m`-truncation of an integer power `u ^ k` of a unit `u : R⟦X⟧ˣ` depends only on
`trunc m u`. -/
theorem trunc_val_zpow_eq_of_trunc_eq {m : ℕ} {u v : R⟦X⟧ˣ}
    (h : trunc m (u : R⟦X⟧) = trunc m (v : R⟦X⟧)) (k : ℤ) :
    trunc m (↑(u ^ k) : R⟦X⟧) = trunc m (↑(v ^ k) : R⟦X⟧) := by
  rcases k with n | n
  · simpa using trunc_pow_eq_of_trunc_eq h n
  · rw [zpow_negSucc, zpow_negSucc, ← inv_pow, ← inv_pow, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    exact trunc_pow_eq_of_trunc_eq (trunc_val_inv_eq_of_trunc_eq h) (n + 1)

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- The `m`-truncation of `(u ^ k) * d⁄dX u` for a unit `u : R⟦X⟧ˣ` depends only on
`trunc (m + 1) u`. -/
theorem trunc_val_zpow_mul_derivative_eq_of_trunc_eq {m : ℕ} {u v : R⟦X⟧ˣ}
    (h : trunc (m + 1) (u : R⟦X⟧) = trunc (m + 1) (v : R⟦X⟧)) (k : ℤ) :
    trunc m ((↑(u ^ k) : R⟦X⟧) * d⁄dX (u : R⟦X⟧)) =
      trunc m ((↑(v ^ k) : R⟦X⟧) * d⁄dX (v : R⟦X⟧)) :=
  trunc_mul_eq_of_trunc_eq
    (trunc_val_zpow_eq_of_trunc_eq (trunc_eq_of_trunc_eq_of_le h (Nat.le_succ m)) k)
    (by rw [trunc_derivative, trunc_derivative, h])

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Over a field, the `m`-truncation of `φ⁻¹` depends only on `trunc m φ`. -/
theorem trunc_inv_eq_of_trunc_eq {m : ℕ} {φ ψ : k⟦X⟧} (h : trunc m φ = trunc m ψ) :
    trunc m φ⁻¹ = trunc m ψ⁻¹ := by
  rcases m with _ | m
  · simp
  · have h0 : constantCoeff φ = constantCoeff ψ := by
      simpa using coeff_eq_of_trunc_eq h (Nat.zero_lt_succ m)
    rw [inv_eq_inv_aux, inv_eq_inv_aux, h0]
    exact trunc_inv_aux_eq_of_trunc_eq _ h

end Field

end PowerSeries
