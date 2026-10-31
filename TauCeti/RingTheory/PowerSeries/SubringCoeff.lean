/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series with coefficients in a subring

Let `R` be a subring of a ring `S`, and let `D` be a power series over `S` with coefficients in
`R` whose first nonzero coefficient, in degree `m`, is `1`; that is, `D = Xᵐ u` with `u(0) = 1`.
If `F * D` has coefficients in `R`, then so does `F` (`PowerSeries.coeff_mem_of_coeff_mul_mem`):
the coefficients of `F` are solved for recursively from those of `F * D`.

This is how integrality of `q`-expansions passes through division by a modular form such as the
discriminant `Δ = q + ⋯`, whose `q`-expansion has integer coefficients.

A power series is the image under `map f` of a power series exactly when each of its coefficients
is in the range of `f` (`PowerSeries.mem_map_rangeS`). For the inclusion of a subring, this lifts a
power series with coefficients in the subring to a power series over the subring.

## Main results

* `PowerSeries.mem_map_rangeS`: `p` is in the range of `map f` if and only if every coefficient
  of `p` is in the range of `f`.
* `PowerSeries.coeff_mem_of_coeff_mul_mem`: if `F * D` and `D = Xᵐ u`, `u(0) = 1`, have
  coefficients in `R`, then so does `F`.
-/

public section

namespace PowerSeries

section Map

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

/-- A power series over `S` is in the range of `map f` if and only if each of its coefficients is
in the range of `f`. This is the power-series form of Mathlib's `Polynomial.mem_map_rangeS`. -/
theorem mem_map_rangeS {p : S⟦X⟧} : p ∈ (map f).rangeS ↔ ∀ n, coeff n p ∈ f.rangeS := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨q, rfl⟩ n
    rw [coeff_map]
    exact f.mem_rangeS_self _
  · simp only [RingHom.mem_rangeS] at h
    choose c hc using h
    exact ⟨mk c, ext fun n ↦ by rw [coeff_map, coeff_mk, hc]⟩

end Map

variable {S : Type*} [Ring S] {R : Subring S}

/-- **Division by `Xᵐ u` with `u(0) = 1` preserves coefficients in a subring.** If `D` has
coefficients in `R`, vanishes below degree `m` and has coefficient `1` in degree `m`, and `F * D`
has coefficients in `R`, then `F` has coefficients in `R`. -/
theorem coeff_mem_of_coeff_mul_mem {m : ℕ} {F D : S⟦X⟧} (hD : ∀ i < m, coeff i D = 0)
    (hDm : coeff m D = 1) (hDR : ∀ i, coeff i D ∈ R) (hFD : ∀ n, coeff n (F * D) ∈ R) (n : ℕ) :
    coeff n F ∈ R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hmem : (n, m) ∈ Finset.antidiagonal (n + m) := Finset.mem_antidiagonal.mpr rfl
  have h := hFD (n + m)
  rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem, hDm, mul_one] at h
  -- every other term involves an earlier coefficient of `F` or a vanishing coefficient of `D`
  refine (add_mem_cancel_right (R.sum_mem fun p hp ↦ ?_)).mp h
  obtain ⟨hpne, hp⟩ := Finset.mem_erase.mp hp
  have hsum : p.1 + p.2 = n + m := Finset.mem_antidiagonal.mp hp
  rcases lt_trichotomy p.1 n with hlt | heq | hgt
  · exact R.mul_mem (ih _ hlt) (hDR _)
  · exact absurd (Prod.ext heq (by omega)) hpne
  · rw [hD _ (by omega), mul_zero]
    exact R.zero_mem

end PowerSeries
