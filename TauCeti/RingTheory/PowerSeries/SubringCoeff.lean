/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Power series with coefficients in a subring: division and expansion

Let `R` be a subring of a ring `S`, and let `D` be a power series over `S` with coefficients in
`R` whose first nonzero coefficient, in degree `m`, is `1`; that is, `D = Xᵐ u` with `u(0) = 1`.
If `F * D` has coefficients in `R`, then so does `F` (`PowerSeries.coeff_mem_of_coeff_mul_mem`):
the coefficients of `F` are solved for recursively from those of `F * D`.

This is how integrality of `q`-expansions passes through division by a modular form such as the
discriminant `Δ = q + ⋯`, whose `q`-expansion has integer coefficients.

A power series lies in the image of `PowerSeries.map f` exactly when each of its coefficients
lies in the range of `f` (`PowerSeries.mem_map_range`), so the same division statement applies
to images of power series over another ring.

Substituting `Xᵖ` for `X` (`PowerSeries.expand`) only spreads the coefficients out and inserts
zeros, so it neither creates nor destroys coefficients in `R`
(`PowerSeries.forall_coeff_expand_mem_iff`). This is how integrality of a `q`-expansion is
unchanged when it is read in a power of `q`, for instance at a multiple of the cusp width.

## Main results

* `PowerSeries.mem_map_range`: the range of `PowerSeries.map f` consists of the power series whose
  coefficients all lie in the range of `f`.
* `PowerSeries.coeff_mem_of_coeff_mul_mem`: if `F * D` and `D = Xᵐ u`, `u(0) = 1`, have
  coefficients in `R`, then so does `F`.
* `PowerSeries.forall_coeff_expand_mem_iff`: `expand p φ` has coefficients in `R` if and only if
  `φ` does.
-/

public section

namespace PowerSeries

variable {S : Type*} [Ring S] {R : Subring S}

/-- The range of `PowerSeries.map f` consists of the power series whose coefficients all lie in
the range of `f`. -/
theorem mem_map_range {T : Type*} [Ring T] (f : T →+* S) {p : S⟦X⟧} :
    p ∈ (map f).range ↔ ∀ n, coeff n p ∈ f.range := by
  refine ⟨fun ⟨q, hq⟩ n ↦ ⟨coeff n q, by rw [← hq, coeff_map]⟩, fun h ↦ ?_⟩
  choose g hg using h
  exact ⟨mk g, by ext n; simp [hg]⟩

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

/-- **Expansion preserves and reflects coefficients in a subring.** The coefficients of
`expand p φ`, the power series `φ` with `Xᵖ` substituted for `X`, all lie in a subring `R` if and
only if those of `φ` do. -/
@[simp]
theorem forall_coeff_expand_mem_iff {S : Type*} [CommRing S] {R : Subring S} {p : ℕ}
    (hp : p ≠ 0) {φ : S⟦X⟧} : (∀ n, coeff n (expand p hp φ) ∈ R) ↔ ∀ n, coeff n φ ∈ R := by
  refine ⟨fun h n ↦ by simpa using h (p * n), fun h n ↦ ?_⟩
  rw [coeff_expand]
  split_ifs
  · exact h _
  · exact R.zero_mem

end PowerSeries
