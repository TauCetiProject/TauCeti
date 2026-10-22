/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Exchanging the variables of an iterated power series

A power series in `v` whose coefficients are power series in `u`, an element of `R⟦X⟧⟦X⟧`, is a
power series in the two variables `u` and `v`: the coefficient of `uᵃ vᵇ` in `G` is
`coeff a (coeff b G)`. This file defines the exchange of the two variables, `PowerSeries.swap`,
as a ring homomorphism. It is an involution.

## Main definitions

* `PowerSeries.swap`: the ring homomorphism `R⟦X⟧⟦X⟧ → R⟦X⟧⟦X⟧` exchanging the two variables.

## Main results

* `PowerSeries.coeff_coeff_swap`: the coefficient of `uᵃ vᵇ` in `swap G` is that of `uᵇ vᵃ` in
  `G`.
* `PowerSeries.swap_swap`: `swap` is an involution.
* `PowerSeries.swap_C`, `PowerSeries.swap_map_C`, `PowerSeries.swap_X`: `swap` exchanges the
  power series in the inner variable `u`, embedded as constants, with those in the outer variable
  `v`, embedded through `map C`.
* `Polynomial.coeff_coeff_swapPowerSeries`: the coefficient of `Xⁱ` in the `tᵏ`-coefficient of
  `swapPowerSeries Q` is the `tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`.
* `Polynomial.swapPowerSeries_C`, `Polynomial.swapPowerSeries_X`: the values of
  `swapPowerSeries` on constants and on the polynomial variable.
* `Polynomial.swapPowerSeries_injective`: `swapPowerSeries` is injective.
* `Polynomial.coeff_swapPowerSeries_mem_degreeLT`: `swapPowerSeries` preserves degree bounds
  coefficientwise.
* `Polynomial.exists_monic_swapPowerSeries_eq`: the power series with monic constant coefficient
  and degree-bounded higher coefficients are exactly images of monic polynomials.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The exchange of the two variables of `R⟦X⟧⟦X⟧`, viewed as power series in `u` and `v`: the
coefficient of `uᵃ vᵇ` in `swap G` is the coefficient of `uᵇ vᵃ` in `G`. -/
noncomputable def swap : R⟦X⟧⟦X⟧ →+* R⟦X⟧⟦X⟧ where
  toFun G := mk fun b ↦ mk fun a ↦ coeff b (coeff a G)
  map_one' := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp only [coeff_mk, coeff_one]
    split_ifs <;> simp_all
  map_mul' G H := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp only [coeff_mk, coeff_mul, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp
  map_add' G H := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp

/-- The coefficient of `uᵃ vᵇ` in `swap G` is the coefficient of `uᵇ vᵃ` in `G`. -/
@[simp]
theorem coeff_coeff_swap (G : R⟦X⟧⟦X⟧) (a b : ℕ) :
    coeff a (coeff b (swap G)) = coeff b (coeff a G) := by
  simp [swap]

/-- Exchanging the variables twice is the identity. -/
@[simp]
theorem swap_swap (G : R⟦X⟧⟦X⟧) : swap (swap G) = G :=
  PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ by simp

/-- Exchanging the variables sends a power series in the inner variable `u` to the same power
series in the outer variable `v`. -/
@[simp]
theorem swap_C (f : R⟦X⟧) : swap (C f) = map C f :=
  PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ by
    simp only [coeff_coeff_swap, coeff_C, coeff_map]
    split_ifs <;> simp

/-- Exchanging the variables sends a power series in the outer variable `v` to the same power
series in the inner variable `u`. -/
@[simp]
theorem swap_map_C (f : R⟦X⟧) : swap (map C f) = C f := by
  rw [← swap_C, swap_swap]

/-- Exchanging the variables sends the outer variable `v` to the inner variable `u`. -/
@[simp]
theorem swap_X : swap (X : R⟦X⟧⟦X⟧) = C X := by
  rw [← map_X (C (R := R)), swap_map_C]

end PowerSeries

open scoped Polynomial PowerSeries

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- The ring homomorphism `R⟦X⟧[X] →+* R[X]⟦X⟧` exchanging the two variables: a polynomial in
`X` whose coefficients are power series in `t` is sent to the power series in `t` whose
coefficients are polynomials in `X`. -/
noncomputable def swapPowerSeries : R⟦X⟧[X] →+* R[X]⟦X⟧ :=
  eval₂RingHom (PowerSeries.map C) (PowerSeries.C X)

/-- `swapPowerSeries` sends a constant polynomial with coefficient `a : R⟦t⟧` to the same
power series in `t` with constant polynomial coefficients. -/
@[simp]
theorem swapPowerSeries_C (a : R⟦X⟧) : swapPowerSeries (C a) = PowerSeries.map C a :=
  eval₂_C _ _

/-- `swapPowerSeries` sends the polynomial variable to the constant power series `X`. -/
@[simp]
theorem swapPowerSeries_X : swapPowerSeries (X : R⟦X⟧[X]) = PowerSeries.C (X : R[X]) :=
  eval₂_X _ _

/-- The coefficient of `Xⁱ` in the `tᵏ`-coefficient of `swapPowerSeries Q` is the
`tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`. -/
@[simp]
theorem coeff_coeff_swapPowerSeries (Q : R⟦X⟧[X]) (k i : ℕ) :
    (PowerSeries.coeff k (swapPowerSeries Q)).coeff i = PowerSeries.coeff k (Q.coeff i) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [swapPowerSeries, coe_eval₂RingHom, eval₂_monomial, ← map_pow,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_map, coeff_C_mul_X_pow, coeff_monomial]
    split_ifs <;> simp_all

/-- The constant coefficient of `swapPowerSeries Q` is the reduction of `Q` modulo `t`. -/
@[simp]
theorem constantCoeff_swapPowerSeries (Q : R⟦X⟧[X]) :
    PowerSeries.constantCoeff (swapPowerSeries Q) = Q.map PowerSeries.constantCoeff := by
  ext i
  rw [coeff_map, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_swapPowerSeries]

/-- A polynomial over `R⟦t⟧` is determined by its image under `swapPowerSeries`. -/
theorem swapPowerSeries_injective : Function.Injective (swapPowerSeries (R := R)) := by
  intro P Q h
  ext i k
  rw [← coeff_coeff_swapPowerSeries, h, coeff_coeff_swapPowerSeries]

/-- If `Q` has degree `< n`, then so does every coefficient of `swapPowerSeries Q`. -/
theorem coeff_swapPowerSeries_mem_degreeLT {Q : R⟦X⟧[X]} {n : ℕ}
    (hQ : Q ∈ degreeLT R⟦X⟧ n) (k : ℕ) :
    PowerSeries.coeff k (swapPowerSeries Q) ∈ degreeLT R n := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hQ ⊢
  intro i hi
  simp [hQ i hi]

section Ring

variable {S : Type*} [CommSemiring S]

/-- A power series `F` over `R[X]` whose constant coefficient is monic of degree `d` and whose
other coefficients have degree `< d` comes from a monic polynomial over `R⟦X⟧` of degree `d`
reducing to `g` modulo `t`. -/
theorem exists_monic_swapPowerSeries_eq [Nontrivial S] {g : S[X]} (hg : g.Monic)
    {F : S[X]⟦X⟧} (hF₀ : PowerSeries.constantCoeff F = g)
    (hF : ∀ k, 1 ≤ k → PowerSeries.coeff k F ∈ degreeLT S g.natDegree) :
    ∃ G : S⟦X⟧[X], G.Monic ∧ G.natDegree = g.natDegree ∧
      G.map PowerSeries.constantCoeff = g ∧ swapPowerSeries G = F := by
  suffices ∃ G : S⟦X⟧[X], G.Monic ∧ swapPowerSeries G = F by
    obtain ⟨G, hG, rfl⟩ := this
    rw [constantCoeff_swapPowerSeries] at hF₀
    exact ⟨G, hG, by rw [← hF₀, hG.natDegree_map], hF₀, rfl⟩
  let a : ℕ → S⟦X⟧ := fun i ↦ PowerSeries.mk fun k ↦ (PowerSeries.coeff k F).coeff i
  have hdeg : (∑ i : Fin g.natDegree, C (a i) * X ^ (i : ℕ)).degree < (g.natDegree : WithBot ℕ) :=
    degree_sum_fin_lt _
  refine ⟨X ^ g.natDegree + ∑ i : Fin g.natDegree, C (a i) * X ^ (i : ℕ),
    monic_X_pow_add hdeg, ?_⟩
  ext k i
  rw [coeff_coeff_swapPowerSeries, coeff_add, coeff_X_pow]
  have hFk : (PowerSeries.coeff k F).coeff g.natDegree = if k = 0 then 1 else 0 := by
    split_ifs with hk
    · rw [hk, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF₀, hg.coeff_natDegree]
    · exact coeff_eq_zero_of_degree_lt (mem_degreeLT.mp (hF k (Nat.one_le_iff_ne_zero.mpr hk)))
  rcases lt_trichotomy i g.natDegree with hi | rfl | hi
  · rw [ite_eq_right hi.ne, zero_add, finsetSum_coeff,
      Finset.sum_eq_single ⟨i, hi⟩ (fun j _ hj ↦ ?_) (by simp)]
    · simp [a]
    · rw [coeff_C_mul_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm))]
  · rw [ite_eq_left rfl, coeff_eq_zero_of_degree_lt hdeg, add_zero, hFk, PowerSeries.coeff_one]
  · rw [ite_eq_right hi.ne', zero_add,
      coeff_eq_zero_of_degree_lt (hdeg.trans (by exact_mod_cast hi)), map_zero]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hF₀, coeff_eq_zero_of_natDegree_lt hi]
    · exact (coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp
        (hF k (Nat.one_le_iff_ne_zero.mpr hk))).trans (by exact_mod_cast hi))).symm

end Ring

end Polynomial
