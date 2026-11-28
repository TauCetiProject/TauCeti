/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Top-degree coefficients of first-order tie relations

For a family of elements `N S` in a ring `R` indexed by subsets `S` of a finite set `J` that
factors at each `j ∉ S` as `N S = N' * Nm j` and `N (insert j S) = N' * der j`, this file proves
that the top square-free coefficient of `(∑ S, N S ∏_{i ∈ S} X_i) * G * (t - X_j r)` vanishes
under a ring homomorphism `σ` whenever `Nm j * ac t = 0` and `σ (der j * ac t) = σ (Nm j * ac r)`.

## Main results

* `TauCeti.coeff_mul_C_sub_X_mul_C_of_notMem`: coefficient of `∏_{i ∈ S} X_i` in
  `G * (C t - X j * C r)` when `j ∉ S`.
* `TauCeti.coeff_mul_C_sub_X_mul_C_insert`: coefficient of `X_j ∏_{i ∈ S} X_i` in
  `G * (C t - X j * C r)` when `j ∉ S`.
* `TauCeti.map_sum_compl_mul_coeff_mul_C_sub_X_mul_C_eq_zero`: vanishing of the top square-free
  coefficient under `σ`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/OnePrime.lean`
(`New.Patching.coeff_mul_C_sub_X_mul_C_of_notMem`,
`New.Patching.coeff_mul_C_sub_X_mul_C_insert`,
`New.Patching.map_top_coeff_mul_C_sub_X_mul_C_eq_zero`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset

/-- For `j ∉ S`, the coefficient of `∏_{i ∈ S} X i` in `G * (C t - X j * C r)` is `t` times the
corresponding coefficient in `G`. -/
theorem coeff_mul_C_sub_X_mul_C_of_notMem {J T : Type*} [CommRing T] (G : MvPolynomial J T)
    (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (MvPolynomial.C t - MvPolynomial.X j * MvPolynomial.C r)).coeff
        (∑ i ∈ S, Finsupp.single i 1) =
      t * G.coeff (∑ i ∈ S, Finsupp.single i 1) := by
  classical
  simp [mul_sub, ← mul_assoc, mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_mul_X',
    Finsupp.finsetSum_apply, Finsupp.single_apply, hj]

/-- For `j ∉ S`, the coefficient of `X j * ∏_{i ∈ S} X i` in `G * (C t - X j * C r)` is `t` times
the coefficient of `X j * ∏_{i ∈ S} X i` in `G` minus `r` times the coefficient of
`∏_{i ∈ S} X i` in `G`. -/
theorem coeff_mul_C_sub_X_mul_C_insert {J T : Type*} [DecidableEq J] [CommRing T]
    (G : MvPolynomial J T) (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (MvPolynomial.C t - MvPolynomial.X j * MvPolynomial.C r)).coeff
        (∑ i ∈ insert j S, Finsupp.single i 1) =
      t * G.coeff (∑ i ∈ insert j S, Finsupp.single i 1) -
        r * G.coeff (∑ i ∈ S, Finsupp.single i 1) := by
  rw [mul_sub, mul_left_comm G, AddMonoidAlgebra.coeff_sub_apply, sum_insert hj,
    MvPolynomial.coeff_X_mul]
  simp [mul_comm G]

/-- Let `σ : R →+* R'` and `ac : T →+* R` be ring homomorphisms, and let `N : Finset J → R`
satisfy `N S = N' * Nm j` and `N (insert j S) = N' * der j` for each `j ∉ S`. If `Nm j * ac t = 0`
and `σ (der j * ac t) = σ (Nm j * ac r)`, then for every `G : MvPolynomial J T`, the image under
`σ` of the top square-free coefficient of `(∑ S, N S ∏_{i ∈ S} X i) * (G * (C t - X j * C r))`
is zero. -/
theorem map_sum_compl_mul_coeff_mul_C_sub_X_mul_C_eq_zero {J R R' T : Type*} [Fintype J]
    [DecidableEq J] [Ring R] [Ring R'] [CommRing T] {σ : R →+* R'} (ac : T →+* R)
    {N : Finset J → R} {Nm der : J → R}
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S →
      ∃ N' : R, N S = N' * Nm j ∧ N (insert j S) = N' * der j)
    {j : J} {t r : T} (h_norm : Nm j * ac t = 0) (h_tie : σ (der j * ac t) = σ (Nm j * ac r))
    (G : MvPolynomial J T) :
    σ (∑ S : Finset J,
      N Sᶜ * ac ((G * (MvPolynomial.C t - MvPolynomial.X j * MvPolynomial.C r)).coeff
        (∑ i ∈ S, Finsupp.single i 1))) = 0 := by
  rw [← powerset_univ, ← insert_erase (mem_univ j), sum_powerset_insert (notMem_erase j _),
    ← sum_add_distrib, map_sum]
  refine sum_eq_zero fun S hS ↦ ?_
  have hj : j ∉ S := fun h ↦ notMem_erase j _ (mem_powerset.mp hS h)
  obtain ⟨N', h_insert, h_S⟩ : ∃ N' : R, N (insert j S)ᶜ = N' * Nm j ∧ N Sᶜ = N' * der j := by
    simpa only [insert_compl_insert hj] using h_factor j (insert j S)ᶜ (by simp)
  have kill (b : T) : N' * Nm j * ac (t * b) = 0 := by
    simp [mul_assoc, ← mul_assoc (Nm j), h_norm]
  have tie (b : T) : σ (N' * der j * ac (t * b)) = σ (N' * Nm j * ac (r * b)) := by
    simpa only [map_mul, mul_assoc] using congrArg (σ N' * · * σ (ac b)) h_tie
  let b : T := G.coeff (∑ i ∈ S, Finsupp.single i 1)
  let b' : T := G.coeff (∑ i ∈ insert j S, Finsupp.single i 1)
  rw [map_add, coeff_mul_C_sub_X_mul_C_of_notMem G t r hj,
    coeff_mul_C_sub_X_mul_C_insert G t r hj, h_S, h_insert]
  calc σ (N' * der j * ac (t * b)) + σ (N' * Nm j * ac (t * b' - r * b))
      = σ (N' * Nm j * ac (r * b)) + σ (-(N' * Nm j * ac (r * b))) := by
        rw [tie, map_sub, mul_sub, kill, zero_sub]
    _ = 0 := by rw [map_neg, add_neg_cancel]

end TauCeti
