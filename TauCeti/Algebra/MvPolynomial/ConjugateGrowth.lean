/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polydisc scaling and conjugate growth of homogeneous polynomials

Let `Q : MvPolynomial ι ℂ` be a homogeneous polynomial of degree `d` and `σ : ℂ ≃+* ℂ` a ring
automorphism of `ℂ`. A bound `‖σ (Q.eval z)‖ ≤ B` on the polydisc `∀ i, ‖σ (z i)‖ ≤ ρ` scales
by homogeneity to `‖σ (Q.eval z)‖ ≤ B * t ^ d` on the dilated polydisc `∀ i, ‖σ (z i)‖ ≤ t * ρ`
for every `t > 0` (`TauCeti.norm_map_eval_le_of_isHomogeneous`).

From this polydisc scaling, if `∑ i, ‖σ (z i)‖ ^ 2 ≤ R` with `R > 0` and `ρ > 0`, then
`‖σ (Q.eval z)‖ ≤ B * (√R / ρ) ^ d` (`TauCeti.norm_map_eval_le_mul_div_pow_of_isHomogeneous`),
and under `∑ i, ‖σ (z i)‖ ^ 2 ≤ T * (2 * d + 2) * R` with `0 ≤ T * (2 * d + 2) ≤ ρ ^ 2`, we
obtain the exponential growth bound `‖σ (Q.eval z)‖ ≤ B * Real.exp (d * R)`
(`TauCeti.norm_map_eval_le_mul_exp_of_isHomogeneous`).

## Main results

* `TauCeti.norm_map_eval_le_of_isHomogeneous`
* `TauCeti.norm_map_eval_le_mul_div_pow_of_isHomogeneous`
* `TauCeti.norm_map_eval_le_mul_exp_of_isHomogeneous`

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/Kernels/DefiniteKernelSize.lean`, declarations
`New.norm_map_eval_le_of_isHomogeneous` and `New.hasConjugateGrowth_of_isHomogeneous`.
-/

public section

open MvPolynomial Real Finset

namespace TauCeti

/-- Polydisc scaling for a homogeneous polynomial `Q : MvPolynomial ι ℂ` of degree `d` under a
ring automorphism `σ : ℂ ≃+* ℂ`: a bound `B` for `‖σ (Q.eval z)‖` on `∀ i, ‖σ (z i)‖ ≤ ρ`
scales to `B * t ^ d` on `∀ i, ‖σ (z i)‖ ≤ t * ρ` for any `t > 0`. -/
theorem norm_map_eval_le_of_isHomogeneous {ι : Type*} {Q : MvPolynomial ι ℂ} {d : ℕ}
    (hQ : MvPolynomial.IsHomogeneous Q d) (σ : ℂ ≃+* ℂ) {ρ B : ℝ}
    (hB : ∀ z : ι → ℂ, (∀ i : ι, ‖σ (z i)‖ ≤ ρ) → ‖σ (MvPolynomial.eval z Q)‖ ≤ B) {t : ℝ}
    (ht : 0 < t) {z : ι → ℂ} (hz : ∀ i : ι, ‖σ (z i)‖ ≤ t * ρ) :
    ‖σ (MvPolynomial.eval z Q)‖ ≤ B * t ^ d := by
  let u : ℂ := σ.symm (t : ℂ)⁻¹
  have h_eval : MvPolynomial.eval (fun i ↦ u * z i) Q = u ^ d * MvPolynomial.eval z Q := by
    simpa only [Pi.smul_def, smul_eq_mul] using hQ.eval_smul u z
  have h_scaled : ‖σ (MvPolynomial.eval (fun i ↦ u * z i) Q)‖ ≤ B :=
    hB _ fun i ↦ by simpa [u, abs_of_pos ht, inv_mul_le_iff₀ ht] using hz i
  rw [h_eval] at h_scaled
  simpa [u, abs_of_pos ht, inv_mul_le_iff₀ (pow_pos ht d), mul_comm B] using h_scaled

/-- `L²`-ball scaling for a homogeneous polynomial `Q : MvPolynomial ι ℂ` of degree `d` under
`σ : ℂ ≃+* ℂ`: if `‖σ (MvPolynomial.eval z Q)‖ ≤ B` on `∀ i, ‖σ (z i)‖ ≤ ρ` (`0 < ρ`), then
`∑ i, ‖σ (z i)‖ ^ 2 ≤ R` (`0 < R`) implies `‖σ (MvPolynomial.eval z Q)‖ ≤ B * (√R / ρ) ^ d`. -/
theorem norm_map_eval_le_mul_div_pow_of_isHomogeneous {ι : Type*} [Fintype ι]
    {Q : MvPolynomial ι ℂ} {d : ℕ} (hQ : MvPolynomial.IsHomogeneous Q d) (σ : ℂ ≃+* ℂ)
    {ρ B R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hB : ∀ z : ι → ℂ, (∀ i : ι, ‖σ (z i)‖ ≤ ρ) → ‖σ (MvPolynomial.eval z Q)‖ ≤ B)
    {z : ι → ℂ} (hz : ∑ i : ι, ‖σ (z i)‖ ^ 2 ≤ R) :
    ‖σ (MvPolynomial.eval z Q)‖ ≤ B * (√R / ρ) ^ d := by
  refine norm_map_eval_le_of_isHomogeneous hQ σ hB (by positivity) fun i ↦ ?_
  rw [div_mul_cancel₀ _ hρ.ne']
  have hsq : ‖σ (z i)‖ ^ 2 ≤ R :=
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖σ (z j)‖) (Finset.mem_univ i)).trans hz
  exact Real.le_sqrt_of_sq_le hsq

/-- Exponential conjugate growth for a homogeneous polynomial `Q : MvPolynomial ι ℂ` of degree `d`:
if `‖σ (MvPolynomial.eval z Q)‖ ≤ B` on the polydisc of radius `ρ > 0` and
`0 ≤ T * (2 * d + 2) ≤ ρ ^ 2`, then `∑ i, ‖σ (z i)‖ ^ 2 ≤ T * (2 * d + 2) * R` implies
`‖σ (MvPolynomial.eval z Q)‖ ≤ B * exp (d * R)`. -/
theorem norm_map_eval_le_mul_exp_of_isHomogeneous {ι : Type*} [Fintype ι]
    {Q : MvPolynomial ι ℂ} {d : ℕ} (hQ : MvPolynomial.IsHomogeneous Q d) (σ : ℂ ≃+* ℂ)
    {ρ B T R : ℝ} (hρ : 0 < ρ) (hT0 : 0 ≤ T) (hT : T * (2 * (d : ℝ) + 2) ≤ ρ ^ 2)
    (hB : ∀ z : ι → ℂ, (∀ i : ι, ‖σ (z i)‖ ≤ ρ) → ‖σ (MvPolynomial.eval z Q)‖ ≤ B)
    {z : ι → ℂ} (hz : ∑ i : ι, ‖σ (z i)‖ ^ 2 ≤ T * (2 * (d : ℝ) + 2) * R) :
    ‖σ (MvPolynomial.eval z Q)‖ ≤ B * exp (d * R) := by
  have h_coord (i : ι) : ‖σ (z i)‖ ≤ exp R * ρ := by
    have hsq : ‖σ (z i)‖ ^ 2 ≤ (exp R * ρ) ^ 2 := by
      have h1 : ‖σ (z i)‖ ^ 2 ≤ T * (2 * (d : ℝ) + 2) * R :=
        (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖σ (z j)‖) (Finset.mem_univ i)).trans hz
      have hR_le : R ≤ exp R ^ 2 := by
        have h2 : R + 1 ≤ exp R := add_one_le_exp R
        nlinarith [exp_pos R]
      have h_mul : T * (2 * (d : ℝ) + 2) * R ≤ ρ ^ 2 * exp R ^ 2 := by
        by_cases hR0 : 0 ≤ R
        · exact mul_le_mul hT hR_le hR0 (sq_nonneg ρ)
        · have h_le0 : T * (2 * (d : ℝ) + 2) * R ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hR0)
          exact h_le0.trans (by positivity)
      calc ‖σ (z i)‖ ^ 2 ≤ ρ ^ 2 * exp R ^ 2 := h1.trans h_mul
        _ = (exp R * ρ) ^ 2 := by ring
    exact le_of_sq_le_sq hsq (by positivity)
  simpa [← exp_natCast_mul] using
    norm_map_eval_le_of_isHomogeneous hQ σ hB (exp_pos R) h_coord

end TauCeti
