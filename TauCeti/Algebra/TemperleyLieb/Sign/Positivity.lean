/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity

import TauCeti.Algebra.TemperleyLieb.Sign

/-!
# Positivity of the Markov trace at negative and nonzero real loop parameters

For a negative real loop parameter `δ < 0`, the unnormalized Markov trace form
`(x, y) ↦ tr n (x⋆ * y)` cannot be positive semidefinite on one strand, where `tr 1 1 = δ < 0`.
Instead, the sign isomorphism `s : TemperleyLieb ℂ (δ : ℂ) n ≃⋆ₐ[ℂ] TemperleyLieb ℂ (-δ : ℂ) n`
of `TauCeti.Algebra.TemperleyLieb.Sign` carries the signed Hermitian form
`(-1) ^ n * tr n (x⋆ * x)` at `δ` to the unsigned Hermitian form `tr' n ((s x)⋆ * s x)` of a
Markov trace `tr'` at `-δ > 0`. Combining this transport with Jones's positivity theorem
(`TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`) classifies positivity
at negative loop parameters:

* For `δ < 0`, the signed forms `(-1) ^ n * tr n (x⋆ * x)` are real and nonnegative at every level
  if and only if `-δ ∈ jonesLoopParameters = {2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`
  (`IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `markovTrace_neg_one_pow_nonneg_iff`).
* When `δ < 0` and `-δ ∉ jonesLoopParameters`, positivity of `(-1) ^ n * tr n (x⋆ * x)` fails on
  every level `n ≥ ⌊π / arccos (-δ / 2)⌋₊`
  (`IsMarkovTrace.exists_neg_one_pow_mul_map_star_mul_self_neg`,
  `IsMarkovTrace.lt_floor_of_forall_neg_one_pow_nonneg`).
* Equivalently, for arbitrary real `δ ≠ 0`, the normalized trace forms
  `(δ : ℂ)⁻¹ ^ n * tr n (x⋆ * x)` are real and nonnegative at every level if and only if
  `|δ| ∈ jonesLoopParameters`
  (`IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`,
  `markovTrace_inv_pow_nonneg_iff`).
* At `δ = 0`, both `tr n (x⋆ * x)` and `(-1) ^ n * tr n (x⋆ * x)` are nonnegative for every `n`
  and `x` (proved in `TauCeti.Algebra.TemperleyLieb.Positivity`:
  `IsMarkovTrace.map_star_mul_self_nonneg_of_eq_zero` and
  `IsMarkovTrace.neg_one_pow_mul_map_star_mul_self_nonneg_of_eq_zero`), while
  `0 ∉ jonesLoopParameters` (`zero_notMem_jonesLoopParameters`), showing that `0 < δ`, `δ < 0`,
  and `δ ≠ 0` cannot be dropped.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_neg_one_pow_mul_map_star_mul_self_neg`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.lt_floor_of_forall_neg_one_pow_nonneg`: failure of signed
  positivity from level `⌊π / arccos (-δ / 2)⌋₊` onward when `δ < 0` and `-δ` is inadmissible.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: **positivity at negative loop
  parameters**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_inv_pow_nonneg_iff`: **positivity of the normalized Markov
  trace** for real `δ ≠ 0`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Theorem 4.3.17 and Facts 4.4.14 (TB6).
-/

public section

namespace TauCeti.TemperleyLieb

open Real

namespace IsMarkovTrace

open scoped ComplexOrder

variable {δ : ℝ}
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Failure of signed positivity from level `k` on.** Let `δ < 0` with `-δ` inadmissible, and
put `k = ⌊π / arccos (-δ / 2)⌋`. On every number `n ≥ k` of strands the signed Hermitian form
`(-1) ^ n * tr n (x⋆ * x)` of a Markov trace takes a negative value. -/
theorem exists_neg_one_pow_mul_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : ⌊π / arccos (-δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, (-1 : ℂ) ^ n * tr n (star x * x) < 0 := by
  have hadd : ((-δ : ℝ) : ℂ) + (δ : ℂ) = 0 := by push_cast; ring
  have hadd' : (δ : ℂ) + ((-δ : ℝ) : ℂ) = 0 := by push_cast; ring
  have htr' := htr.neg_one_pow_smul_comp_signEquivOfAddEqZero hadd
  obtain ⟨y, hy⟩ := htr'.exists_map_star_mul_self_neg (neg_pos.mpr hδ) hδJ hn
  refine ⟨signEquivOfAddEqZero hadd n y, ?_⟩
  rwa [← htr.map_signEquivOfAddEqZero htr' hadd', map_mul, signEquivOfAddEqZero_star,
    signEquivOfAddEqZero_apply_self]

/-- **Necessity at negative loop parameters.** If `δ < 0` and the signed Hermitian forms
`(-1) ^ n * tr n (x⋆ * x)` of a Markov trace are nonnegative on every number of strands, then `-δ`
is an admissible Jones loop parameter. -/
theorem neg_mem_jonesLoopParameters_of_forall_neg_one_pow_nonneg
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0)
    (h : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    -δ ∈ jonesLoopParameters := by
  by_contra hδJ
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ le_rfl
  exact (h _ x).not_gt hx

/-- At an inadmissible negative loop parameter (`δ < 0` and `-δ ∉ jonesLoopParameters`), the signed
Hermitian form `(-1) ^ n * tr n (x⋆ * x)` on `n` strands can be nonnegative only below level
`⌊π / arccos (-δ / 2)⌋`. -/
theorem lt_floor_of_forall_neg_one_pow_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    n < ⌊π / arccos (-δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ (not_lt.1 hn)
  exact (h x).not_gt hx

/-- **Positivity at negative loop parameters.** For `δ < 0`, the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number of
strands if and only if `-δ` is an admissible Jones loop parameter,
`-δ = 2 cos (π / m)` for some `m ≥ 3` or `2 ≤ -δ`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  have hadd : ((-δ : ℝ) : ℂ) + (δ : ℂ) = 0 := by push_cast; ring
  have hadd' : (δ : ℂ) + ((-δ : ℝ) : ℂ) = 0 := by push_cast; ring
  have htr' := htr.neg_one_pow_smul_comp_signEquivOfAddEqZero hadd
  rw [← htr'.forall_map_star_mul_self_nonneg_iff (neg_pos.mpr hδ)]
  refine forall_congr' fun n ↦ ?_
  rw [(signEquivOfAddEqZero hadd' n).surjective.forall]
  refine forall_congr' fun x ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul,
    ← signEquivOfAddEqZero_star, ← map_mul, signEquivOfAddEqZero_apply_self]

/-- **Positivity of the normalized Markov trace** for arbitrary real `δ ≠ 0`: the normalized forms
`(δ : ℂ)⁻¹ ^ n * tr n (x⋆ * x)` are real and nonnegative on every number of strands if and only if
`|δ|` is an admissible Jones loop parameter. -/
theorem forall_inv_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (δ : ℂ)⁻¹ ^ n * tr n (star x * x)) ↔
      |δ| ∈ jonesLoopParameters := by
  have hscale : ∀ {r : ℝ}, 0 < r → ∀ z : ℂ, 0 ≤ (r : ℂ) * z ↔ 0 ≤ z := by
    intro r hr z
    simp [Complex.nonneg_iff, mul_nonneg_iff_of_pos_left hr, hr.ne', eq_comm]
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · rw [abs_of_neg hneg, ← htr.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hneg]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    have hpow : (δ : ℂ)⁻¹ ^ n = ((((-δ)⁻¹ ^ n : ℝ) : ℂ)) * (-1 : ℂ) ^ n := by
      have hd : (δ : ℂ) = (((-δ : ℝ) : ℂ)) * (-1 : ℂ) := by push_cast; ring
      rw [hd, mul_inv, inv_neg, inv_one, mul_pow]
      push_cast
      rfl
    rw [hpow, mul_assoc]
    exact hscale (pow_pos (inv_pos.mpr (neg_pos.mpr hneg)) n) _
  · rw [abs_of_pos hpos, ← htr.forall_map_star_mul_self_nonneg_iff hpos]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    have hpow : (δ : ℂ)⁻¹ ^ n = (((δ⁻¹ ^ n : ℝ) : ℂ)) := by push_cast; rfl
    rw [hpow]
    exact hscale (pow_pos (inv_pos.mpr hpos) n) _

end IsMarkovTrace

open scoped ComplexOrder in
/-- **Positivity at negative loop parameters** for the spin-model Markov trace. Let `δ < 0` and
let `q` be a unit with `δ = -(q + q⁻¹)`. Then `(-1) ^ n * markovTrace q hq (x⋆ * x)` is real and
nonnegative for every number of strands and every `x` if and only if `-δ` is an admissible Jones
loop parameter (`-δ ∈ {2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`). -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} (hδ : δ < 0) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * markovTrace q hq (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

open scoped ComplexOrder in
/-- **Positivity of the normalized spin-model Markov trace** for real `δ ≠ 0`:
`(δ : ℂ)⁻¹ ^ n * markovTrace q hq (x⋆ * x)` is real and nonnegative for every number of strands
and every `x` if and only if `|δ|` is an admissible Jones loop parameter. -/
theorem markovTrace_inv_pow_nonneg_iff {δ : ℝ} (hδ : δ ≠ 0) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (δ : ℂ)⁻¹ ^ n * markovTrace q hq (star x * x)) ↔
      |δ| ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_inv_pow_mul_map_star_mul_self_nonneg_iff hδ

end TauCeti.TemperleyLieb
