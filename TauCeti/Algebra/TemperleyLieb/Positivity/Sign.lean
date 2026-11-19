/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Sign

/-!
# Positivity at negative loop parameters

The sign isomorphism `TauCeti.TemperleyLieb.signEquiv : TL_n(δ) ≃ₐ TL_n(-δ)` preserves the analytic
adjoint and intertwines Markov traces up to the sign `(-1) ^ n`. Combined with Jones's positivity
theorem at the positive loop value `-δ`, this classifies the negative loop values with positive
signed closure forms: for real `δ < 0`, the forms `(-1) ^ n * tr n (x⋆ * x)` are real and
nonnegative on every number of strands exactly when `-δ` is an admissible loop parameter,
`-δ = 2 cos (π / m)` for some `m ≥ 3` or `-δ ≥ 2`. The sign `(-1) ^ n` cannot be dropped: on one
strand the unsigned form is `tr 1 1 = δ < 0`.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: **positivity at negative loop
  parameters**.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Facts 4.4.14, for the signed
  closure forms at negative loop values.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
-/

public section

namespace TauCeti.TemperleyLieb

open scoped ComplexOrder

namespace IsMarkovTrace

/-- Positivity of the signed Hermitian forms at a loop value `c = -d`, stated for an arbitrary
complex `c` equal to `-d` so that it applies to the coercion of a negative real loop value. -/
private theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff_of_eq_neg {c : ℂ}
    [Fact (IsSelfAdjoint c)] {tr : ∀ n : ℕ, TemperleyLieb ℂ c n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ c tr) {d : ℝ} (h : c = -(d : ℂ)) (hd : 0 < d) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ c n), 0 ≤ (-1) ^ n * tr n (star x * x)) ↔
      d ∈ jonesLoopParameters := by
  subst h
  have : Fact (IsSelfAdjoint (d : ℂ)) := ⟨Complex.conj_ofReal _⟩
  rw [← htr.neg_one_pow_smul_comp_signEquiv.forall_map_star_mul_self_nonneg_iff hd]
  refine forall_congr' fun n ↦
    ((signEquiv (d : ℂ) n).surjective.forall).trans (forall_congr' fun x ↦ ?_)
  simp [signEquiv_star]

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Positivity at negative loop parameters.** For `δ < 0`, the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number
`n` of strands exactly when `-δ` is an admissible loop parameter, `-δ = 2 cos (π / m)` for some
`m ≥ 3` or `-δ ≥ 2`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  htr.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff_of_eq_neg (by push_cast; ring)
    (neg_pos.2 hδ)

end IsMarkovTrace

/-- **Positivity at negative loop parameters** for the spin-model trace. Let `δ < 0` and let `q` be
a unit with `δ = -(q + q⁻¹)`. Then the signed closure forms
`(-1) ^ n * TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` are real and nonnegative for every
number `n` of strands and every `x` exactly when `-δ` is an admissible loop parameter. -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ < 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1) ^ n * markovTrace q hq (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

end TauCeti.TemperleyLieb
