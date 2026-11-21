/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.Algebra.TemperleyLieb.Quotient.Tower
/-! # Low-strand examples of positive Jones quotients and Markov formulas

Concrete checks on positive Temperley–Lieb trace quotients `htr.Quotient n`, their path-algebra
models at `δ = 1` (`A_2`), `δ = √2` (`A_3`), and `δ = 2` (`A_∞`), trace radicals versus Jacobson
radicals (`traceRadical_two_ne_jacobson_at_one`), and low-strand Markov formulas. -/
public section
noncomputable section
namespace TauCeti.TemperleyLieb.QuotientExamples
open Real SimpleGraph
local instance (x : ℝ) : Fact (IsSelfAdjoint (x : ℂ)) := ⟨Complex.conj_ofReal x⟩
/-- At `δ = 1` (`A_2`), every positive Jones quotient `htr.Quotient n` is `1`-dimensional. -/
theorem finrank_quotient_one {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 : ℝ) : ℂ) tr) (n : ℕ) : Module.finrank ℂ (htr.Quotient n) = 1 := by
  rw [(htr.discreteQuotientEquiv (m := 3) (by omega)
      (by rw [Nat.cast_ofNat, cos_pi_div_three]; ring) n).toAlgEquiv.toLinearEquiv.finrank_eq,
    PathAlgebra.finrank_fintype, Fin.sum_univ_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [card_endpointWalk_pathGraph_two, hn]
/-- At `δ = 1` on `2` strands, `f_2` lies in `htr.traceRadical 2` but not the Jacobson radical. -/
theorem traceRadical_two_ne_jacobson_at_one {tr : ∀ n : ℕ, TemperleyLieb ℂ 1 n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ 1 tr) : htr.traceRadical 2 ≠ Ring.jacobson (TemperleyLieb ℂ 1 2) := by
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ (1 : ℂ) k) := fun k hk ↦ by
    rcases Finset.mem_Icc.1 hk with ⟨_, _⟩; interval_cases k <;> simp [qInt_one, qInt_two]
  have hmem : jonesWenzl (1 : ℂ) 2 ∈ htr.traceRadical 2 :=
    (htr.jonesWenzl_mem_traceRadical_iff hunit).2 <| by
      have h := qInt_add_two (R := ℂ) (1 : ℂ) 1; rw [qInt_one, qInt_two] at h; linear_combination h
  intro heq; rw [heq, ← Ideal.jacobson_bot] at hmem
  obtain ⟨z, hz⟩ := Ideal.mem_jacobson_iff.mp hmem (-1)
  have hmul := congrArg (· * jonesWenzl (1 : ℂ) 2)
    (sub_eq_zero.mp ((Submodule.mem_bot (TemperleyLieb ℂ 1 2)).1 hz))
  rw [one_mul, add_mul, mul_assoc, (isIdempotentElem_jonesWenzl hunit).eq, mul_neg, mul_one,
    neg_mul, neg_add_cancel] at hmul
  exact zero_ne_one (α := ℂ) (by simpa [← hmul] using aug_jonesWenzl (R := ℂ) (δ := 1) 2)
private theorem sqrt_two_eq_two_mul_cos : √2 = 2 * cos (π / (4 : ℕ)) := by
  rw [Nat.cast_ofNat, cos_pi_div_four]; ring
private theorem finrank_pathAlgebra_pathGraph_three :
    Module.finrank ℂ (PathAlgebra ℂ (pathGraph 3) 0 2) = 2 ∧
      Module.finrank ℂ (PathAlgebra ℂ (pathGraph 3) 0 3) = 4 := by
  simp only [PathAlgebra.finrank_fintype, Fin.sum_univ_three, card_endpointWalk_succ,
    card_endpointWalk_zero, (by decide : (pathGraph 3).neighborFinset 0 = {1}),
    (by decide : (pathGraph 3).neighborFinset 1 = {0, 2}),
    (by decide : (pathGraph 3).neighborFinset 2 = {1}), Finset.sum_singleton,
    Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]; decide
/-- At `δ = √2` (`A_3`), `htr.Quotient 2` has dimension `2`. -/
theorem finrank_quotient_sqrt_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 2) = 2 :=
  (htr.discreteQuotientEquiv (m := 4) (by omega) sqrt_two_eq_two_mul_cos 2
    |>.toAlgEquiv.toLinearEquiv.finrank_eq).trans finrank_pathAlgebra_pathGraph_three.1
/-- At `δ = √2` (`A_3`), `htr.Quotient 3` has dimension `4` (dropping from the full `5`). -/
theorem finrank_quotient_sqrt_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 3) = 4 :=
  (htr.discreteQuotientEquiv (m := 4) (by omega) sqrt_two_eq_two_mul_cos 3
    |>.toAlgEquiv.toLinearEquiv.finrank_eq).trans finrank_pathAlgebra_pathGraph_three.2
/-- On `A_∞` (`hasse ℕ`) at `δ = 2`, the `2`-step path trace of `1` equals `4`. -/
theorem walkTrace_one_hasse_two :
    walkTrace (hasse ℕ) 0 (genericPathWeight 2) (1 : PathAlgebra ℂ (hasse ℕ) 0 2) = 4 := by
  rw [walkTrace_one (genericPathWeight_ne_zero (δ := 2) le_rfl 0)
    (sum_neighborFinset_genericPathWeight_sq (δ := 2) le_rfl)]; norm_num
private theorem finrank_pathAlgebra_hasse :
    Module.finrank ℂ (PathAlgebra ℂ (hasse ℕ) 0 2) = 2 ∧
      Module.finrank ℂ (PathAlgebra ℂ (hasse ℕ) 0 3) = 5 := by
  have hw2 : (hasse ℕ).walkEndpoints 0 2 = {0, 2} := by ext; simp [walkEndpoints_succ]
  have hw3 : (hasse ℕ).walkEndpoints 0 3 = {1, 3} := by rw [walkEndpoints_succ, hw2]; ext; simp
  simp only [PathAlgebra.finrank, hw2, hw3, card_endpointWalk_succ, card_endpointWalk_zero,
    neighborFinset_hasse_nat_zero, neighborFinset_hasse_nat_succ, Finset.sum_singleton,
    Finset.sum_pair (by decide : 0 ≠ 2), Finset.sum_pair (by decide : 1 ≠ 3),
    Finset.sum_pair (by decide : 2 ≠ 4)]; decide
/-- At `δ = 2` (`A_∞`), `htr.Quotient 2` has dimension `2`. -/
theorem finrank_quotient_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 2) = 2 :=
  (htr.genericQuotientEquiv (δ := 2) le_rfl 2).toAlgEquiv.toLinearEquiv.finrank_eq.trans
    finrank_pathAlgebra_hasse.1
/-- At `δ = 2` (`A_∞`), `htr.Quotient 3` has full Catalan dimension `5`. -/
theorem finrank_quotient_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 3) = 5 :=
  (htr.genericQuotientEquiv (δ := 2) le_rfl 3).toAlgEquiv.toLinearEquiv.finrank_eq.trans
    finrank_pathAlgebra_hasse.2
section MarkovChecks
variable {δ : ℝ} (hδ : δ ∈ jonesLoopParameters)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- Unnormalized and normalized Markov trace values of the first Jones projection `p_0`. -/
theorem markov_check_one_unit :
    htr.positiveQuotientTrace hδ 2 (htr.jonesProjection 0) = 1 ∧
      htr.normalizedQuotientTrace hδ 2 (htr.jonesProjection 0) = (δ : ℂ)⁻¹ ^ 2 := by
  have h1 := htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection hδ (1 : htr.Quotient 1)
  rw [map_one, one_mul, htr.positiveQuotientTrace_one, pow_one,
    inv_mul_cancel₀ (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero] at h1
  exact ⟨h1, by rw [htr.normalizedQuotientTrace_apply, h1, mul_one]⟩
/-- Unnormalized and normalized Markov trace values of `e_0 * p_1` on `3` strands. -/
theorem markov_check_two_generator :
    let x : htr.Quotient 2 := Ideal.Quotient.mk (htr.traceRadical 2) (e (δ : ℂ) 0)
    htr.positiveQuotientTrace hδ 3 (htr.jonesStrandIncl 2 x * htr.jonesProjection 1) = 1 ∧
      htr.normalizedQuotientTrace hδ 3 (htr.jonesStrandIncl 2 x * htr.jonesProjection 1) =
        (δ : ℂ)⁻¹ ^ 3 := by
  intro x; have h1 := htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection hδ x
  have he : tr 2 (e (δ : ℂ) 0) = (δ : ℂ) := by
    simpa [htr.map_one] using htr.map_strandIncl_mul_e_last 0 1
  rw [htr.positiveQuotientTrace_mk, he,
    inv_mul_cancel₀ (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero] at h1
  exact ⟨h1, by rw [htr.normalizedQuotientTrace_apply, h1, mul_one]⟩
end MarkovChecks
end TauCeti.TemperleyLieb.QuotientExamples
