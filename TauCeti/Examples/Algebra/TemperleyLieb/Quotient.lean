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
theorem one_mem_jonesLoopParameters : (1 : ℝ) ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inl ⟨3, le_rfl, by rw [Nat.cast_ofNat, cos_pi_div_three]; ring⟩
theorem sqrt_two_mem_jonesLoopParameters : √2 ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inl ⟨4, by omega, by rw [Nat.cast_ofNat, cos_pi_div_four]; ring⟩
theorem two_mem_jonesLoopParameters : (2 : ℝ) ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inr le_rfl
private theorem card_endpointWalk_pathGraph_two (n : ℕ) (v : Fin 2) :
    Fintype.card ((pathGraph 2).EndpointWalk 0 n v) = if v.val = n % 2 then 1 else 0 := by
  induction n generalizing v with
  | zero => rw [card_endpointWalk_zero]; fin_cases v <;> simp
  | succ n ih =>
    rw [card_endpointWalk_succ]
    have h0 : (pathGraph 2).neighborFinset 0 = {1} := by decide
    have h1 : (pathGraph 2).neighborFinset 1 = {0} := by decide
    fin_cases v <;> simp only [Fin.zero_eta, Fin.mk_one, h0, h1, Finset.sum_singleton, ih,
      Fin.val_zero, Fin.val_one] <;> split_ifs <;> omega
private theorem finrank_pathAlgebra_fintype {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [LocallyFinite G] (v₀ : V) (n : ℕ) :
    Module.finrank ℂ (PathAlgebra ℂ G v₀ n) =
      ∑ v : V, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 := by
  rw [PathAlgebra.finrank]
  exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv ↦ by
    have : IsEmpty (G.EndpointWalk v₀ n v) := ⟨fun p ↦ hv ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩)⟩
    simp [Fintype.card_eq_zero]
theorem finrank_quotient_one {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 : ℝ) : ℂ) tr) (n : ℕ) :
    Module.finrank ℂ (htr.Quotient n) = 1 := by
  have hcos : (1 : ℝ) = 2 * cos (π / (3 : ℕ)) := by rw [Nat.cast_ofNat, cos_pi_div_three]; ring
  rw [(htr.discreteQuotientEquiv (m := 3) le_rfl hcos n).toAlgEquiv.toLinearEquiv.finrank_eq,
    finrank_pathAlgebra_fintype, Fin.sum_univ_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [card_endpointWalk_pathGraph_two, hn]
theorem traceRadical_two_ne_jacobson_at_one {tr : ∀ n : ℕ, TemperleyLieb ℂ 1 n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ 1 tr) :
    htr.traceRadical 2 ≠ Ring.jacobson (TemperleyLieb ℂ 1 2) := by
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ (1 : ℂ) k) := fun k hk ↦ by
    rcases Finset.mem_Icc.1 hk with ⟨_, _⟩; interval_cases k <;> simp [qInt_one, qInt_two]
  have hq3 : qInt ℂ (1 : ℂ) 3 = 0 := by
    have h := qInt_add_two (R := ℂ) (1 : ℂ) 1; rw [qInt_one, qInt_two] at h; linear_combination h
  have hmem : jonesWenzl (1 : ℂ) 2 ∈ htr.traceRadical 2 :=
    (htr.jonesWenzl_mem_traceRadical_iff hunit).2 hq3
  intro heq
  obtain ⟨z, hz⟩ :=
    (Ideal.mem_jacobson_iff.mp (Ideal.jacobson_bot (R := TemperleyLieb ℂ 1 2) ▸ heq ▸ hmem)) (-1)
  have hzp : z * -1 * jonesWenzl (1 : ℂ) 2 + z = 1 :=
    sub_eq_zero.mp ((Submodule.mem_bot (TemperleyLieb ℂ 1 2)).mp hz)
  have hmul := (congrArg (· * jonesWenzl (1 : ℂ) 2) hzp).symm
  rw [one_mul, add_mul, mul_assoc, (isIdempotentElem_jonesWenzl hunit).eq, mul_neg, mul_one,
    neg_mul, neg_add_cancel] at hmul
  have haug := aug_jonesWenzl (R := ℂ) (δ := 1) 2; rw [hmul, map_zero] at haug
  exact zero_ne_one haug
private theorem sqrt_two_eq_two_mul_cos : √2 = 2 * cos (π / (4 : ℕ)) := by
  rw [Nat.cast_ofNat, cos_pi_div_four]; ring
private theorem finrank_pathAlgebra_pathGraph_three :
    Module.finrank ℂ (PathAlgebra ℂ (pathGraph 3) 0 2) = 2 ∧
      Module.finrank ℂ (PathAlgebra ℂ (pathGraph 3) 0 3) = 4 := by
  have h0 : (pathGraph 3).neighborFinset 0 = {1} := by decide
  have h1 : (pathGraph 3).neighborFinset 1 = {0, 2} := by decide
  have h2 : (pathGraph 3).neighborFinset 2 = {1} := by decide
  simp only [finrank_pathAlgebra_fintype, Fin.sum_univ_three, card_endpointWalk_succ,
    card_endpointWalk_zero, h0, h1, h2, Finset.sum_singleton,
    Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
  decide
theorem finrank_quotient_sqrt_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 2) = 2 :=
  (htr.discreteQuotientEquiv (m := 4) (by omega) sqrt_two_eq_two_mul_cos 2)
    |>.toAlgEquiv.toLinearEquiv.finrank_eq.trans finrank_pathAlgebra_pathGraph_three.1
theorem finrank_quotient_sqrt_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 3) = 4 :=
  (htr.discreteQuotientEquiv (m := 4) (by omega) sqrt_two_eq_two_mul_cos 3)
    |>.toAlgEquiv.toLinearEquiv.finrank_eq.trans finrank_pathAlgebra_pathGraph_three.2
theorem walkTrace_one_hasse_two :
    walkTrace (hasse ℕ) 0 (genericPathWeight 2) (1 : PathAlgebra ℂ (hasse ℕ) 0 2) = 4 := by
  rw [walkTrace_one (genericPathWeight_ne_zero (δ := 2) le_rfl)
    (sum_neighborFinset_genericPathWeight_sq (δ := 2) le_rfl)]; norm_num
private theorem finrank_pathAlgebra_hasse :
    Module.finrank ℂ (PathAlgebra ℂ (hasse ℕ) 0 2) = 2 ∧
      Module.finrank ℂ (PathAlgebra ℂ (hasse ℕ) 0 3) = 5 := by
  have hw2 : (hasse ℕ).walkEndpoints 0 2 = {0, 2} := by ext; simp [walkEndpoints_succ]
  have hw3 : (hasse ℕ).walkEndpoints 0 3 = {1, 3} := by rw [walkEndpoints_succ, hw2]; ext; simp
  simp only [PathAlgebra.finrank, hw2, hw3, card_endpointWalk_succ, card_endpointWalk_zero,
    neighborFinset_hasse_nat_zero, neighborFinset_hasse_nat_succ, Finset.sum_singleton,
    Finset.sum_pair (by decide : 0 ≠ 2), Finset.sum_pair (by decide : 1 ≠ 3),
    Finset.sum_pair (by decide : 2 ≠ 4)]
  decide
theorem finrank_quotient_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 2) = 2 :=
  (htr.genericQuotientEquiv (δ := 2) le_rfl 2).toAlgEquiv.toLinearEquiv.finrank_eq.trans
    finrank_pathAlgebra_hasse.1
theorem finrank_quotient_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) : Module.finrank ℂ (htr.Quotient 3) = 5 :=
  (htr.genericQuotientEquiv (δ := 2) le_rfl 3).toAlgEquiv.toLinearEquiv.finrank_eq.trans
    finrank_pathAlgebra_hasse.2
section MarkovChecks
variable {δ : ℝ} (hδ : δ ∈ jonesLoopParameters)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
theorem markov_check_one_unit :
    htr.positiveQuotientTrace hδ 2 (htr.jonesProjection 0) = 1 ∧
      htr.normalizedQuotientTrace hδ 2 (htr.jonesProjection 0) = (δ : ℂ)⁻¹ ^ 2 := by
  have h1 := htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection hδ (1 : htr.Quotient 1)
  rw [map_one, one_mul, htr.positiveQuotientTrace_one, pow_one,
    inv_mul_cancel₀ (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero] at h1
  exact ⟨h1, by rw [htr.normalizedQuotientTrace_apply, h1, mul_one]⟩
theorem markov_check_two_generator :
    let x : htr.Quotient 2 := Ideal.Quotient.mk (htr.traceRadical 2) (e (δ : ℂ) 0)
    htr.positiveQuotientTrace hδ 3 (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) = 1 ∧
      htr.normalizedQuotientTrace hδ 3 (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) =
        (δ : ℂ)⁻¹ ^ 3 := by
  intro x; have he0 : e (δ : ℂ) (0 : Fin 1) =
      strandIncl (1 : TemperleyLieb ℂ (δ : ℂ) 1) * e (δ : ℂ) (Fin.last 0) := by
    rw [map_one, one_mul]; rfl
  have h1 : htr.positiveQuotientTrace hδ 3
      (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) = 1 := by
    rw [htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection, htr.positiveQuotientTrace_mk,
      he0, htr.map_strandIncl_mul_e_last, htr.map_one, pow_one,
      inv_mul_cancel₀ (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero]
  exact ⟨h1, by rw [htr.normalizedQuotientTrace_apply, h1, mul_one]⟩
end MarkovChecks
end TauCeti.TemperleyLieb.QuotientExamples
