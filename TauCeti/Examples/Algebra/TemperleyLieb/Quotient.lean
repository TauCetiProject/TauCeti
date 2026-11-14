/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.Algebra.TemperleyLieb.Quotient.Tower

/-!
# Low-strand examples of positive Jones quotients and Markov formulas

Concrete checks on the positive Temperley–Lieb trace quotients `htr.Quotient n`, their path-algebra
models, their trace radicals versus Jacobson radicals, and the Markov formulas for Jones
projections:

1. **At `δ = 1` (`m = 3`, Dynkin graph `A_2`):** `Module.finrank ℂ (htr.Quotient n) = 1` for every
   `n : ℕ`.
2. **Trace radical vs. Jacobson radical at `δ = 1`, `n = 2`:** the Jones–Wenzl projection
   `jonesWenzl (1 : ℂ) 2` is a nonzero idempotent in `htr.traceRadical 2`, whereas the Jacobson
   radical of any ring contains no nonzero idempotents, so
   `htr.traceRadical 2 ≠ Ring.jacobson (TemperleyLieb ℂ 1 2)`.
3. **At `δ = √2` (`m = 4`, Dynkin graph `A_3`):** `Module.finrank ℂ (htr.Quotient 2) = 2` and
   `Module.finrank ℂ (htr.Quotient 3) = 4`.
4. **At `δ = 2` (infinite ray `A_∞`):** `walkTrace (hasse ℕ) 0 (genericPathWeight 2) 1 = 4` on
   `PathAlgebra ℂ (hasse ℕ) 0 2`, with `Module.finrank ℂ (htr.Quotient 2) = 2` and
   `Module.finrank ℂ (htr.Quotient 3) = 5`.
5. **Low-strand Markov formulas:** explicit evaluation of both the unnormalized and normalized
   Markov formulas on `1 : htr.Quotient 1` and `mk (e δ 0) : htr.Quotient 2`.
-/

public section

noncomputable section

namespace TauCeti.TemperleyLieb.QuotientExamples

open Real SimpleGraph

theorem one_mem_jonesLoopParameters : (1 : ℝ) ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inl ⟨3, le_rfl, by rw [Nat.cast_ofNat, cos_pi_div_three]; ring⟩

theorem sqrt_two_mem_jonesLoopParameters : √2 ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inl ⟨4, by omega, by rw [Nat.cast_ofNat, cos_pi_div_four]; ring⟩

theorem two_mem_jonesLoopParameters : (2 : ℝ) ∈ jonesLoopParameters :=
  mem_jonesLoopParameters.2 <| Or.inr le_rfl

private theorem eq_zero_of_isIdempotentElem_of_mem_jacobson {R : Type*} [Ring R] {p : R}
    (hp : IsIdempotentElem p) (hjac : p ∈ Ring.jacobson R) : p = 0 := by
  obtain ⟨z, hz⟩ :=
    (Ideal.mem_jacobson_iff.mp (Ideal.jacobson_bot (R := R) ▸ hjac)) (-1)
  have hzp : z * -1 * p + z = 1 := sub_eq_zero.mp ((Submodule.mem_bot R).mp hz)
  calc p = 1 * p := (one_mul p).symm
    _ = (z * -1 * p + z) * p := by rw [hzp]
    _ = 0 := by rw [add_mul, mul_assoc, hp.eq, mul_neg, mul_one, neg_mul, neg_add_cancel]

private theorem finrank_eq_sum_univ_card_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ : V) (n : ℕ) :
    (∑ v ∈ G.walkEndpoints v₀ n, Fintype.card (G.EndpointWalk v₀ n v) ^ 2) =
      ∑ v : V, Fintype.card (G.EndpointWalk v₀ n v) ^ 2 :=
  Finset.sum_subset (Finset.subset_univ _) fun v _ hv ↦ by
    have : IsEmpty (G.EndpointWalk v₀ n v) := ⟨fun p ↦ hv ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩)⟩
    simp [Fintype.card_eq_zero]

section LoopOne

private theorem neighborFinset_pathGraph_two_zero :
    (pathGraph 2).neighborFinset 0 = {1} := by
  ext x
  fin_cases x <;> simp [mem_neighborFinset, pathGraph_adj]

private theorem neighborFinset_pathGraph_two_one :
    (pathGraph 2).neighborFinset 1 = {0} := by
  ext x
  fin_cases x <;> simp [mem_neighborFinset, pathGraph_adj]

private theorem card_endpointWalk_pathGraph_two (n : ℕ) (v : Fin 2) :
    Fintype.card ((pathGraph 2).EndpointWalk 0 n v) = if v.val = n % 2 then 1 else 0 := by
  induction n generalizing v with
  | zero =>
    rw [card_endpointWalk_zero]
    fin_cases v <;> simp
  | succ n ih =>
    rw [card_endpointWalk_succ]
    fin_cases v
    · simp only [Fin.zero_eta, neighborFinset_pathGraph_two_zero, Finset.sum_singleton, ih,
        Fin.val_one]
      split_ifs <;> omega
    · simp only [Fin.mk_one, neighborFinset_pathGraph_two_one, Finset.sum_singleton, ih,
        Fin.val_zero]
      split_ifs <;> omega

/-- At `δ = 1` (`m = 3`), every positive Jones quotient `htr.Quotient n` is `1`-dimensional. -/
theorem finrank_quotient_one {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 : ℝ) : ℂ) tr) (n : ℕ) :
    letI : Fact (IsSelfAdjoint ((1 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 1⟩
    Module.finrank ℂ (htr.Quotient n) = 1 := by
  let _ : Fact (IsSelfAdjoint ((1 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 1⟩
  have hcos : (1 : ℝ) = 2 * cos (π / (3 : ℕ)) := by rw [Nat.cast_ofNat, cos_pi_div_three]; ring
  rw [htr.finrank_quotient_eq_sum_card_sq (pathGraph 2) (0 : Fin 2)
      (discretePathWeight_ne_zero (m := 3) le_rfl) (isSelfAdjoint_discretePathWeight 3)
      (fun v ↦ by rw [hcos]; exact sum_neighborFinset_discretePathWeight_sq (m := 3) le_rfl v)
      Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) n,
    finrank_eq_sum_univ_card_sq, Fin.sum_univ_two]
  simp_rw [card_endpointWalk_pathGraph_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]

/-- At `δ = 1` on `2` strands, `jonesWenzl 1 2` is a nonzero idempotent in `htr.traceRadical 2`, so
`htr.traceRadical 2` is strictly larger than (in particular unequal to) the Jacobson radical. -/
theorem traceRadical_two_ne_jacobson_at_one {tr : ∀ n : ℕ, TemperleyLieb ℂ 1 n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ 1 tr) :
    htr.traceRadical 2 ≠ Ring.jacobson (TemperleyLieb ℂ 1 2) := by
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ (1 : ℂ) k) := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
    interval_cases k
    · rw [qInt_one]; exact isUnit_one
    · rw [qInt_two]; exact isUnit_one
  have hq3 : qInt ℂ (1 : ℂ) 3 = 0 := by
    have h := qInt_add_two (R := ℂ) (1 : ℂ) 1
    rw [qInt_one, qInt_two] at h
    linear_combination h
  have hmem : jonesWenzl (1 : ℂ) 2 ∈ htr.traceRadical 2 :=
    (htr.jonesWenzl_mem_traceRadical_iff hunit).2 hq3
  have hne : jonesWenzl (1 : ℂ) 2 ≠ 0 := by
    intro h0
    have haug := aug_jonesWenzl (R := ℂ) (δ := 1) 2
    rw [h0, map_zero] at haug
    exact zero_ne_one haug
  intro heq
  exact hne (eq_zero_of_isIdempotentElem_of_mem_jacobson (isIdempotentElem_jonesWenzl hunit)
    (heq ▸ hmem))

end LoopOne

section LoopSqrtTwo

private theorem neighborFinset_pathGraph_three_zero :
    (pathGraph 3).neighborFinset 0 = {1} := by
  ext x
  fin_cases x <;> simp [mem_neighborFinset, pathGraph_adj]

private theorem neighborFinset_pathGraph_three_one :
    (pathGraph 3).neighborFinset 1 = {0, 2} := by
  ext x
  fin_cases x <;> simp [mem_neighborFinset, pathGraph_adj]

private theorem neighborFinset_pathGraph_three_two :
    (pathGraph 3).neighborFinset 2 = {1} := by
  ext x
  fin_cases x <;> simp [mem_neighborFinset, pathGraph_adj]

private theorem card_endpointWalk_pathGraph_three_two (v : Fin 3) :
    Fintype.card ((pathGraph 3).EndpointWalk 0 2 v) = if v = 1 then 0 else 1 := by
  fin_cases v <;>
    simp [card_endpointWalk_succ, neighborFinset_pathGraph_three_zero,
      neighborFinset_pathGraph_three_one, neighborFinset_pathGraph_three_two, pathGraph_adj,
      Finset.filter_singleton]

private theorem card_endpointWalk_pathGraph_three_three (v : Fin 3) :
    Fintype.card ((pathGraph 3).EndpointWalk 0 3 v) = if v = 1 then 2 else 0 := by
  fin_cases v <;>
    simp [card_endpointWalk_succ, neighborFinset_pathGraph_three_zero,
      neighborFinset_pathGraph_three_one, neighborFinset_pathGraph_three_two, pathGraph_adj,
      Finset.filter_singleton]

/-- At `δ = √2` (`m = 4`), `htr.Quotient 2` has dimension `2` (`ℂ ⊕ ℂ`). -/
theorem finrank_quotient_sqrt_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) :
    letI : Fact (IsSelfAdjoint ((√2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal _⟩
    Module.finrank ℂ (htr.Quotient 2) = 2 := by
  let _ : Fact (IsSelfAdjoint ((√2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal _⟩
  have hcos : √2 = 2 * cos (π / (4 : ℕ)) := by rw [Nat.cast_ofNat, cos_pi_div_four]; ring
  rw [htr.finrank_quotient_eq_sum_card_sq (pathGraph 3) (0 : Fin 3)
      (discretePathWeight_ne_zero (m := 4) (by omega)) (isSelfAdjoint_discretePathWeight 4)
      (fun v ↦ by rw [hcos]; exact sum_neighborFinset_discretePathWeight_sq (m := 4) (by omega) v)
      Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) 2,
    finrank_eq_sum_univ_card_sq, Fin.sum_univ_three]
  simp [card_endpointWalk_pathGraph_three_two]

/-- At `δ = √2` (`m = 4`), `htr.Quotient 3` has dimension `4` (`M₂(ℂ)`, killing the `1`-dimensional
Jones–Wenzl ideal of the `5`-dimensional algebra `TemperleyLieb ℂ √2 3`). -/
theorem finrank_quotient_sqrt_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) :
    letI : Fact (IsSelfAdjoint ((√2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal _⟩
    Module.finrank ℂ (htr.Quotient 3) = 4 := by
  let _ : Fact (IsSelfAdjoint ((√2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal _⟩
  have hcos : √2 = 2 * cos (π / (4 : ℕ)) := by rw [Nat.cast_ofNat, cos_pi_div_four]; ring
  rw [htr.finrank_quotient_eq_sum_card_sq (pathGraph 3) (0 : Fin 3)
      (discretePathWeight_ne_zero (m := 4) (by omega)) (isSelfAdjoint_discretePathWeight 4)
      (fun v ↦ by rw [hcos]; exact sum_neighborFinset_discretePathWeight_sq (m := 4) (by omega) v)
      Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) 3,
    finrank_eq_sum_univ_card_sq, Fin.sum_univ_three]
  simp [card_endpointWalk_pathGraph_three_three]

end LoopSqrtTwo

section LoopTwo

/-- At `δ = 2` on `n = 2` strands, `walkTrace` of the identity in `PathAlgebra ℂ (hasse ℕ) 0 2`
evaluates to `2 ^ 2 = 4`. -/
theorem walkTrace_one_hasse_two :
    walkTrace (hasse ℕ) 0 (genericPathWeight 2) (1 : PathAlgebra ℂ (hasse ℕ) 0 2) = 4 := by
  rw [walkTrace_one (genericPathWeight_ne_zero (δ := 2) le_rfl)
    (sum_neighborFinset_genericPathWeight_sq (δ := 2) le_rfl)]
  norm_num

private theorem walkEndpoints_hasse_two : (hasse ℕ).walkEndpoints 0 2 = {0, 2} := by
  rw [walkEndpoints_succ, walkEndpoints_succ, walkEndpoints_zero, Finset.singleton_biUnion,
    neighborFinset_hasse_nat_zero, Finset.singleton_biUnion, neighborFinset_hasse_nat_succ]

private theorem walkEndpoints_hasse_three : (hasse ℕ).walkEndpoints 0 3 = {1, 3} := by
  rw [walkEndpoints_succ, walkEndpoints_hasse_two]
  ext x
  simp [neighborFinset_hasse_nat_zero, neighborFinset_hasse_nat_succ]

private theorem card_endpointWalk_hasse_one (v : ℕ) :
    Fintype.card ((hasse ℕ).EndpointWalk 0 1 v) = if v = 1 then 1 else 0 := by
  cases v with
  | zero => simp [card_endpointWalk_succ, neighborFinset_hasse_nat_zero]
  | succ k =>
    rw [card_endpointWalk_succ, neighborFinset_hasse_nat_succ, Finset.sum_pair (by omega)]
    cases k <;> simp

private theorem card_endpointWalk_hasse_two_zero :
    Fintype.card ((hasse ℕ).EndpointWalk 0 2 0) = 1 := by
  simp [card_endpointWalk_succ, neighborFinset_hasse_nat_zero]

private theorem card_endpointWalk_hasse_two_two :
    Fintype.card ((hasse ℕ).EndpointWalk 0 2 2) = 1 := by
  rw [card_endpointWalk_succ, neighborFinset_hasse_nat_succ 1, Finset.sum_pair (by omega)]
  simp [card_endpointWalk_hasse_one]

private theorem card_endpointWalk_hasse_two_four :
    Fintype.card ((hasse ℕ).EndpointWalk 0 2 4) = 0 := by
  rw [card_endpointWalk_succ, neighborFinset_hasse_nat_succ 3, Finset.sum_pair (by omega)]
  simp [card_endpointWalk_hasse_one]

/-- At `δ = 2`, `htr.Quotient 2` has dimension `2`. -/
theorem finrank_quotient_two_two {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) :
    letI : Fact (IsSelfAdjoint ((2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 2⟩
    Module.finrank ℂ (htr.Quotient 2) = 2 := by
  let _ : Fact (IsSelfAdjoint ((2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 2⟩
  rw [htr.finrank_quotient_eq_sum_card_sq (hasse ℕ) 0
      (genericPathWeight_ne_zero (δ := 2) le_rfl) (isSelfAdjoint_genericPathWeight 2)
      (sum_neighborFinset_genericPathWeight_sq (δ := 2) le_rfl)
      Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) 2,
    walkEndpoints_hasse_two, Finset.sum_pair (by omega),
    card_endpointWalk_hasse_two_zero, card_endpointWalk_hasse_two_two]
  norm_num

/-- At `δ = 2`, `htr.Quotient 3` has dimension `5` (`M₂(ℂ) ⊕ ℂ`, matching the Catalan number
`C_3 = 5`). -/
theorem finrank_quotient_two_three {tr : ∀ n : ℕ, TemperleyLieb ℂ ((2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((2 : ℝ) : ℂ) tr) :
    letI : Fact (IsSelfAdjoint ((2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 2⟩
    Module.finrank ℂ (htr.Quotient 3) = 5 := by
  let _ : Fact (IsSelfAdjoint ((2 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 2⟩
  have hc1 : Fintype.card ((hasse ℕ).EndpointWalk 0 3 1) = 2 := by
    rw [card_endpointWalk_succ, neighborFinset_hasse_nat_succ 0, Finset.sum_pair (by omega),
      card_endpointWalk_hasse_two_zero, card_endpointWalk_hasse_two_two]
  have hc3 : Fintype.card ((hasse ℕ).EndpointWalk 0 3 3) = 1 := by
    rw [card_endpointWalk_succ, neighborFinset_hasse_nat_succ 2, Finset.sum_pair (by omega),
      card_endpointWalk_hasse_two_two, card_endpointWalk_hasse_two_four]
  rw [htr.finrank_quotient_eq_sum_card_sq (hasse ℕ) 0
      (genericPathWeight_ne_zero (δ := 2) le_rfl) (isSelfAdjoint_genericPathWeight 2)
      (sum_neighborFinset_genericPathWeight_sq (δ := 2) le_rfl)
      Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) 3,
    walkEndpoints_hasse_three, Finset.sum_pair (by omega), hc1, hc3]
  norm_num

end LoopTwo

section MarkovChecks

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ ∈ jonesLoopParameters)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)

/-- Low-strand check (`n = 1`, `x = 1`): `τ_2 (p_0) = δ⁻¹ * τ_1 (1) = 1` and
`tr_2 (p_0) = δ⁻²`. -/
theorem markov_check_one_unit :
    htr.positiveQuotientTrace hδ 2 (htr.jonesProjection 0) = 1 ∧
      htr.normalizedQuotientTrace hδ 2 (htr.jonesProjection 0) = (δ : ℂ)⁻¹ ^ 2 := by
  have hδc : (δ : ℂ) ≠ 0 := (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  have h1 := htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection hδ (1 : htr.Quotient 1)
  rw [map_one, one_mul, htr.positiveQuotientTrace_one, pow_one, inv_mul_cancel₀ hδc] at h1
  have h2 := htr.normalizedQuotientTrace_jonesStrandIncl_mul_jonesProjection hδ (1 : htr.Quotient 1)
  rw [map_one, one_mul, htr.normalizedQuotientTrace_one, mul_one] at h2
  exact ⟨h1, h2⟩

/-- Low-strand check (`n = 2`, `x = mk (e δ 0)`): `τ_3 (ι (mk (e δ 0)) * p_1) = 1` and
`tr_3 (ι (mk (e δ 0)) * p_1) = δ⁻³`. -/
theorem markov_check_two_generator :
    let x : htr.Quotient 2 := Ideal.Quotient.mk (htr.traceRadical 2) (e (δ : ℂ) 0)
    htr.positiveQuotientTrace hδ 3 (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) = 1 ∧
      htr.normalizedQuotientTrace hδ 3 (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) =
        (δ : ℂ)⁻¹ ^ 3 := by
  intro x
  have hδc : (δ : ℂ) ≠ 0 := (IsMarkovTrace.isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  have htrx : htr.positiveQuotientTrace hδ 2 x = (δ : ℂ) := by
    rw [htr.positiveQuotientTrace_mk]
    have he : e (δ : ℂ) (0 : Fin 1) =
        strandIncl (1 : TemperleyLieb ℂ (δ : ℂ) 1) * e (δ : ℂ) (Fin.last 0) := by
      rw [map_one, one_mul]; rfl
    rw [he, htr.map_strandIncl_mul_e_last, htr.map_one, pow_one]
  have h1 : htr.positiveQuotientTrace hδ 3
      (htr.jonesStrandIncl hδ 2 x * htr.jonesProjection 1) = 1 := by
    rw [htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection, htrx, inv_mul_cancel₀ hδc]
  refine ⟨h1, ?_⟩
  rw [htr.normalizedQuotientTrace_apply, h1, mul_one]

end MarkovChecks

end TauCeti.TemperleyLieb.QuotientExamples
