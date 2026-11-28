/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Basic.Real.Basic

import Mathlib.Data.Finsupp.PWO
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted polynomial reduction modulo low-cost power relations

This file proves the Dickson well-foundedness and weighted reduction lemma used in the weighted
Combinatorial Nullstellensatz with multiplicity:

* TauCeti.mem_of_forall_monomial_mem: a submodule of MvPolynomial ι R containing every
  monomial monomial α 1 in the support of p contains p.
* TauCeti.wellFounded_lt_of_monotone_finsupp: comparing exponents in ι →₀ ℕ (for finite ι)
  by a monotone real function is well founded.
* TauCeti.monomial_mul_aeval_mem_of_weight_le: if each g u has all monomials of weighted cost
  < 1 for weights (κ u : ℝ)⁻¹, then any submodule containing all X ^ α * ψ ^ γ with
  α u < κ u and γ.degree + cost α ≤ r (where ψ u = X u ^ κ u - g u) contains all such
  products with γ.degree + cost α ≤ r.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207), file src/Lib/General/Algebra/MultivariatePolynomials.lean
(New.mem_of_forall_monomial_mem, New.wellFounded_lt_of_monotone_finsupp,
New.monomial_mul_bind₁_mem_of_weight_le).
-/

public section

open MvPolynomial Finsupp Submodule

namespace TauCeti

/-- A submodule that contains every monomial monomial α 1 occurring in p contains p. -/
theorem mem_of_forall_monomial_mem {R ι : Type*} [CommSemiring R]
    {N : Submodule R (MvPolynomial ι R)} {p : MvPolynomial ι R}
    (h_monomial : ∀ α ∈ p.support, monomial α 1 ∈ N) : p ∈ N := by
  rw [p.as_sum]
  exact N.sum_mem fun α hα ↦ by simpa [smul_monomial] using N.smul_mem _ (h_monomial α hα)

/-- Comparing exponents in ι →₀ ℕ by a monotone real function is well founded (Dickson's
lemma). -/
theorem wellFounded_lt_of_monotone_finsupp {ι : Type*} [Finite ι] {c : (ι →₀ ℕ) → ℝ}
    (hc : Monotone c) : WellFounded fun α β : ι →₀ ℕ ↦ c α < c β := by
  let e : (fun α β : ι →₀ ℕ ↦ α ≤ β) →r fun α β : ι →₀ ℕ ↦ c α ≤ c β := ⟨id, fun h_le ↦ hc h_le⟩
  have h_wqo : WellQuasiOrdered fun α β : ι →₀ ℕ ↦ c α ≤ c β :=
    wellQuasiOrdered_le.of_surjective e Function.surjective_id
  simpa only [lt_iff_le_not_ge] using h_wqo.wellFounded

/-- Weighted division by ψ u = X u ^ κ u - g u, where variable u has cost 1 / κ u and every
monomial of g u has cost < 1. If a submodule N contains X ^ α * ψ ^ γ whenever α u < κ u
for all u and γ.degree + cost α ≤ r, then it contains all such products with
γ.degree + cost α ≤ r. -/
theorem monomial_mul_aeval_mem_of_weight_le {R ι : Type*} [CommRing R] [Finite ι] {κ : ι → ℕ}
    (hκ : ∀ u : ι, 0 < κ u) {g : ι → MvPolynomial ι R}
    (hg : ∀ u : ι, ∀ α ∈ (g u).support, weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α < 1)
    {N : Submodule R (MvPolynomial ι R)} {r : ℝ}
    (hN : ∀ α γ : ι →₀ ℕ, (∀ u : ι, α u < κ u) →
      γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r →
      monomial α 1 * aeval (R := R) (fun u : ι ↦ X u ^ κ u - g u) (monomial γ 1) ∈ N)
    (α γ : ι →₀ ℕ) (h_le : γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r) :
    monomial α 1 * aeval (R := R) (fun u : ι ↦ X u ^ κ u - g u) (monomial γ 1) ∈ N := by
  classical
  have := Fintype.ofFinite ι
  set cost : (ι →₀ ℕ) →+ ℝ := weight (fun u : ι ↦ (κ u : ℝ))⁻¹ with h_cost
  have h_mono : Monotone cost := fun α β h_exp ↦ by
    simp only [h_cost, weight_eq_sum, Pi.inv_apply]
    gcongr with u
    exact h_exp u
  let b (α γ : ι →₀ ℕ) : MvPolynomial ι R :=
    monomial α 1 * aeval (R := R) (fun u : ι ↦ X u ^ κ u - g u) (monomial γ 1)
  change b α γ ∈ N
  induction α using (wellFounded_lt_of_monotone_finsupp h_mono).induction generalizing γ with
  | _ α ih => ?_
  by_cases! hα : ∀ u : ι, α u < κ u
  · exact hN α γ hα h_le
  obtain ⟨u, hu : κ u ≤ α u⟩ := hα
  obtain ⟨β, rfl⟩ : ∃ β : ι →₀ ℕ, α = single u (κ u) + β := exists_add_of_le (single_le_iff.mpr hu)
  have cost_eq : cost (single u (κ u) + β) = 1 + cost β := by simp [h_cost, weight, hκ, ne_of_gt]
  have h_split : b (single u (κ u) + β) γ = b β (single u 1 + γ) + g u * b β γ := by
    simp only [b, monomial_single_add, map_mul, pow_one, aeval_X]
    ring
  rw [cost_eq] at ih h_le
  rw [h_split]
  refine add_mem (ih β (by simp) _ (by simpa [add_assoc, add_comm, add_left_comm] using h_le)) ?_
  suffices g u ∈ N.comap (LinearMap.mulRight R (b β γ)) by simpa
  refine mem_of_forall_monomial_mem fun δ hδ ↦ ?_
  have h_lt : cost (δ + β) < 1 + cost β := by simpa using hg u δ hδ
  simpa [b, ← mul_assoc] using ih (δ + β) h_lt γ (by linarith)

end TauCeti
