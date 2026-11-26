/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Data.Finset.Finsupp
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.Linarith
import TauCeti.Data.Finsupp.PWO
import TauCeti.RingTheory.MvPolynomial.LocalOrder
import TauCeti.RingTheory.MvPolynomial.Submodule
import TauCeti.RingTheory.MvPolynomial.TaylorJet

/-!
# Weighted Combinatorial Nullstellensatz with multiplicity

This file proves a weighted form of the Combinatorial Nullstellensatz with multiplicity over an
arbitrary field `K`. Each variable `u : ι` is assigned a positive integer `κ u` and weight
`1 / κ u`. Given at least `∏ u, κ u` distinct points `z t : ι → K` at which each `X u ^ κ u`
agrees with a polynomial `g u` whose monomials all have weight strictly less than `1`, every
nonzero polynomial `f : MvPolynomial ι K` that vanishes to order `d` at all points `z t`
(meaning `f ∈ MvPolynomial.vanishingIdeal K {z t} ^ d`) has a monomial of weight at least `d`.

## Main results

* `TauCeti.exists_le_weight_of_mem_vanishingIdeal_pow`: weighted Combinatorial Nullstellensatz
  with multiplicity.

## References

* L. Alpöge and L. Sernau, grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0,
  Copyright 2026 Anthropic, PBC), `src/Lib/General/Algebra/MultivariatePolynomials.lean`
  (`New.exists_le_weight_of_mem_vanishingIdeal_pow`).
* N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. **8** (1999), 7–29.
* S. Ball and O. Serra, *Punctured combinatorial Nullstellensätze*, Combinatorica **29** (2009),
  511–522.
-/

public section

open MvPolynomial Finset Finsupp Submodule Ideal

namespace TauCeti

variable {K ι S : Type*} [Field K]

/-- A real-valued weight with nonnegative coordinates is monotone on `ι →₀ ℕ`. -/
private lemma weight_mono_of_nonneg {w : ι → ℝ} (hw : ∀ u : ι, 0 ≤ w u) :
    Monotone (weight w : (ι →₀ ℕ) → ℝ) := fun α β h_exp ↦ by
  classical
  rw [weight_apply, weight_apply,
    Finsupp.sum_of_support_subset α (Finsupp.support_mono h_exp) _ (by simp), Finsupp.sum]
  simp only [nsmul_eq_mul]
  gcongr with u
  · exact hw u
  · exact h_exp u

/-- Basis element `X ^ α * ∏ u, (X u ^ κ u - g u) ^ (γ u)` used in the weighted division argument
for the Combinatorial Nullstellensatz with multiplicity. -/
private noncomputable def weightedBasis (κ : ι → ℕ) (g : ι → MvPolynomial ι K)
    (α γ : ι →₀ ℕ) : MvPolynomial ι K :=
  monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K))

/-- Weighted division by `ψ u = X u ^ κ u - g u`, where `u` has cost `1 / κ u` and every monomial
of `g u` has cost `< 1`. If a submodule `N` contains `weightedBasis κ g α γ` whenever `α < κ` and
`γ.degree + cost α ≤ r`, then it contains all `weightedBasis κ g α γ` with
`γ.degree + cost α ≤ r`. -/
private lemma weightedBasis_mem_of_weight_le [Finite ι] {κ : ι → ℕ}
    (hκ : ∀ u : ι, 0 < κ u) {g : ι → MvPolynomial ι K}
    (hg : ∀ u : ι, ∀ α ∈ (g u).support, weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α < 1)
    {N : Submodule K (MvPolynomial ι K)} {r : ℝ}
    (hN : ∀ α γ : ι →₀ ℕ, (∀ u : ι, α u < κ u) →
      γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r → weightedBasis κ g α γ ∈ N)
    (α γ : ι →₀ ℕ) (h_le : γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r) :
    weightedBasis κ g α γ ∈ N := by
  have := Fintype.ofFinite ι
  set cost : (ι →₀ ℕ) →+ ℝ := weight (fun u : ι ↦ (κ u : ℝ))⁻¹ with h_cost
  have h_mono : Monotone cost :=
    weight_mono_of_nonneg fun u ↦ inv_nonneg.2 (Nat.cast_nonneg _)
  induction α using (wellFounded_lt_of_monotone h_mono).induction generalizing γ with
  | _ α ih => ?_
  by_cases! hα : ∀ u : ι, α u < κ u
  · exact hN α γ hα h_le
  obtain ⟨u, hu : κ u ≤ α u⟩ := hα
  obtain ⟨β, rfl⟩ : ∃ β : ι →₀ ℕ, α = single u (κ u) + β := exists_add_of_le (single_le_iff.2 hu)
  have cost_eq : cost (single u (κ u) + β) = 1 + cost β := by simp [h_cost, weight, hκ, ne_of_gt]
  have h_split : weightedBasis κ g (single u (κ u) + β) γ =
      weightedBasis κ g β (single u 1 + γ) + g u * weightedBasis κ g β γ := by
    simp only [weightedBasis, monomial_single_add, map_mul, pow_one, aeval_X]
    ring
  rw [cost_eq] at ih h_le
  rw [h_split]
  refine add_mem (ih β (by simp) _ (by simpa [add_assoc, add_comm, add_left_comm] using h_le)) ?_
  suffices g u ∈ N.comap (LinearMap.mulRight K (weightedBasis κ g β γ)) by simpa
  refine mem_submodule_of_forall_monomial_mem fun δ hδ ↦ ?_
  have h_lt : cost (δ + β) < 1 + cost β := by simpa using hg u δ hδ
  simpa [weightedBasis, ← mul_assoc] using ih (δ + β) h_lt γ (by linarith)

/-- **Weighted Combinatorial Nullstellensatz with multiplicity.** Give each variable `u : ι` the
weight `1 / κ u`. Take at least `∏ u, κ u` distinct points `z t : ι → K` at which each `X u ^ κ u`
agrees with a polynomial `g u` whose monomials all have weight strictly less than `1`. Then every
nonzero polynomial `f : MvPolynomial ι K` that vanishes to order `d` at all points `z t` has a
monomial of weight at least `d`. -/
theorem exists_le_weight_of_mem_vanishingIdeal_pow [Fintype ι] [Fintype S] (κ : ι → ℕ)
    (hκ : ∀ u : ι, 0 < κ u) (z : S → ι → K) (hz_inj : z.Injective)
    (h_card : ∏ u : ι, κ u ≤ Fintype.card S) (g : ι → MvPolynomial ι K)
    (hg_cost : ∀ u : ι, ∀ α ∈ (g u).support, weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α < 1)
    (hg_eval : ∀ (u : ι) (t : S), eval (z t) (g u) = z t u ^ κ u)
    (d : ℕ) (f : MvPolynomial ι K) (hf_ne : f ≠ 0) (hf : ∀ t : S, f ∈ vanishingIdeal K {z t} ^ d) :
    ∃ α ∈ f.support, (d : ℝ) ≤ weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α := by
  classical
  let Γ : Finset (ι →₀ ℕ) := (finite_of_degree_lt d).toFinset
  have hΓ (γ : ι →₀ ℕ) : γ ∈ Γ ↔ γ.degree < d := Set.Finite.mem_toFinset _
  let J : MvPolynomial ι K →ₗ[K] (S × Γ → K) :=
    LinearMap.pi fun (t, γ) ↦ lcoeff K γ ∘ₗ (taylor (z t)).toLinearMap
  have mem_ker {p : MvPolynomial ι K} (hp : ∀ t : S, p ∈ vanishingIdeal K {z t} ^ d) : p ∈ J.ker :=
    LinearMap.mem_ker.2 <| funext fun (t, γ) ↦
      le_orderAt_iff.1 ((mem_pow_vanishingIdeal_singleton_iff p (z t) d).1 (hp t)) γ
        (by exact_mod_cast (hΓ γ).1 γ.property)
  have J_surj : Function.Surjective J := fun y ↦
    (exists_forall_coeff_taylor_eq hz_inj Γ y).imp fun p hp ↦ funext fun (t, γ) ↦ hp t γ
  let v : univ.finsupp (range ∘ κ) × Γ → MvPolynomial ι K := fun (α, γ) ↦ weightedBasis κ g α γ
  have b_span (α γ : ι →₀ ℕ) (hα : ∀ u : ι, α u < κ u) (hγ : γ.degree < d) :
      weightedBasis κ g α γ ∈ span K (Set.range v) :=
    subset_span ⟨(⟨α, by simpa [mem_finsupp_iff]⟩, ⟨γ, (hΓ γ).2 hγ⟩), rfl⟩
  have b_ker (α γ : ι →₀ ℕ) (hγ : d ≤ γ.degree) : weightedBasis κ g α γ ∈ J.ker :=
    mem_ker fun t ↦ mul_mem_left _ _
      (aeval_monomial_mem_vanishingIdeal_pow (fun u ↦ by simp [hg_eval]) hγ)
  have mem_sup (p : MvPolynomial ι K) : p ∈ span K (Set.range v) ⊔ J.ker :=
    mem_submodule_of_forall_monomial_mem fun α _ ↦ by
      suffices weightedBasis κ g α 0 ∈ span K (Set.range v) ⊔ J.ker by simpa [weightedBasis]
      refine weightedBasis_mem_of_weight_le hκ hg_cost (fun β γ hβ _ ↦ ?_) α 0 le_rfl
      exact (lt_or_ge γ.degree d).elim (fun h ↦ mem_sup_left (b_span β γ hβ h))
        (fun h ↦ mem_sup_right (b_ker β γ h))
  have h_span : ⊤ ≤ span K (Set.range (J ∘ v)) := fun y _ ↦ by
    obtain ⟨p, rfl⟩ := J_surj y
    simpa only [Set.range_comp, span_image, ← Submodule.mem_comap, Submodule.comap_map_eq]
      using mem_sup p
  have h_indep : LinearIndependent K (J ∘ v) :=
    linearIndependent_of_top_le_span_of_card_le_finrank h_span
      (by simpa using Nat.mul_le_mul_right Γ.card h_card)
  by_contra! h_low
  have hf_span : f ∈ span K (Set.range v) := mem_submodule_of_forall_monomial_mem fun α hα ↦ by
    suffices weightedBasis κ g α 0 ∈ span K (Set.range v) by simpa [weightedBasis]
    refine weightedBasis_mem_of_weight_le hκ hg_cost (fun β γ hβ h_le ↦ ?_) α 0 le_rfl
    have h_nonneg : 0 ≤ weight (fun u : ι ↦ (κ u : ℝ))⁻¹ β := by
      simpa using weight_mono_of_nonneg (w := (fun u : ι ↦ (κ u : ℝ))⁻¹)
        (fun u ↦ inv_nonneg.2 (Nat.cast_nonneg _)) (zero_le (a := β))
    simp only [map_zero, Nat.cast_zero, zero_add] at h_le
    exact b_span β γ hβ ((Nat.cast_lt (α := ℝ)).1 (by linarith [h_low α hα]))
  exact hf_ne ((range_ker_disjoint h_indep).le_bot ⟨hf_span, mem_ker hf⟩)

end TauCeti
