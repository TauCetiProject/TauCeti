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
import Mathlib.Data.Finsupp.PWO
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.Linarith
import TauCeti.Data.Finsupp.Weight
import TauCeti.Order.WellQuasiOrder
import TauCeti.RingTheory.MvPolynomial.Ideal.Pow
import TauCeti.RingTheory.MvPolynomial.RestrictSupport
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

variable {K ι S : Type*}

section CommRing

variable [CommRing K]

/-- Basis element `X ^ α * ∏ u, (X u ^ κ u - g u) ^ (γ u)` used in the weighted division argument
for the Combinatorial Nullstellensatz with multiplicity. -/
private noncomputable def weightedBasis (κ : ι → ℕ) (g : ι → MvPolynomial ι K)
    (α γ : ι →₀ ℕ) : MvPolynomial ι K :=
  monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K))

/-- `weightedBasis κ g α 0` is the monomial `X ^ α`. -/
private lemma weightedBasis_zero (κ : ι → ℕ) (g : ι → MvPolynomial ι K) (α : ι →₀ ℕ) :
    weightedBasis κ g α 0 = monomial α 1 := by
  simp only [weightedBasis, aeval_monomial, Finsupp.prod_zero_index, map_one, mul_one]

/-- Multiplying `weightedBasis κ g β γ` by `X ^ δ` shifts its monomial part to `X ^ (δ + β)`. -/
private lemma monomial_mul_weightedBasis (κ : ι → ℕ) (g : ι → MvPolynomial ι K)
    (δ β γ : ι →₀ ℕ) :
    monomial δ 1 * weightedBasis κ g β γ = weightedBasis κ g (δ + β) γ := by
  rw [weightedBasis, weightedBasis, ← mul_assoc, monomial_mul_monomial, one_mul]

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
    Finsupp.weight_mono_of_nonneg fun u ↦ inv_nonneg.2 (Nat.cast_nonneg _)
  induction α using h_mono.wellFounded_lt_comp.induction generalizing γ with
  | _ α ih => ?_
  by_cases! hα : ∀ u : ι, α u < κ u
  · exact hN α γ hα h_le
  obtain ⟨u, hu : κ u ≤ α u⟩ := hα
  obtain ⟨β, rfl⟩ : ∃ β : ι →₀ ℕ, α = single u (κ u) + β := exists_add_of_le (single_le_iff.2 hu)
  have cost_eq : cost (single u (κ u) + β) = 1 + cost β := by
    simp [h_cost, weight_single, (hκ u).ne']
  have h_split : weightedBasis κ g (single u (κ u) + β) γ =
      weightedBasis κ g β (single u 1 + γ) + g u * weightedBasis κ g β γ := by
    simp only [weightedBasis, monomial_single_add, map_mul, pow_one, aeval_X]
    ring
  rw [cost_eq] at ih h_le
  rw [h_split]
  have h_le' : ((single u 1 + γ).degree : ℝ) + cost β ≤ r := by
    rw [map_add, degree_single]
    push_cast
    linarith
  refine add_mem (ih β (by simp) _ h_le') ?_
  -- `g u * b ∈ N` is the statement that `g u` lies in the preimage of `N` under `· * b`.
  suffices g u ∈ N.comap (LinearMap.mulRight K (weightedBasis κ g β γ)) by simpa
  refine mem_submodule_of_support fun δ hδ ↦ ?_
  have h_lt : cost (δ + β) < 1 + cost β := by simpa using hg u δ hδ
  rw [Submodule.mem_comap, LinearMap.mulRight_apply, monomial_mul_weightedBasis]
  exact ih (δ + β) h_lt γ (by linarith)

/-- A submodule `N` contains a polynomial `p` as soon as, for every monomial `X ^ α` of `p`, it
contains `weightedBasis κ g β γ` whenever `β < κ` and `γ.degree + cost β ≤ cost α`. -/
private lemma mem_of_forall_weightedBasis_mem [Finite ι] {κ : ι → ℕ}
    (hκ : ∀ u : ι, 0 < κ u) {g : ι → MvPolynomial ι K}
    (hg : ∀ u : ι, ∀ α ∈ (g u).support, weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α < 1)
    {N : Submodule K (MvPolynomial ι K)} {p : MvPolynomial ι K}
    (hN : ∀ α ∈ p.support, ∀ β γ : ι →₀ ℕ, (∀ u : ι, β u < κ u) →
      γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ β ≤ weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α →
        weightedBasis κ g β γ ∈ N) :
    p ∈ N := by
  refine mem_submodule_of_support fun α hα ↦ ?_
  rw [← weightedBasis_zero κ g α]
  exact weightedBasis_mem_of_weight_le hκ hg (hN α hα) α 0 (by simp)

end CommRing

/-- **Weighted Combinatorial Nullstellensatz with multiplicity.** Give each variable `u : ι` the
weight `1 / κ u`. Take at least `∏ u, κ u` distinct points `z t : ι → K` at which each `X u ^ κ u`
agrees with a polynomial `g u` whose monomials all have weight strictly less than `1`. Then every
nonzero polynomial `f : MvPolynomial ι K` that vanishes to order `d` at all points `z t` has a
monomial of weight at least `d`. -/
theorem exists_le_weight_of_mem_vanishingIdeal_pow [Field K] [Fintype ι] [Fintype S] (κ : ι → ℕ)
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
      (aeval_monomial_mem_pow (I := vanishingIdeal K {z t})
        (fun u ↦ (mem_vanishingIdeal_singleton_iff _ _).2 (by simp [hg_eval])) hγ)
  have mem_sup (p : MvPolynomial ι K) : p ∈ span K (Set.range v) ⊔ J.ker :=
    mem_of_forall_weightedBasis_mem hκ hg_cost fun _ _ β γ hβ _ ↦
      (lt_or_ge γ.degree d).elim (fun h ↦ mem_sup_left (b_span β γ hβ h))
        (fun h ↦ mem_sup_right (b_ker β γ h))
  have h_span : ⊤ ≤ span K (Set.range (J ∘ v)) := by
    rw [Set.range_comp, span_image, top_le_iff,
      LinearMap.map_eq_top_iff (LinearMap.range_eq_top.2 J_surj)]
    exact eq_top_iff.2 fun p _ ↦ mem_sup p
  have h_indep : LinearIndependent K (J ∘ v) :=
    linearIndependent_of_top_le_span_of_card_le_finrank h_span
      (by simpa using Nat.mul_le_mul_right Γ.card h_card)
  by_contra! h_low
  have hf_span : f ∈ span K (Set.range v) :=
    mem_of_forall_weightedBasis_mem hκ hg_cost fun α hα β γ hβ h_le ↦ by
      have h_nonneg : 0 ≤ weight (fun u : ι ↦ (κ u : ℝ))⁻¹ β :=
        Finsupp.weight_nonneg (w := (fun u : ι ↦ (κ u : ℝ))⁻¹)
          (fun u ↦ inv_nonneg.2 (Nat.cast_nonneg _)) β
      exact b_span β γ hβ ((Nat.cast_lt (α := ℝ)).1 (by linarith [h_low α hα]))
  exact hf_ne ((range_ker_disjoint h_indep).le_bot ⟨hf_span, mem_ker hf⟩)

end TauCeti
