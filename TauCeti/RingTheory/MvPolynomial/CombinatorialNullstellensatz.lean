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
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic.Linarith

/-!
# Weighted Combinatorial Nullstellensatz with multiplicity

This file proves a weighted form of the Combinatorial Nullstellensatz with multiplicity over an
arbitrary field `K`. Each variable `u : ι` is assigned a positive integer `κ u` and weight
`1 / κ u`. Given at least `∏ u, κ u` distinct points `z t : ι → K` at which each `X u ^ κ u`
agrees with a polynomial `g u` whose monomials all have weight strictly less than `1`, every
nonzero polynomial `f : MvPolynomial ι K` that vanishes to order `d` at all points `z t`
(meaning `f ∈ MvPolynomial.vanishingIdeal K {z t} ^ d`) has a monomial of weight at least `d`.

## Main results

* `TauCeti.exists_forall_coeff_translate_eq`: Chinese remainder theorem for polynomial jets — at
  finitely many distinct points `z t`, the Taylor coefficients on any finite exponent set `Γ` can
  be prescribed arbitrarily.
* `TauCeti.exists_le_weight_of_mem_vanishingIdeal_pow`: weighted Combinatorial Nullstellensatz
  with multiplicity.

## References

* N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. **8** (1999), 7–29.
* S. Ball and O. Serra, *Punctured combinatorial Nullstellensätze*, Combinatorica **29** (2009),
  511–522.
-/

public section

open MvPolynomial Finset Finsupp Submodule Ideal

namespace TauCeti

variable {K ι S : Type*} [Field K]

/-- If `p` vanishes to order `d` at `w`, then after translating `w` to the origin all coefficients
of `p` of degree below `d` vanish. -/
private lemma coeff_translate_eq_zero_of_mem_vanishingIdeal_pow {w : ι → K} {d : ℕ}
    {p : MvPolynomial ι K} (hp : p ∈ vanishingIdeal K {w} ^ d) {γ : ι →₀ ℕ} (hγ : γ.degree < d) :
    (aeval (X + C ∘ w) p).coeff γ = 0 := by
  let T : MvPolynomial ι K →ₐ[K] MvPolynomial ι K := aeval (X + C ∘ w)
  have h_origin : vanishingIdeal K {w} ≤ (idealOfVars ι K).comap T := fun q hq ↦ by
    have h_eq : constantCoeff.comp T.toRingHom = eval w :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp [T]) (fun i ↦ by simp [T])
    have h_const : constantCoeff (T q) = 0 := by
      simpa using (RingHom.congr_fun h_eq q).trans (by simpa using hq)
    rw [Ideal.mem_comap, ← pow_one (idealOfVars ι K), mem_pow_idealOfVars_iff']
    simpa [degree_eq_zero_iff, ← constantCoeff_eq] using h_const
  have h_mem : T p ∈ idealOfVars ι K ^ d := le_comap_pow T d (pow_right_mono h_origin d hp)
  exact (mem_pow_idealOfVars_iff' d _).1 h_mem γ hγ

/-- If every `φ u` vanishes at `w`, then `∏ u, (φ u) ^ (γ u)` vanishes at `w` to every order
`d ≤ γ.degree`. -/
private lemma aeval_monomial_mem_vanishingIdeal_pow {w : ι → K}
    {φ : ι → MvPolynomial ι K} (hφ : ∀ u : ι, eval w (φ u) = 0) {d : ℕ} {γ : ι →₀ ℕ}
    (hγ : d ≤ γ.degree) : aeval φ (monomial γ (1 : K)) ∈ vanishingIdeal K {w} ^ d := by
  classical
  have h_vars : idealOfVars ι K ≤ (vanishingIdeal K {w}).comap (aeval φ) := by
    simp [Ideal.span_le, hφ, Set.range_subset_iff]
  have h_mem : monomial γ (1 : K) ∈ idealOfVars ι K ^ d :=
    (mem_pow_idealOfVars_iff d _).2 (by simpa)
  exact le_comap_pow (aeval φ) d (pow_right_mono h_vars d h_mem)

/-- Chinese remainder theorem for polynomial jets: at finitely many distinct points `z t`, the
coefficients on any finite exponent set `Γ` after translating each `z t` to the origin can be
prescribed arbitrarily. -/
theorem exists_forall_coeff_translate_eq [Finite S] {z : S → ι → K}
    (hz_inj : z.Injective) (Γ : Finset (ι →₀ ℕ)) (y : S × Γ → K) :
    ∃ p : MvPolynomial ι K, ∀ (t : S) (γ : Γ), (aeval (X + C ∘ z t) p).coeff γ = y (t, γ) := by
  classical
  have := Fintype.ofFinite S
  let d : ℕ := Γ.sup Finsupp.degree + 1
  have h_ideal_inj : Function.Injective fun w : ι → K ↦ vanishingIdeal K {w} := fun w w' h_eq ↦ by
    funext u
    simpa [sub_eq_zero] using h_eq.ge (show X u - C (w' u) ∈ vanishingIdeal K {w'} by simp)
  have h_coprime : Pairwise (Function.onFun IsCoprime fun t : S ↦ vanishingIdeal K {z t} ^ d) :=
    fun t t' h_ne ↦ .pow (isCoprime_of_isMaximal ((h_ideal_inj.comp hz_inj).ne h_ne))
  let q (t : S) : MvPolynomial ι K := aeval (X + C ∘ (-z t)) (∑ γ : Γ, monomial γ (y (t, γ)))
  obtain ⟨p, hp⟩ := exists_forall_sub_mem_ideal h_coprime q
  refine ⟨p, fun t γ ↦ ?_⟩
  have h_jet : (aeval (X + C ∘ z t) (p - q t)).coeff γ = 0 :=
    coeff_translate_eq_zero_of_mem_vanishingIdeal_pow (hp t)
      (Nat.lt_succ_of_le (Finset.le_sup γ.property))
  have h_inv : (aeval (X + C ∘ z t) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K).comp
      (aeval (X + C ∘ (-z t))) = AlgHom.id K _ := by
    ext u
    simp
  have h_qt : aeval (X + C ∘ z t) (q t) = ∑ δ : Γ, monomial δ (y (t, δ)) :=
    AlgHom.congr_fun h_inv _
  simpa [h_qt, coeff_sum, sub_eq_zero] using h_jet

/-- A submodule containing every monomial occurring in `p` contains `p`. -/
private lemma mem_of_forall_monomial_mem {N : Submodule K (MvPolynomial ι K)}
    {p : MvPolynomial ι K} (h_monomial : ∀ α ∈ p.support, monomial α 1 ∈ N) : p ∈ N := by
  rw [p.as_sum]
  exact N.sum_mem fun α hα ↦ by simpa [smul_monomial] using N.smul_mem _ (h_monomial α hα)

/-- Comparing exponents by a monotone real-valued function is well founded (by Dickson's lemma). -/
private lemma wellFounded_lt_of_monotone_finsupp [Finite ι] {c : (ι →₀ ℕ) → ℝ} (hc : Monotone c) :
    WellFounded fun α β : ι →₀ ℕ ↦ c α < c β := by
  have := Fintype.ofFinite ι
  let e : (fun α β : ι →₀ ℕ ↦ α ≤ β) →r fun α β : ι →₀ ℕ ↦ c α ≤ c β := ⟨id, fun h ↦ hc h⟩
  have h_wqo : WellQuasiOrdered fun α β : ι →₀ ℕ ↦ c α ≤ c β :=
    wellQuasiOrdered_le.of_surjective e Function.surjective_id
  simpa only [lt_iff_le_not_ge] using h_wqo.wellFounded

/-- Weighted division by `ψ u = X u ^ κ u - g u`, where `u` has cost `1 / κ u` and every monomial
of `g u` has cost `< 1`. If a submodule `N` contains `X ^ α * ψ ^ γ` whenever `α < κ` and
`γ.degree + cost α ≤ r`, then it contains all `X ^ α * ψ ^ γ` with `γ.degree + cost α ≤ r`. -/
private lemma monomial_mul_aeval_mem_of_weight_le [Finite ι] {κ : ι → ℕ}
    (hκ : ∀ u : ι, 0 < κ u) {g : ι → MvPolynomial ι K}
    (hg : ∀ u : ι, ∀ α ∈ (g u).support, weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α < 1)
    {N : Submodule K (MvPolynomial ι K)} {r : ℝ}
    (hN : ∀ α γ : ι →₀ ℕ, (∀ u : ι, α u < κ u) →
      γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r →
      monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K)) ∈ N)
    (α γ : ι →₀ ℕ) (h_le : γ.degree + weight (fun u : ι ↦ (κ u : ℝ))⁻¹ α ≤ r) :
    monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K)) ∈ N := by
  have := Fintype.ofFinite ι
  set cost : (ι →₀ ℕ) →+ ℝ := weight (fun u : ι ↦ (κ u : ℝ))⁻¹ with h_cost
  have h_mono : Monotone cost := fun α β h_exp ↦ by
    simp only [h_cost, weight_eq_sum, nsmul_eq_mul, Pi.inv_apply]
    gcongr with u
    exact h_exp u
  let b (α γ : ι →₀ ℕ) : MvPolynomial ι K :=
    monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K))
  change b α γ ∈ N
  induction α using (wellFounded_lt_of_monotone_finsupp h_mono).induction generalizing γ with
  | _ α ih => ?_
  by_cases! hα : ∀ u : ι, α u < κ u
  · exact hN α γ hα h_le
  obtain ⟨u, hu : κ u ≤ α u⟩ := hα
  obtain ⟨β, rfl⟩ : ∃ β : ι →₀ ℕ, α = single u (κ u) + β := exists_add_of_le (single_le_iff.2 hu)
  have cost_eq : cost (single u (κ u) + β) = 1 + cost β := by simp [h_cost, weight, hκ, ne_of_gt]
  have h_split : b (single u (κ u) + β) γ = b β (single u 1 + γ) + g u * b β γ := by
    simp only [b, monomial_single_add, map_mul, pow_one, aeval_X]
    ring
  rw [cost_eq] at ih h_le
  rw [h_split]
  refine add_mem (ih β (by simp) _ (by simpa [add_assoc, add_comm, add_left_comm] using h_le)) ?_
  suffices g u ∈ N.comap (LinearMap.mulRight K (b β γ)) by simpa
  refine mem_of_forall_monomial_mem fun δ hδ ↦ ?_
  have h_lt : cost (δ + β) < 1 + cost β := by simpa using hg u δ hδ
  simpa [b, ← mul_assoc] using ih (δ + β) h_lt γ (by linarith)

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
    LinearMap.pi fun (t, γ) ↦ lcoeff K γ ∘ₗ (aeval (X + C ∘ z t)).toLinearMap
  have mem_ker {p : MvPolynomial ι K} (hp : ∀ t : S, p ∈ vanishingIdeal K {z t} ^ d) : p ∈ J.ker :=
    LinearMap.mem_ker.2 <| funext fun (t, γ) ↦
      coeff_translate_eq_zero_of_mem_vanishingIdeal_pow (hp t) ((hΓ γ).1 γ.property)
  have J_surj : Function.Surjective J := fun y ↦
    (exists_forall_coeff_translate_eq hz_inj Γ y).imp
      fun p hp ↦ funext fun (t, γ) ↦ hp t γ
  let b (α γ : ι →₀ ℕ) : MvPolynomial ι K :=
    monomial α 1 * aeval (fun u : ι ↦ X u ^ κ u - g u) (monomial γ (1 : K))
  let v : univ.finsupp (range ∘ κ) × Γ → MvPolynomial ι K := fun (α, γ) ↦ b α γ
  have b_span (α γ : ι →₀ ℕ) (hα : ∀ u : ι, α u < κ u) (hγ : γ.degree < d) :
      b α γ ∈ span K (Set.range v) :=
    subset_span ⟨(⟨α, by simpa [mem_finsupp_iff]⟩, ⟨γ, (hΓ γ).2 hγ⟩), rfl⟩
  have b_ker (α γ : ι →₀ ℕ) (hγ : d ≤ γ.degree) : b α γ ∈ J.ker :=
    mem_ker fun t ↦ mul_mem_left _ _
      (aeval_monomial_mem_vanishingIdeal_pow (fun u ↦ by simp [hg_eval]) hγ)
  have mem_sup (p : MvPolynomial ι K) : p ∈ span K (Set.range v) ⊔ J.ker :=
    mem_of_forall_monomial_mem fun α _ ↦ by
      suffices b α 0 ∈ span K (Set.range v) ⊔ J.ker by simpa [b]
      refine monomial_mul_aeval_mem_of_weight_le hκ hg_cost (fun β γ hβ _ ↦ ?_) α 0 le_rfl
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
  have hf_span : f ∈ span K (Set.range v) := mem_of_forall_monomial_mem fun α hα ↦ by
    suffices b α 0 ∈ span K (Set.range v) by simpa [b]
    refine monomial_mul_aeval_mem_of_weight_le hκ hg_cost (fun β γ hβ h_le ↦ ?_) α 0 le_rfl
    have h_nonneg : 0 ≤ weight (fun u : ι ↦ (κ u : ℝ))⁻¹ β := by
      simp only [weight_eq_sum, Pi.inv_apply, nsmul_eq_mul]
      exact Finset.sum_nonneg fun u _ ↦
        mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
    simp only [map_zero, Nat.cast_zero, zero_add] at h_le
    exact b_span β γ hβ ((Nat.cast_lt (α := ℝ)).1 (by linarith [h_low α hα]))
  exact hf_ne ((range_ker_disjoint h_indep).le_bot ⟨hf_span, mem_ker hf⟩)

end TauCeti
