/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Positivity

/-!
# Low-cost polynomial evaluation on spans and weighted dimension bounds

This file collects two general linear-algebraic and polynomial ingredients used to bound the sum
of dimensions of spaces of forms with only deep translates:

## Main results

* `TauCeti.exists_eval_eq_dotProduct_of_mem_span`: if every vector `u ∈ S` satisfies
  `u ⬝ᵥ a y = z y v ^ e` for some variable `v` and exponent `e < o v`, then every `u` in the span
  of `S` is realized as `eval (z y) g` by a polynomial `g` whose monomials all have weighted cost
  `< 1` for the weights `v ↦ (o v : ℝ)⁻¹`.
* `TauCeti.finrank_le_card_of_forall_exists_ne_zero`: if every nonzero function in a subspace
  `S ≤ (ι → K)` is nonzero at some point of a finite set `s`, then `Module.finrank K S ≤ s.card`.
* `TauCeti.sum_finrank_le_sum_cost_of_exists_le_cost`: if every nonzero vector in `S d` has a
  nonzero coordinate `β` of nonnegative cost `≥ d + 1`, then
  `(∑ d ∈ Finset.range M, Module.finrank K (S d) : ℝ) ≤ ∑ β, cost β`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/Depth.lean`
  (`New.exists_eval_eq_dotProduct_of_mem_span`, `New.finrank_le_card_of_forall_exists_ne_zero`,
  and the dimension-summing argument of `New.FrobeniusCycle.sum_finrank_deepForms_le`).
-/

public section

namespace TauCeti

open MvPolynomial Finsupp Finset Submodule Module

/-- If every `u ∈ S` satisfies `u ⬝ᵥ a y = z y v ^ e` for some `v` and `e < o v`, then every `u`
in `Submodule.span L S` is realized as `eval (z y) g` by a polynomial `g` whose monomials all have
weighted degree `< 1` for the weights `v ↦ (o v : ℝ)⁻¹`. -/
theorem exists_eval_eq_dotProduct_of_mem_span {σ I Y L : Type*} [Fintype I] [Field L]
    {o : σ → ℕ} {z : Y → σ → L} {a : Y → I → L} {S : Set (I → L)}
    (hS : ∀ u ∈ S, ∃ (v : σ) (e : ℕ), e < o v ∧ ∀ y : Y, ∑ i : I, u i * a y i = z y v ^ e)
    {u : I → L} (hu : u ∈ span L S) :
    ∃ g : MvPolynomial σ L,
      (∀ α ∈ g.support, weight (fun v : σ ↦ (o v : ℝ)⁻¹) α < 1) ∧
      ∀ y : Y, eval (z y) g = ∑ i : I, u i * a y i := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, e, h_lt, h_eval⟩ := hS u hu
    refine ⟨X v ^ e, fun α hα ↦ ?_, fun y ↦ by rw [map_pow, eval_X, h_eval]⟩
    rw [X_pow_eq_monomial] at hα
    have h_eq : α = Finsupp.single v e := Finset.mem_singleton.mp (support_monomial_subset hα)
    subst h_eq
    have h_cast : (e : ℝ) < o v := Nat.cast_lt.mpr h_lt
    calc weight (fun w : σ ↦ (o w : ℝ)⁻¹) (Finsupp.single v e) = e / o v := by
          simp [weight_single, div_eq_mul_inv]
      _ < 1 := (div_lt_one (h_cast.trans_le' e.cast_nonneg)).mpr h_cast
  | zero => exact ⟨0, by simp, fun y ↦ by simp⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    obtain ⟨g', hg'_cost, hg'_eval⟩ := ih'
    refine ⟨g + g', fun α hα ↦ ?_, fun y ↦ by
      simp [hg_eval, hg'_eval, add_mul, Finset.sum_add_distrib]⟩
    exact (mem_union.mp (MvPolynomial.support_add hα)).elim (hg_cost α) (hg'_cost α)
  | smul s u _ ih =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    exact ⟨s • g, fun α hα ↦ hg_cost α (MvPolynomial.support_smul hα), fun y ↦ by
      simp [smul_eq_C_mul, hg_eval, Finset.mul_sum, mul_assoc]⟩

/-- If every nonzero function in a subspace `S ≤ (ι → K)` is nonzero at some point of a finite
set `s`, then `Module.finrank K S ≤ s.card`. -/
theorem finrank_le_card_of_forall_exists_ne_zero {K ι : Type*} [Field K]
    {S : Submodule K (ι → K)} {s : Finset ι} (hS : ∀ F ∈ S, F ≠ 0 → ∃ β ∈ s, F β ≠ 0) :
    finrank K S ≤ s.card := by
  let res : S →ₗ[K] s → K := (LinearMap.funLeft K K ((↑) : s → ι)).domRestrict S
  have h_inj : Function.Injective res :=
    (injective_iff_map_eq_zero res).mpr fun F hF ↦ Subtype.ext <| by
      by_contra h_ne
      obtain ⟨β, hβ, h_value⟩ := hS F F.property h_ne
      exact h_value (by simpa [res] using congrFun hF ⟨β, hβ⟩)
  simpa [Module.finrank_pi_fintype] using res.finrank_le_finrank_of_injective h_inj

/-- Double-counting dimension bound from a nonnegative cost function: if every nonzero vector in
`S d` has a nonzero coordinate `β` with `(d + 1 : ℝ) ≤ cost β`, then
`(∑ d ∈ Finset.range M, Module.finrank K (S d) : ℝ) ≤ ∑ β : ι, cost β`. -/
theorem sum_finrank_le_sum_cost_of_exists_le_cost {K ι : Type*} [Field K] [Fintype ι]
    (S : ℕ → Submodule K (ι → K)) (cost : ι → ℝ) (h_nonneg : ∀ β : ι, 0 ≤ cost β)
    (hS : ∀ d : ℕ, ∀ F ∈ S d, F ≠ 0 → ∃ β : ι, F β ≠ 0 ∧ ((d + 1 : ℕ) : ℝ) ≤ cost β) (M : ℕ) :
    (∑ d ∈ range M, finrank K (S d) : ℝ) ≤ ∑ β : ι, cost β := by
  classical
  have h_rank (d : ℕ) : finrank K (S d) ≤ (univ.filter fun β : ι ↦ d < ⌊cost β⌋₊).card := by
    refine finrank_le_card_of_forall_exists_ne_zero fun F hF hF_ne ↦ ?_
    obtain ⟨β, hβ, h_cost⟩ := hS d F hF hF_ne
    exact ⟨β, mem_filter.mpr ⟨mem_univ β, Nat.le_floor h_cost⟩, hβ⟩
  have h_sum : ∑ d ∈ range M, finrank K (S d) ≤ ∑ β : ι, ⌊cost β⌋₊ := by
    refine (sum_le_sum fun d _ ↦ h_rank d).trans ?_
    let N := max M (univ.sup fun β : ι ↦ ⌊cost β⌋₊)
    refine (sum_le_sum_of_subset (range_mono (le_max_left M _ : M ≤ N))).trans_eq ?_
    simp only [card_filter]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun β _ ↦ ?_
    rw [sum_boole, Nat.cast_id]
    have hlt : ⌊cost β⌋₊ ≤ N := le_max_of_le_right (le_sup (f := fun β ↦ ⌊cost β⌋₊) (mem_univ β))
    have hfilter : (range N).filter (fun d ↦ d < ⌊cost β⌋₊) = range ⌊cost β⌋₊ := by
      ext d; simp only [mem_filter, mem_range]; exact ⟨fun h ↦ h.right, fun h ↦ ⟨h.trans_le hlt, h⟩⟩
    rw [hfilter, card_range]
  calc (∑ d ∈ range M, finrank K (S d) : ℝ)
      ≤ ∑ β : ι, (⌊cost β⌋₊ : ℝ) := by exact_mod_cast h_sum
    _ ≤ ∑ β : ι, cost β := sum_le_sum fun β _ ↦ Nat.floor_le (h_nonneg β)

end TauCeti
