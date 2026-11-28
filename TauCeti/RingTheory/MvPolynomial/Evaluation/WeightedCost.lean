/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Low-cost multivariate polynomials realizing linear forms on evaluations

Given families of points z : Y → σ → R and vectors  : Y → I → R over a commutative ring R,
together with positive capacity bounds o : σ → ℕ, suppose each generator u ∈ S has u ⬝ᵥ a y
equal to a pure power z y v ^ e with e < o v. Then every vector u in the R-span of S
is realized by a single multivariate polynomial g : MvPolynomial σ R whose evaluation at z y
equals u ⬝ᵥ a y for all y and every monomial of which has weighted cost
∑ v, α v / o v < 1.

## Main results

* TauCeti.exists_eval_eq_dotProduct_of_mem_span: low-cost polynomial realization for any
  u ∈ Submodule.span R S.
* TauCeti.exists_eval_eq_dotProduct_of_span_eq_top: the case where S spans I → R.
* TauCeti.exists_eval_eq_apply_of_mem_span: coordinate specialization when
  Pi.single i 1 ∈ Submodule.span R S.

## Provenance

TauCeti.exists_eval_eq_dotProduct_of_mem_span is adapted from
New.exists_eval_eq_dotProduct_of_mem_span in src/New/UpperBound/ElementaryDivisors/Depth.lean
in grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC),
generalized from a field to any commutative ring.
-/

public section

open MvPolynomial

namespace TauCeti

variable {σ I Y R : Type*} [Fintype I] [CommRing R]

/-- If every u ∈ S satisfies ∀ y, u ⬝ᵥ a y = z y v ^ e for some  : σ and e < o v, then
every u ∈ Submodule.span R S is realized by a polynomial g : MvPolynomial σ R whose monomials
all have weighted cost Finsupp.weight (fun v ↦ (o v : ℝ)⁻¹) α < 1 and satisfy
eval (z y) g = u ⬝ᵥ a y for all y. -/
theorem exists_eval_eq_dotProduct_of_mem_span {o : σ → ℕ} {z : Y → σ → R} {a : Y → I → R}
    {S : Set (I → R)}
    (hS : ∀ u ∈ S, ∃ (v : σ) (e : ℕ), e < o v ∧ ∀ y : Y, u ⬝ᵥ a y = z y v ^ e) {u : I → R}
    (hu : u ∈ Submodule.span R S) :
    ∃ g : MvPolynomial σ R,
      (∀ α ∈ g.support, Finsupp.weight (fun v : σ ↦ (o v : ℝ)⁻¹) α < 1) ∧
      ∀ y : Y, eval (z y) g = u ⬝ᵥ a y := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, e, h_lt, h_eval⟩ := hS u hu
    refine ⟨X v ^ e, fun α hα ↦ ?_, fun y ↦ by rw [h_eval, map_pow, eval_X]⟩
    obtain ⟨rfl, -⟩ : Finsupp.single v e = α ∧ (1 : R) ≠ 0 := by
      simpa [X_pow_eq_monomial] using hα
    have h_cast : (e : ℝ) < o v := Nat.cast_lt.mpr h_lt
    calc Finsupp.weight (fun v : σ ↦ (o v : ℝ)⁻¹) (Finsupp.single v e) = e / o v := by
          simp [Finsupp.weight_single, div_eq_mul_inv]
      _ < 1 := (div_lt_one (h_cast.trans_le' e.cast_nonneg)).mpr h_cast
  | zero => exact ⟨0, by simp, fun y ↦ by rw [map_zero, zero_dotProduct]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    obtain ⟨g', hg'_cost, hg'_eval⟩ := ih'
    refine ⟨g + g', fun α hα ↦ ?_, fun y ↦ by rw [map_add, hg_eval, hg'_eval, add_dotProduct]⟩
    exact (Finset.mem_union.mp (MvPolynomial.support_add hα)).elim (hg_cost α) (hg'_cost α)
  | smul s u _ ih =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    exact ⟨s • g, fun α hα ↦ hg_cost α (MvPolynomial.support_smul hα), fun y ↦ by
      rw [smul_eq_C_mul, map_mul, eval_C, hg_eval, smul_dotProduct, smul_eq_mul]⟩

/-- When the generators S span I → R, every vector u : I → R admits a low-cost polynomial
realization of y ↦ u ⬝ᵥ a y. -/
theorem exists_eval_eq_dotProduct_of_span_eq_top {o : σ → ℕ} {z : Y → σ → R} {a : Y → I → R}
    {S : Set (I → R)}
    (hS : ∀ u ∈ S, ∃ (v : σ) (e : ℕ), e < o v ∧ ∀ y : Y, u ⬝ᵥ a y = z y v ^ e)
    (hspan : Submodule.span R S = ⊤) (u : I → R) :
    ∃ g : MvPolynomial σ R,
      (∀ α ∈ g.support, Finsupp.weight (fun v : σ ↦ (o v : ℝ)⁻¹) α < 1) ∧
      ∀ y : Y, eval (z y) g = u ⬝ᵥ a y :=
  exists_eval_eq_dotProduct_of_mem_span hS (hspan.symm ▸ Submodule.mem_top)

/-- If the i-th standard basis vector lies in Submodule.span R S, then the coordinate
y ↦ a y i is realized by a polynomial of weighted cost strictly less than 1. -/
theorem exists_eval_eq_apply_of_mem_span [DecidableEq I] {o : σ → ℕ} {z : Y → σ → R}
    {a : Y → I → R} {S : Set (I → R)}
    (hS : ∀ u ∈ S, ∃ (v : σ) (e : ℕ), e < o v ∧ ∀ y : Y, u ⬝ᵥ a y = z y v ^ e)
    {i : I} (hi : Pi.single i (1 : R) ∈ Submodule.span R S) :
    ∃ g : MvPolynomial σ R,
      (∀ α ∈ g.support, Finsupp.weight (fun v : σ ↦ (o v : ℝ)⁻¹) α < 1) ∧
      ∀ y : Y, eval (z y) g = a y i := by
  obtain ⟨g, hg_cost, hg_eval⟩ := exists_eval_eq_dotProduct_of_mem_span hS hi
  exact ⟨g, hg_cost, fun y ↦ by simpa using hg_eval y⟩

end TauCeti
