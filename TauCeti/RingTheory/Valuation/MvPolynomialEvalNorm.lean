/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# Valuation lower bounds for evaluations of residually independent polynomials

Let `v : Valuation K Γ₀` be a valuation on a field `K` whose valuation ring `v.integer` has an
infinite residue field. If a finite family `b : ι → MvPolynomial σ v.integer` remains linearly
independent after reducing coefficients modulo the maximal ideal, then for every family of scalars
`α : ι → K`, there is a single integral point `y : σ → v.integer` at which
`v (∑ s, α s * eval y (b s))` is at least `v (α t)` for every `t : ι`.

The proof scales by a scalar `α t₀` of maximal valuation to obtain an integral linear combination
whose reduction modulo the maximal ideal is nonzero, evaluates at a non-root over the infinite
residue field via `MvPolynomial.exists_eval_ne_zero`, and lifts the point to `v.integer`.

## Main results

* `TauCeti.exists_forall_valuation_le_valuation_sum_mul_eval`: uniform form giving a single
  integral point `y` attaining at least `v (α t)` for every `t : ι`.
* `TauCeti.exists_valuation_le_valuation_sum_mul_eval`: pointwise form for a fixed index `t₁ : ι`.

## Provenance

Adapted from `New.exists_norm_le_norm_sum_mul_eval` in
`grh/src/New/Derivatives/Divisibility/Count.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset MvPolynomial

/-- If a finite family of multivariate polynomials over the valuation ring `v.integer` remains
linearly independent over the infinite residue field of `v.integer`, then for any scalars
`α : ι → K`, there is a single integral point `y : σ → v.integer` such that
`v (α t) ≤ v (∑ s, α s * (eval y (b s) : K))` for every `t : ι`. -/
theorem exists_forall_valuation_le_valuation_sum_mul_eval
    {K Γ₀ ι σ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Fintype ι]
    (v : Valuation K Γ₀) [Infinite (IsLocalRing.ResidueField v.integer)]
    {b : ι → MvPolynomial σ v.integer}
    (hb : LinearIndependent (IsLocalRing.ResidueField v.integer)
      fun t : ι ↦ (b t).map (IsLocalRing.residue v.integer))
    (α : ι → K) :
    ∃ y : σ → v.integer, ∀ t : ι, v (α t) ≤ v (∑ s : ι, α s * (eval y (b s) : K)) := by
  obtain h_empty | h_nonempty := isEmpty_or_nonempty ι
  · exact ⟨0, fun t ↦ h_empty.elim t⟩
  obtain ⟨t₀, h_max⟩ := Finite.exists_max fun t : ι ↦ v (α t)
  by_cases h_zero : α t₀ = 0
  · exact ⟨0, fun t ↦ (h_max t).trans (by simp [h_zero])⟩
  let β : ι → v.integer := fun t ↦
    ⟨α t / α t₀, by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ (h_max t) zero_le⟩
  have hβ : β t₀ = 1 := Subtype.ext (div_self h_zero)
  have h_ne : (∑ t, β t • b t).map (IsLocalRing.residue v.integer) ≠ 0 := fun h_map ↦ by
    have h_dep := Fintype.linearIndependent_iff.mp hb
      (fun t ↦ IsLocalRing.residue v.integer (β t))
      (by simpa only [map_sum, smul_eq_C_mul, map_mul, map_C] using h_map) t₀
    simp [hβ] at h_dep
  obtain ⟨x, hx⟩ := MvPolynomial.exists_eval_ne_zero h_ne
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective.comp_left x
  have h_unit : IsUnit (eval y (∑ t, β t • b t)) := by
    rwa [← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.map_eval]
  have h_val_one : v (eval y (∑ t, β t • b t) : K) = 1 :=
    (Valuation.integer.integers v).one_of_isUnit h_unit
  have h_eq : ∑ t, α t * (eval y (b t) : K) = α t₀ * (eval y (∑ t, β t • b t) : K) := by
    simp [β, mul_sum, smul_eval, ← mul_assoc, mul_div_cancel₀ _ h_zero]
  refine ⟨y, fun t ↦ (h_max t).trans_eq ?_⟩
  rw [h_eq, map_mul, h_val_one, mul_one]

/-- Pointwise form of `TauCeti.exists_forall_valuation_le_valuation_sum_mul_eval`: for any fixed
index `t₁ : ι`, there is an integral point `y : σ → v.integer` with
`v (α t₁) ≤ v (∑ t, α t * (eval y (b t) : K))`. -/
theorem exists_valuation_le_valuation_sum_mul_eval
    {K Γ₀ ι σ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Fintype ι]
    (v : Valuation K Γ₀) [Infinite (IsLocalRing.ResidueField v.integer)]
    {b : ι → MvPolynomial σ v.integer}
    (hb : LinearIndependent (IsLocalRing.ResidueField v.integer)
      fun t : ι ↦ (b t).map (IsLocalRing.residue v.integer))
    (α : ι → K) (t₁ : ι) :
    ∃ y : σ → v.integer, v (α t₁) ≤ v (∑ t : ι, α t * (eval y (b t) : K)) :=
  let ⟨y, hy⟩ := exists_forall_valuation_le_valuation_sum_mul_eval v hb α
  ⟨y, hy t₁⟩

end TauCeti
