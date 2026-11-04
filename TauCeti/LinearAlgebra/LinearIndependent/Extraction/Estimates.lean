/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import TauCeti.Algebra.Order.BigOperators.Fin

/-!
# Product estimates for independent vectors extracted through field towers

From `[K : F] * k` vectors with independent images under an `F`-linear map one may select `k`
vectors independent over `K`, the `j`-th of them (counted from zero) at position at most
`[K : F] * j` (`TauCeti.exists_linearIndependent_comp_finrank_mul`). If the original family
carries nonnegative quantities bounded by a monotone sequence `c`, as a family of successive
minima does, then the index bounds control the quantities of the selected vectors: the
`[K : F]`-th power of their product is at most the product of the whole sequence `c`.

## Main results

* `TauCeti.exists_linearIndependent_comp_finrank_mul_prod_pow_le`: a `K`-independent selection
  of `k` vectors whose quantities `b` have product with `[K : F]`-th power at most `∏ l, c l`.
* `TauCeti.exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv`: for real quantities, the
  same selection with product at most `(∏ l, c l) ^ (1 / [K : F])`.
-/

public section

open Module

namespace TauCeti

variable {F K E V W R : Type*} [Field F] [DivisionRing K] [Semiring E] [Nontrivial E]
  [Algebra F K] [Algebra F E] [Module.Finite F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
  [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R] [PosMulMono R]

/-- From `[K : F] * k` vectors with independent images under an `F`-linear map, carrying
nonnegative quantities `b` bounded by a monotone sequence `c`, select `k` vectors independent
over `K`, the `j`-th at position at most `[K : F] * j`, such that the `[K : F]`-th power of the
product of their quantities is at most the product of the whole sequence `c`. -/
theorem exists_linearIndependent_comp_finrank_mul_prod_pow_le {k : ℕ} {f : V →ₗ[F] W}
    {u : Fin (finrank F K * k) → V} (h : LinearIndependent E (f ∘ u))
    {b c : Fin (finrank F K * k) → R} (hb0 : ∀ l, 0 ≤ b l) (hbc : ∀ l, b l ≤ c l)
    (hc : Monotone c) :
    ∃ s : Fin k → Fin (finrank F K * k), LinearIndependent K (u ∘ s) ∧
      (∀ j, (s j : ℕ) ≤ finrank F K * j) ∧ (∏ j, b (s j)) ^ finrank F K ≤ ∏ l, c l := by
  obtain ⟨s, hs, hsD⟩ := exists_linearIndependent_comp_finrank_mul (K := K) h
  have := PosMulMono.toMulPosMono (α := R)
  exact ⟨s, hs, hsD, (pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ ↦ hb0 _)
    (Finset.prod_le_prod₀ (fun _ _ ↦ hb0 _) fun _ _ ↦ hbc _) _).trans
    (Fin.prod_pow_le_prod_of_monotone (fun l ↦ (hb0 l).trans (hbc l)) hc hsD)⟩

/-- The real form of `exists_linearIndependent_comp_finrank_mul_prod_pow_le`: from
`[K : F] * k` vectors with independent images under an `F`-linear map, carrying nonnegative real
quantities `b` bounded by a monotone sequence `c`, select `k` vectors independent over `K`, the
`j`-th at position at most `[K : F] * j`, such that the product of their quantities is at most
`(∏ l, c l) ^ (1 / [K : F])`. -/
theorem exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv {k : ℕ} {f : V →ₗ[F] W}
    {u : Fin (finrank F K * k) → V} (h : LinearIndependent E (f ∘ u))
    {b c : Fin (finrank F K * k) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbc : ∀ l, b l ≤ c l)
    (hc : Monotone c) :
    ∃ s : Fin k → Fin (finrank F K * k), LinearIndependent K (u ∘ s) ∧
      (∀ j, (s j : ℕ) ≤ finrank F K * j) ∧
      ∏ j, b (s j) ≤ (∏ l, c l) ^ (finrank F K : ℝ)⁻¹ := by
  obtain ⟨s, hs, hsD, hprod⟩ := exists_linearIndependent_comp_finrank_mul_prod_pow_le h hb0 hbc hc
  refine ⟨s, hs, hsD, ?_⟩
  have hb : 0 ≤ ∏ j, b (s j) := Finset.prod_nonneg fun j _ ↦ hb0 _
  calc ∏ j, b (s j)
      = ((∏ j, b (s j)) ^ finrank F K) ^ (finrank F K : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast hb finrank_pos.ne').symm
    _ ≤ (∏ l, c l) ^ (finrank F K : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hb _) hprod (by positivity)

end TauCeti
