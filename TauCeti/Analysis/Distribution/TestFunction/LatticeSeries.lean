/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Algebra.Order.Ring.Basic
import TauCeti.Analysis.Distribution.TestFunction.DominatedSeries

/-!
# Weighted lattice series of modulated cutoffs

Let `χ` be a smooth function supported in a compact set `K` and `Λ` a discrete subgroup of `E`.
The derivatives of the modulated cutoffs `χ.modulate m` grow at most polynomially in `m`
(`ContDiffMapSupportedIn.seminorm_modulate_le`), so a series `∑ m, c m • χ.modulate m` over `Λ`
converges in `𝓓_K` as soon as its coefficients decay faster than every power of `1 + ‖m‖`.

This file treats coefficients `a x m` depending on a parameter `x` with a weight `w x ≥ 0`, which
decay faster than every power of `1 + w x + ‖m‖`, uniformly in `x`. Weighted by `(1 + w x) ^ N`,
their products with the seminorms of the modulated cutoffs are still dominated by summable
sequences, uniformly in `x`
(`ContDiffMapSupportedIn.exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le`). If the
parameter lies in a topological space, the coefficients depend continuously on it and the weight
tends to infinity at infinity, then the weighted series together with `0` form a compact set of
`𝓓_K` (`ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate`).

These are the compactness arguments behind the continuity of pullbacks in the normal topology of
Hörmander's spaces `𝓓'_Γ`: there `a x m` are the coefficients of a lattice series of a localized
Fourier transform, the parameter `x` is a frequency and `w x` is its norm.
-/

public section

noncomputable section

open Filter Set TopologicalSpace
open scoped Real Distributions Topology

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {K : Compacts E} (Λ : Submodule ℤ E)
  [DiscreteTopology Λ]

/-- **Domination of weighted lattice series of modulated cutoffs.** If the coefficients `a x m`
decay faster than every power of `1 + w x + ‖m‖`, uniformly in `x`, then the products of the
weighted coefficients `(1 + w x) ^ N a x m` with the seminorms of the modulated cutoffs
`χ.modulate m` are dominated by nonnegative summable sequences, uniformly in `x`. -/
theorem exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le {X : Type*} {w : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) {a : X → Λ → ℂ}
    (ha : ∀ M : ℕ, ∃ C, ∀ x (m : Λ), (1 + w x + ‖(m : E)‖) ^ M * ‖a x m‖ ≤ C) (χ : 𝓓_{K}(E, F))
    (N : ℕ) :
    ∃ b : ℕ → Λ → ℝ, (∀ k, Summable (b k)) ∧ (∀ k m, 0 ≤ b k m) ∧
      ∀ x k m, (1 + w x) ^ N * ‖a x m‖ * N[ℂ]_{K, k} (χ.modulate (m : E)) ≤ b k m := by
  set q := Module.finrank ℤ Λ + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv Λ (r := q) (by omega)
  choose C hC using fun k : ℕ ↦ ha (N + k + q)
  set S : ℕ → ℝ := fun k ↦ ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ
  have hS (k : ℕ) : 0 ≤ S k := apply_nonneg _ _
  refine ⟨fun k m ↦ max (C k) 0 * (S k * (1 + 2 * π) ^ k) * ((1 + ‖(m : E)‖) ^ q)⁻¹,
    fun k ↦ hq.mul_left _, fun k m ↦ by have := hS k; positivity, fun x k m ↦ ?_⟩
  set t := ‖(m : E)‖
  have ht : 0 ≤ t := norm_nonneg _
  have hwx := hw x
  have := hS k
  -- The derivatives of the modulated cutoff grow at most polynomially.
  have hmod : N[ℂ]_{K, k} (χ.modulate (m : E)) ≤ S k * (1 + 2 * π) ^ k * (1 + t) ^ k := by
    calc _ ≤ S k * (1 + 2 * π * t) ^ k := seminorm_modulate_le _ _ k
      _ ≤ S k * ((1 + 2 * π) * (1 + t)) ^ k := by
          gcongr
          nlinarith [Real.pi_pos]
      _ = S k * (1 + 2 * π) ^ k * (1 + t) ^ k := by rw [mul_pow, mul_assoc]
  have hpow : (1 + w x) ^ N * (1 + t) ^ (k + q) ≤ (1 + w x + t) ^ (N + k + q) :=
    TauCeti.one_add_pow_mul_one_add_pow_le hwx ht (by omega)
  rw [le_mul_inv_iff₀ (by positivity)]
  calc (1 + w x) ^ N * ‖a x m‖ * N[ℂ]_{K, k} (χ.modulate (m : E)) * (1 + t) ^ q
      ≤ (1 + w x) ^ N * ‖a x m‖ * (S k * (1 + 2 * π) ^ k * (1 + t) ^ k) * (1 + t) ^ q := by
        gcongr
    _ = (S k * (1 + 2 * π) ^ k) * ((1 + w x) ^ N * (1 + t) ^ (k + q) * ‖a x m‖) := by ring
    _ ≤ (S k * (1 + 2 * π) ^ k) * ((1 + w x + t) ^ (N + k + q) * ‖a x m‖) := by gcongr
    _ ≤ (S k * (1 + 2 * π) ^ k) * max (C k) 0 := by
        gcongr
        exact (hC k x m).trans (le_max_left _ _)
    _ = _ := by ring

variable [CompleteSpace F]

/-- **Weighted lattice series of modulated cutoffs form a compact set.** If moreover the
coefficients `a x m` depend continuously on a parameter `x` of a topological space and the
continuous weight `w x` tends to infinity at infinity, then the series
`∑ m, ((1 + w x) ^ N a x m) • χ.modulate m` depend continuously on `x` and tend to zero at
infinity, so that together with `0` they form a compact set of `𝓓_K`. -/
theorem isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate {X : Type*} [TopologicalSpace X]
    {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (hwc : Continuous w) (hwt : Tendsto w (cocompact X) atTop)
    {a : X → Λ → ℂ} (hac : ∀ m, Continuous fun x ↦ a x m)
    (ha : ∀ M : ℕ, ∃ C, ∀ x (m : Λ), (1 + w x + ‖(m : E)‖) ^ M * ‖a x m‖ ≤ C) (χ : 𝓓_{K}(E, F))
    (N : ℕ) :
    IsCompact (insert 0 (range fun x ↦ ∑' m : Λ,
      ((((1 + w x) ^ N : ℝ) : ℂ) * a x m) • χ.modulate (m : E))) := by
  obtain ⟨b, hb, hb0, hbound⟩ :=
    exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le Λ hw ha χ N
  have hnorm (x : X) (m : Λ) : ‖(((1 + w x) ^ N : ℝ) : ℂ) * a x m‖ = (1 + w x) ^ N * ‖a x m‖ := by
    have := hw x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine isCompact_insert_range_tsum_smul_of_dominated hb hb0 (fun x k m ↦ ?_) (fun m ↦ ?_)
    fun m ↦ ?_
  · rw [hnorm]
    exact hbound x k m
  · exact (Complex.continuous_ofReal.comp ((continuous_const.add hwc).pow N)).mul (hac m)
  -- The weighted coefficients are at most `C (1 + w x)⁻¹`, by the decay estimate of order `N + 1`.
  obtain ⟨C, hC⟩ := ha (N + 1)
  have hinv := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hwt)).const_mul C
  rw [mul_zero] at hinv
  refine squeeze_zero_norm (fun x ↦ ?_) hinv
  have hwx := hw x
  rw [hnorm, Function.comp_apply, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (1 + w x) ^ N * ‖a x m‖ * (1 + w x) = (1 + w x) ^ (N + 1) * ‖a x m‖ := by ring
    _ ≤ (1 + w x + ‖(m : E)‖) ^ (N + 1) * ‖a x m‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (le_add_of_nonneg_right (norm_nonneg _)) _) (norm_nonneg _)
    _ ≤ C := hC x m

end ContDiffMapSupportedIn
