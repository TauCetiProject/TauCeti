/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A logarithmic bound at one for Dirichlet L-functions

For a nonprincipal complex Dirichlet character of positive level `N`, the continued value at
one has norm at most `2 + log N`. This estimate also applies to imprimitive characters; for
primitive characters the level is the conductor.

Cancellation within each full period bounds the block after the first by
`1 / k - 1 / (k + 1)`. The first block is bounded by a harmonic number. Thus the estimate
uses the ordered boundary limit, not an absolutely convergent Dirichlet series at one.

## References

* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Finset Filter Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

private lemma norm_block_le (hχ : χ ≠ 1) {k : ℕ} (hk : 0 < k) :
    ‖∑ n ∈ range N, χ (k * N + n : ℕ) / ((k * N + n : ℕ) : ℂ)‖ ≤
      (k : ℝ)⁻¹ - (k + 1 : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- Subtract the reciprocal of the right endpoint using cancellation over a full period.
  have hcancel : ∑ n ∈ range N, χ n * (((k + 1) * N : ℕ) : ℂ)⁻¹ = 0 := by
    rw [← sum_mul]
    rw [sum_range_eq_zero_of_ne_one χ hχ, zero_mul]
  have hrewrite : (∑ n ∈ range N, χ (k * N + n : ℕ) / ((k * N + n : ℕ) : ℂ)) =
      ∑ n ∈ range N, χ n *
        (((k * N + n : ℕ) : ℂ)⁻¹ - (((k + 1) * N : ℕ) : ℂ)⁻¹) := by
    simp only [mul_sub, sum_sub_distrib, hcancel, sub_zero, div_eq_mul_inv]
    apply sum_congr rfl
    intro n hn
    -- Character values are periodic modulo the level N.
    simp [Nat.cast_add, Nat.cast_mul]
  rw [hrewrite]
  calc
    _ ≤ ∑ n ∈ range N, ‖χ n *
        (((k * N + n : ℕ) : ℂ)⁻¹ - (((k + 1) * N : ℕ) : ℂ)⁻¹)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N,
        (((k * N : ℕ) : ℝ)⁻¹ - (((k + 1) * N : ℕ) : ℝ)⁻¹) := by
      apply sum_le_sum
      intro n hn
      -- Each reciprocal lies between the reciprocals of the two block endpoints.
      have hnN := mem_range.mp hn
      have hlow : (0 : ℝ) < ((k * N + n : ℕ) : ℝ) := by push_cast; positivity
      have hleft : (((k + 1) * N : ℕ) : ℝ)⁻¹ ≤ ((k * N + n : ℕ) : ℝ)⁻¹ := by
        apply inv_anti₀ hlow
        have hle : k * N + n ≤ (k + 1) * N := by rw [Nat.add_mul, one_mul]; omega
        exact_mod_cast hle
      have hright : ((k * N + n : ℕ) : ℝ)⁻¹ ≤ ((k * N : ℕ) : ℝ)⁻¹ := by
        apply inv_anti₀ (by push_cast; positivity : (0 : ℝ) < ((k * N : ℕ) : ℝ))
        exact_mod_cast Nat.le_add_right (k * N) n
      have hnorm : ‖(((k * N + n : ℕ) : ℂ)⁻¹ -
          (((k + 1) * N : ℕ) : ℂ)⁻¹)‖ =
          ((k * N + n : ℕ) : ℝ)⁻¹ - (((k + 1) * N : ℕ) : ℝ)⁻¹ := by
        have hcast : (((k * N + n : ℕ) : ℂ)⁻¹ - (((k + 1) * N : ℕ) : ℂ)⁻¹) =
            ((((k * N + n : ℕ) : ℝ)⁻¹ - (((k + 1) * N : ℕ) : ℝ)⁻¹) : ℝ) := by
          simp only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [hcast, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hleft)]
      rw [norm_mul, hnorm]
      exact (mul_le_of_le_one_left (sub_nonneg.mpr hleft) (χ.norm_le_one n)).trans
        (sub_le_sub_right hright _)
    _ = (k : ℝ)⁻¹ - (k + 1 : ℝ)⁻¹ := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

private lemma norm_first_block_le :
    ‖∑ n ∈ range N, χ n / (n : ℂ)‖ ≤ (harmonic N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ range N, ‖χ n / (n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, (n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      simpa [norm_div, Complex.norm_natCast, div_eq_mul_inv] using
        mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg n)) (χ.norm_le_one n)
    _ ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      rw [← sum_range_add_sum_Ico (f := fun n : ℕ ↦ (n : ℝ)⁻¹) (NeZero.pos N)]
      simp only [sum_range_one, Nat.cast_zero, inv_zero, zero_add]
      exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Icc_self) (by intros; positivity)

private lemma norm_sum_mul_level_le (hχ : χ ≠ 1) {k : ℕ} (hk : 0 < k) :
    ‖∑ n ∈ range (k * N), χ n / (n : ℂ)‖ ≤
      (harmonic N : ℝ) + 1 - (k : ℝ)⁻¹ := by
  induction k, hk using Nat.le_induction with
  | base => simpa using norm_first_block_le χ
  | succ k hk ih =>
    rw [Nat.add_mul, one_mul, sum_range_add]
    calc
      _ ≤ ‖∑ n ∈ range (k * N), χ n / (n : ℂ)‖ +
          ‖∑ n ∈ range N, χ (k * N + n : ℕ) / ((k * N + n : ℕ) : ℂ)‖ := norm_add_le _ _
      _ ≤ ((harmonic N : ℝ) + 1 - (k : ℝ)⁻¹) +
          ((k : ℝ)⁻¹ - (k + 1 : ℝ)⁻¹) := add_le_add ih (norm_block_le χ hχ hk)
      _ = (harmonic N : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)⁻¹ := by push_cast; ring

/-- The continued value at one of a nonprincipal character is bounded by the first harmonic
block plus one. No primitivity assumption is needed. -/
theorem norm_LFunction_one_le_harmonic_add_one (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ (harmonic N : ℝ) + 1 := by
  have hlim := (χ.tendsto_sum_Icc_div_LFunction_one hχ).comp
    (tendsto_id.atTop_mul_const' (NeZero.pos N))
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_gt_atTop 0] with k hk
  have heq : (∑ n ∈ Icc 1 (k * N), χ n / (n : ℂ)) =
      ∑ n ∈ range (k * N), χ n / (n : ℂ) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega)]
    simp [sum_range_succ, χ.map_zero' (fun h => hχ (χ.level_one' h))]
  simp only [Function.comp_apply, id_eq]
  rw [heq]
  exact (norm_sum_mul_level_le χ hχ hk).trans (sub_le_self _ (by positivity))

/-- A logarithmic level bound for the continued Dirichlet L-value at one. For primitive
characters this is a logarithmic conductor bound. -/
theorem norm_LFunction_one_le_two_add_log (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 2 + Real.log N := by
  have := harmonic_le_one_add_log N
  linarith [χ.norm_LFunction_one_le_harmonic_add_one hχ]

end DirichletCharacter
