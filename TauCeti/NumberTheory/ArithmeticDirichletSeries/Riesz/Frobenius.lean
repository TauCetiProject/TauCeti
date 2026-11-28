/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Character expansion of Frobenius-restricted Riesz sums

For each summation index, one can average over a finite set of group elements rather than
selecting a single element. In the prime-power application this set is the entire Frobenius coset
of inertia. The coefficients on the character side are then the means of the character over
these cosets, including at ramified primes. A positive cap depending on the group element becomes
a change of scale in each Riesz sum.

The prime-power application is the character expansion in Levent Alpöge's `Deduction.ch_balance`,
in `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean`.
-/

public section

open Finset
open scoped BigOperators

namespace TauCeti

variable {G : Type*} [Group G] [IsMulCommutative G] [Finite G]

open scoped IsMulCommutative in
/-- Inverting the character averages inside a Riesz sum selects the mass of one group element
at each index. The mass is its indicator averaged over the input finset. -/
theorem sum_inv_mul_rieszSum_expect_eq_card_mul_rieszSum_expect_ite [DecidableEq G]
    (F : ℕ → Finset G) (b : ℕ → ℂ) (g : G) (y : ℝ) :
    (∑ χ : G →* ℂˣ, (↑(χ g)⁻¹ : ℂ) *
      rieszSum (fun n ↦ b n * 𝔼 h ∈ F n, (χ h : ℂ)) y) =
    (Nat.card G : ℂ) * rieszSum (fun n ↦ b n * 𝔼 h ∈ F n, if h = g then 1 else 0) y := by
  have : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  simp only [rieszSum_def, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n _ ↦ ?_
  calc
    _ = b n * (∑ χ : G →* ℂˣ, (↑(χ g)⁻¹ : ℂ) * 𝔼 h ∈ F n, (χ h : ℂ)) *
        ((y : ℂ) / n - 1) := by
      simp only [mul_sum, sum_mul]
      exact sum_congr rfl fun χ _ ↦ by ring
    _ = _ := by
      have hinv : (∑ χ : G →* ℂˣ, (↑(χ g)⁻¹ : ℂ) * 𝔼 h ∈ F n, (χ h : ℂ)) =
          (Nat.card G : ℂ) * 𝔼 h ∈ F n, if h = g then 1 else 0 := by
        simp only [Finset.mul_expect]
        rw [← Finset.expect_sum_comm]
        refine Finset.expect_congr rfl fun h _ ↦ ?_
        rw [CommGroup.sum_inv_mul_monoidHom_apply_eq_ite]
        split_ifs <;> simp
      rw [hinv]
      ring

/-- In a sum of capped ramps averaged over `F n`, constrain the group elements to `S` and give
`g ∈ S` a positive cap `w g`. The character expansion uses a first Riesz sum at scale `a / w g`
with coefficient at `n` equal to `b n` times the mean of the character over `F n`.

It suffices to truncate the index sum at any common upper bound `N` on the integer parts of the
rescaled cutoffs. No disjointness or nonemptiness condition on the sets `F n` is required. -/
theorem sum_mul_expect_max_eq_sum_mul_rieszSum_expect [DecidableEq G]
    (S : Finset G) (F : ℕ → Finset G) (b : ℕ → ℂ) (w : G → ℝ) (a : ℝ) (N : ℕ)
    (hw : ∀ g ∈ S, 0 < w g) (hN : ∀ g ∈ S, ⌊a / w g⌋₊ ≤ N) :
    (∑ n ∈ Icc 1 N, b n * 𝔼 h ∈ F n,
      if h ∈ S then (↑(max (a / (n : ℝ) - w h) 0) : ℂ) else 0) =
    (Nat.card G : ℂ)⁻¹ * ∑ g ∈ S, (w g : ℂ) *
      ∑ χ : G →* ℂˣ, (↑(χ g)⁻¹ : ℂ) *
        rieszSum (fun n ↦ b n * 𝔼 h ∈ F n, (χ h : ℂ)) (a / w g) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp_rw [sum_inv_mul_rieszSum_expect_eq_card_mul_rieszSum_expect_ite]
  have hnorm (g : G) (z : ℂ) : (w g : ℂ) * ((Nat.card G : ℂ) * z) =
      (Nat.card G : ℂ) * ((w g : ℂ) * z) := mul_left_comm ..
  simp_rw [hnorm, ← mul_sum, inv_mul_cancel_left₀ hcard]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ g ∈ S,
        b n * (𝔼 h ∈ F n, if h = g then 1 else 0) *
          (↑(max (a / (n : ℝ) - w g) 0) : ℂ) := by
      refine sum_congr rfl fun n _ ↦ ?_
      simp only [mul_assoc, ← mul_sum]
      refine congrArg (b n * ·) ?_
      simp only [Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      refine Finset.expect_congr rfl fun h _ ↦ ?_
      simp [ite_mul, Finset.sum_ite_eq]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun g hg ↦ ?_
      rw [rieszSum_eq_sum_max_of_floor_le _ (hN g hg), mul_sum]
      refine sum_congr rfl fun n _ ↦ ?_
      have hscale : w g * (a / w g / (n : ℝ) - 1) = a / (n : ℝ) - w g := by
        rw [mul_sub, ← mul_div_assoc, mul_div_cancel₀ _ (hw g hg).ne', mul_one]
      have hmax := mul_max_of_nonneg (a / w g / (n : ℝ) - 1) 0 (hw g hg).le
      rw [hscale, mul_zero] at hmax
      rw [← hmax, Complex.ofReal_mul]
      ring

end TauCeti
