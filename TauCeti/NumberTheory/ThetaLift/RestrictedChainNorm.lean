/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SumKernelChain
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The archimedean size of a restricted theta chain

After evaluation at class representatives, each translation contributes a finite chain of
kernels. The class counts and the sum of the norms of the translation coefficients cost part
of the logarithmic error. Restricting the last lift saves a multiple of `log N` at the level
prime `N`. The bound below combines these costs with the saving from the long rows.

The budgets are those of `New.Data.weylNormSq_restrictedChain_le` in
[lsernau/grh-lean, `New/UpperBound/Size/ArchimedeanSize.lean` at `72fead1`][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/UpperBound/Size/ArchimedeanSize.lean
-/

public section

open Finset Real
open LinearMap (sumKernelChain norm_sumKernelChain_le_exp)

namespace TauCeti.ThetaLift

/-- The polynomial overhead in the archimedean estimate, including the shortfall in the level
saving, fits in one quarter of the logarithmic error allowance. -/
private theorem restrictedChain_overhead_le {x b f g l : ℝ} {m : ℕ}
    (hb : x ^ 89 ≤ b) (hb' : 13 ≤ log b) (hf : 1 ≤ f) (hf' : f ≤ x ^ 12)
    (hm : (m : ℝ) ≤ x) (hg : g ≤ x ^ 41) (hl : 0 ≤ l) (hl' : l ≤ 30 * m * log b)
    (hlog : log b ≤ x) :
    2 * m * (x ^ 30 + x ^ 50) + 2 * x ^ 60 + x ^ 70 + f * m * g * l ≤
      f * (x * b) * log b ^ 3 / 4 := by
  have hx₁ : 1 ≤ x := by linarith only [hb', hlog]
  have hx₀ := zero_le_one.trans hx₁
  have hb₀ : 0 ≤ b := (pow_nonneg hx₀ _).trans hb
  have hpow (i : ℕ) (hi : i ≤ 70) : x ^ i ≤ x ^ 70 := pow_le_pow_right₀ hx₁ hi
  have hlevel : f * m * g * l ≤ 30 * x ^ 56 := by
    calc
      _ ≤ f * m * x ^ 41 * l := by gcongr
      _ ≤ x ^ 12 * x * x ^ 41 * (30 * x * x) := by gcongr; exact hl'.trans (by gcongr)
      _ = _ := by ring
  have hsteps : 2 * m * (x ^ 30 + x ^ 50) ≤ 4 * x ^ 51 := by
    calc
      _ ≤ 2 * x * (x ^ 50 + x ^ 50) := by
        gcongr
        norm_num
      _ = _ := by ring
  have hbudget : x ^ 70 ≤ f * (x * b) := by
    calc
      _ ≤ x ^ 90 := pow_le_pow_right₀ hx₁ (by decide)
      _ = x * x ^ 89 := by ring
      _ ≤ x * b := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hf
  have hcub : (13 : ℝ) ^ 3 ≤ log b ^ 3 := by gcongr
  have hbudget' : 37 * (f * (x * b)) ≤ f * (x * b) * log b ^ 3 / 4 := by
    have h : (148 : ℝ) ≤ log b ^ 3 := by linarith only [hcub]
    linarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ f * (x * b) by positivity)]
  nlinarith only [hsteps, hlevel, hpow 51 (by decide), hpow 56 (by decide),
    hpow 60 (by decide), hbudget, hbudget']

/-- Bound the squared norm of a restricted, weighted sum of `m` finite kernel chains.
Here `rs j` is the row cost of step `j`, `A` the number of long places, `f` the number of all
places, `g` the half-gap, and `l = log N` the logarithmic level. The restriction saves `S * l`,
where `S ≥ A * (x * b) - f * m * g`. The row estimate after the full long-place saving has
leading cost `H`; the output has leading cost `B + H` plus one error unit.

To use the estimate at a complex field automorphism, use the transformed kernels, coefficient
vectors, and translation coefficients. No invariance of complex norms under that automorphism
is required. -/
theorem norm_sq_restricted_chain_le {𝕜 T F : Type*} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup F] [Module 𝕜 F]
    {I V : ℕ → Type*} [∀ j, Fintype (I j)]
    [∀ j, SeminormedAddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    {m : ℕ} [IsBoundedSMul 𝕜 (V m)] (K : T → ∀ j, I j → I (j + 1) → V j →ₗ[𝕜] V (j + 1))
    (R : V m →ₗ[𝕜] F) (t : Finset T) (c : T → 𝕜) {v : I 0 → V 0}
    {x b f g l A S B H : ℝ} {rs : ℕ → ℝ}
    (hb : x ^ 89 ≤ b) (hb' : 13 ≤ log b) (hf : 1 ≤ f) (hf' : f ≤ x ^ 12)
    (hm : (m : ℝ) ≤ x) (hg : g ≤ x ^ 41) (hl : 0 ≤ l) (hl' : l ≤ 30 * m * log b)
    (hlog : log b ≤ x) (hS : A * (x * b) - f * m * g ≤ S)
    (hrow : (∑ j ∈ range m, rs j) - A * (x * b) * l ≤
      H + f * (x * b) * log b ^ 3 / 2 + 32 * (f * (x * b)) * log b)
    (hv : ∀ a, ‖v a‖ ^ 2 ≤ exp B) (hI : ∀ j < m, (Fintype.card (I j) : ℝ) ≤ exp (x ^ 30))
    (hK : ∀ y ∈ t, ∀ j < m, ∀ a b u, ‖K y j a b u‖ ≤ exp (x ^ 50 + rs j / 2) * ‖u‖)
    (hc : ∑ y ∈ t, ‖c y‖ ≤ exp (x ^ 60))
    (hR : ∀ u, ‖R u‖ ^ 2 ≤ exp (x ^ 70 - S * l) * ‖u‖ ^ 2) (z : I m) :
    ‖R (∑ y ∈ t, c y • sumKernelChain (K y) v m z)‖ ^ 2 ≤
      exp (B + H + f * (x * b) * log b ^ 3) := by
  let L := B / 2 + (m : ℝ) * (x ^ 30 + x ^ 50) + (∑ j ∈ range m, rs j) / 2
  have hv' (a : I 0) : ‖v a‖ ≤ exp (B / 2) := by
    rw [exp_half, ← sqrt_sq (norm_nonneg (v a))]
    exact sqrt_le_sqrt (hv a)
  have hsum (y : T) (hy : y ∈ t) : ‖sumKernelChain (K y) v m z‖ ≤ exp L := by
    have h := norm_sumKernelChain_le_exp (K y) hv' hI (hK y hy) z
    have hL : B / 2 + (∑ j ∈ range m, (x ^ 30 + (x ^ 50 + rs j / 2))) = L := by
      simp_rw [← add_assoc (x ^ 30), div_eq_mul_inv]
      rw [sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul]
      dsimp only [L]
      ring
    exact h.trans_eq (congrArg exp hL)
  have hnorm : ‖∑ y ∈ t, c y • sumKernelChain (K y) v m z‖ ≤ exp (x ^ 60 + L) := by
    calc
      _ ≤ ∑ y ∈ t, ‖c y • sumKernelChain (K y) v m z‖ := norm_sum_le _ _
      _ ≤ ∑ y ∈ t, ‖c y‖ * exp L := sum_le_sum fun y hy ↦
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hsum y hy) (norm_nonneg _))
      _ ≤ exp (x ^ 60 + L) := by
        rw [← sum_mul, exp_add (x ^ 60) L]
        exact mul_le_mul_of_nonneg_right hc (exp_nonneg _)
  have hcore := restrictedChain_overhead_le hb hb' hf hf' hm hg hl hl' hlog
  have hlog' : 128 ≤ log b ^ 2 := by
    have h : (13 : ℝ) ^ 2 ≤ log b ^ 2 := by gcongr
    linarith
  have ha : 0 ≤ f * (x * b) * log b := by
    have : 0 ≤ b := (pow_nonneg (by linarith : 0 ≤ x) _).trans hb
    have : 0 ≤ log b := by linarith
    have : 0 ≤ x := by linarith only [hb', hlog]
    have : 0 ≤ f := zero_le_one.trans hf
    positivity
  have hlin := mul_le_mul_of_nonneg_left hlog' ha
  calc
    _ ≤ exp (x ^ 70 - S * l) * exp (x ^ 60 + L) ^ 2 := by
      refine (hR _).trans ?_
      gcongr
    _ ≤ _ := by
      rw [sq, ← exp_add, ← exp_add, exp_le_exp]
      dsimp only [L]
      nlinarith only [hrow, hcore, hlin, mul_le_mul_of_nonneg_right hS hl]

end TauCeti.ThetaLift
