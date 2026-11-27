/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Bounds
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.WeightBounds

/-!
# A lower bound for the main amount of a theta-lift chain

In each direction, the logarithmic jet size is reduced by a prime sum whose cap varies with
the prime power. The two-valued weights limit the contributing prime powers to the second
cutoff. The resulting bound on the subtracted sums leaves a contribution from the directions
of weight `b`; multiplying by the product of the ranks gives a lower bound for use in
covolume comparisons.

The weights and normalization follow `New.Data.le_mainAmount` in
`grh/src/New/Reduction/PrimeSums.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

/-- For the two-valued weights `b` on `t` and `x * b / X` elsewhere, the rank-scaled direction
amount is at least `x⁴ · #s · (xb)`. The cap at the prime power `n` in direction `i` is the
weight at `next i n`. Here `X` is the second cutoff, `#s = F * T`, and `c` is the logarithmic
jet scale. -/
theorem le_mul_directionAmount_of_primeWeight {ι : Type*} [DecidableEq ι] (d : ℕ) [Fact d.Prime]
    {s t : Finset ι} {x X b m k F T : ℕ} {c : ℝ} (next : ι → ℕ → ι)
    (ht : t ⊆ s) (hxX : x ≤ X) (hXb : X ∣ b) (hL : 2 ≤ log b)
    (hsep : log (b : ℝ) ^ 8 ≤ x) (hlog : 4 * log X ≤ log b) (hc : 2 * log b ≤ c)
    (hT : (T : ℝ) ≤ t.card * log b) (hcard : s.card = F * T) (hF : (F : ℝ) ≤ log b)
    (hm : (x : ℝ) ≤ (m : ℝ) ^ 2) (hk : exp (-2) * (x : ℝ) ^ 5 ≤ k) :
    let κ : ι → ℕ := fun i ↦ if i ∈ t then b else x * b / X
    (x : ℝ) ^ 4 * s.card * (x * b : ℝ) ≤ (m * k : ℝ) * directionAmount s κ c
      (fun i ↦ ∑ n ∈ Ioc 0 (x * b), primeWeight d 1 n * max (κ i / (n : ℝ) - κ (next i n)) 0) := by
  intro κ
  have hx : 1 ≤ x := Nat.cast_pos.mp ((pow_pos (by linarith : 0 < log (b : ℝ)) 8).trans_le hsep)
  have hX : 0 < X := hx.trans hxX
  have hκ (i : ι) : κ i ∈ Set.Icc (x * b / X) b :=
    (dvd_and_cutoffWeight_mem_Icc (i ∈ t) hxX (by simpa using hXb : 1 * X ∣ b)).2
  have hcap (i j : ι) : (κ i : ℝ) ≤ X * κ j := by
    have hdiv : X ∣ x * b := hXb.trans (dvd_mul_left b x)
    have hmul : X * κ j ≥ x * b := by
      calc
        x * b = X * (x * b / X) := (Nat.mul_div_cancel' hdiv).symm
        _ ≤ X * κ j := Nat.mul_le_mul_left _ (hκ j).1
    exact_mod_cast (hκ i).2.trans ((Nat.le_mul_of_pos_left b hx).trans hmul)
  have hP (i : ι) : (∑ n ∈ Ioc 0 (x * b),
      primeWeight d 1 n * max (κ i / (n : ℝ) - κ (next i n)) 0) ≤ κ i * log b := by
    have h := sum_prime_weight_mul_max_mem_Icc (y := (κ i : ℝ)) (X := (X : ℝ))
      (N := x * b) (w := fun n ↦ (κ (next i n) : ℝ)) (Nat.cast_nonneg _) (by exact_mod_cast hX)
      (fun n _ ↦ ⟨primeWeight_nonneg d 1 n, primeWeight_le_two_mul_vonMangoldt d 1 n⟩)
      (fun n _ ↦ hcap i (next i n))
    refine h.2.trans ?_
    calc
      4 * (κ i : ℝ) * log X = κ i * (4 * log X) := by ring
      _ ≤ κ i * log b := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  have hrank := mul_pow_five_le_mul_of_separated_scales hL hF hsep (Nat.cast_nonneg _) hm hk
  exact le_rank_mul_directionAmount ht hc (fun i hi ↦ by simp [κ, hi]) hT (fun i _ ↦ hP i)
    hcard hrank

end TauCeti.OneSidedBound
