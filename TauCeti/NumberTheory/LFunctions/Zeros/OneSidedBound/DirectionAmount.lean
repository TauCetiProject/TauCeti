/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Bounds

/-!
# Lower bound for the main amount of a theta-lift chain

With the two weights `b` and `⌊xb/X⌋`, every jet order is at most `b` and every
prime sum has effective cutoff `X`, even when the division is not exact. The directions
with weight `b` then supply a lower bound for the total remaining jet size. Multiplication
by the chain length and the source rank gives a lower bound for the main amount.

The estimates correspond to `New.Data.primeSum_mem_Icc` and `New.Data.le_mainAmount`
in `grh/src/New/Reduction/PrimeSums.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

/-- The main amount is at least `x⁴ * #s * (x*b)` for the two-cutoff weights `b` on `t`
and `x*b/X` off `t`. Here `m` is the length of the chain, `k` the source rank, `F` the
number of residue classes, and `c` the logarithmic jet scale. The prime sum at each direction
uses the weight of the direction reached by `next`; the bound is independent of this map. -/
theorem le_rank_mul_directionAmount_of_two_cutoffs {ι : Type*} [DecidableEq ι]
    (d : ℕ) [Fact d.Prime] {s t : Finset ι} (next : ℕ → ι → ι) {x X b m k F T : ℕ} {c : ℝ}
    (ht : t ⊆ s) (hxX : x ≤ X) (hXb : X ^ 4 ≤ b)
    (hb : 2 ≤ log (b : ℝ)) (hsep : log (b : ℝ) ^ 8 ≤ x) (hm : x ≤ m ^ 2)
    (hk : exp (-2) * (x : ℝ) ^ 5 ≤ k) (hF : F ≤ log (b : ℝ))
    (hc : 2 * log (b : ℝ) ≤ c) (hT : T ≤ t.card * log (b : ℝ)) (hcard : s.card = F * T) :
    let κ (i : ι) := if i ∈ t then b else x * b / X
    (x : ℝ) ^ 4 * s.card * ((x : ℝ) * b) ≤ (m : ℝ) * k * directionAmount s κ c
      (fun i ↦ ∑ n ∈ Finset.Ioc 0 (x * b),
        primeWeight d 1 n * max ((κ i : ℝ) / n - (κ (next n i) : ℝ)) 0) := by
  intro κ
  have hx : 2 ≤ x := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 8
    exact_mod_cast (by norm_num at h; linarith : (2 : ℝ) ≤ x)
  have hX : 0 < X := by omega
  have hXb₀ : X ≤ b := (Nat.le_self_pow (by decide : 4 ≠ 0) _).trans hXb
  have hsmall : x * b / X ≤ b := Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ hxX)
  -- Rounding costs less than `X ≤ b`, while the numerator is at least `2 * b`.
  have hprod : b ≤ X * (x * b / X) := by
    have hm₁ := Nat.mod_lt (x * b) hX
    have hm₂ := Nat.mod_add_div (x * b) X
    have hm₃ := Nat.mul_le_mul_right b hx
    omega
  have hupper (i : ι) : κ i ≤ b := by
    by_cases hi : i ∈ t <;> simp [κ, hi, hsmall]
  have hlower (i : ι) : b ≤ X * κ i :=
    hprod.trans (Nat.mul_le_mul_left _ (by simp [κ, apply_ite, hsmall]))
  have hlogs : 4 * log (X : ℝ) ≤ log (b : ℝ) := by
    have hXb' : (X : ℝ) ^ 4 ≤ (b : ℝ) := by exact_mod_cast hXb
    simpa [log_pow] using log_le_log (by positivity) hXb'
  have hrank : (F : ℝ) * (x : ℝ) ^ 5 ≤ (m : ℝ) * k :=
    mul_pow_five_le_mul_of_separated_scales hb hF hsep (Nat.cast_nonneg m)
      (by exact_mod_cast hm) hk
  refine le_rank_mul_directionAmount ht hc (fun i hi ↦ by simp [κ, hi]) hT ?_ hcard hrank
  intro i _
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsum := sum_prime_weight_mul_max_mem_Icc (a := primeWeight d 1) (N := x * b)
    (w := fun n ↦ (κ (next n i) : ℝ)) (Nat.cast_nonneg (κ i)) hX₁
    (fun n _ ↦ ⟨primeWeight_nonneg d 1 n, primeWeight_le_two_mul_vonMangoldt d 1 n⟩)
    (fun n _ ↦ by exact_mod_cast (hupper i).trans (hlower (next n i)))
  exact hsum.2.trans (by
    simpa [mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg (κ i)))

end TauCeti.OneSidedBound
