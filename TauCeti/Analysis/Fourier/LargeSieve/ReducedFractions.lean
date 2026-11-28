/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.Analysis.Fourier.LargeSieve.Basic
import TauCeti.Analysis.Normed.Group.AddCircle.Rational
import TauCeti.Data.ZMod.Units

/-!
# The additive large sieve over reduced fractions

The reduced fractions `b / q` with `0 ≤ b < q ≤ Q` and `gcd(b, q) = 1` are pairwise at distance at
least `1 / Q ^ 2` on the circle `ℝ / ℤ`. Bombieri's additive large sieve inequality, applied to
this family, bounds the mean square of an exponential sum `S(t) = ∑_{j < H} a_j e((M + j) t)` over
these points: `∑_{1 ≤ q ≤ Q} ∑_{b mod q, gcd(b, q) = 1} |S(b / q)| ^ 2 ≤ (H + 2 Q ^ 2) ∑ |a_j| ^ 2`.

The constant `H + 2 Q ^ 2` is the one supplied by the form of the additive large sieve proved in
`TauCeti.Analysis.Fourier.LargeSieve.Basic`. It is weaker than the sharp constant `H - 1 + Q ^ 2`.

## Main results

* `TauCeti.sum_Icc_sum_filter_coprime_norm_sum_fourierChar_sq_le`: the inequality with the inner
  sum over the natural numbers `b < q` coprime to `q`.
* `TauCeti.sum_range_sum_units_norm_sum_fourierChar_sq_le`: the same inequality with the moduli
  written `q + 1` for `q < Q` and the inner sum over the units `u` of `ZMod (q + 1)`, at the points
  `u.val / (q + 1)`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 16, §16.1, Theorem 16.1.
-/

public section

open Finset

namespace TauCeti

/-- **The additive large sieve over reduced fractions.** For every integer `M`, natural numbers
`H` and `Q`, and coefficients `a : Fin H → ℂ`,
`∑_{1 ≤ q ≤ Q} ∑_{b < q, gcd(b, q) = 1} |∑_j a_j e((M + j) b / q)| ^ 2` is at most
`(H + 2 Q ^ 2) ∑_j |a_j| ^ 2`.
The modulus `q = 1` contributes its single point `0`. -/
theorem sum_Icc_sum_filter_coprime_norm_sum_fourierChar_sq_le (M : ℤ) (H Q : ℕ) (a : Fin H → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (·.Coprime q),
        ‖∑ j : Fin H, a j * (Real.fourierChar (((M : ℝ) + (j : ℕ)) * ((b : ℝ) / q)) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 * (Q : ℝ) ^ 2) * ∑ j : Fin H, ‖a j‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simpa using mul_nonneg (Nat.cast_nonneg H) (sum_nonneg fun j _ ↦ sq_nonneg ‖a j‖)
  have hQ' : (0 : ℝ) < Q := Nat.cast_pos.2 hQ
  set s : Finset (Σ _ : ℕ, ℕ) := (Icc 1 Q).sigma fun q ↦ (range q).filter (·.Coprime q) with hs
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      1 / (Q : ℝ) ^ 2 ≤ ‖(((i.2 : ℝ) / i.1 - (j.2 : ℝ) / j.1 : ℝ) : UnitAddCircle)‖ := by
    rintro ⟨p, b⟩ hi ⟨q, c⟩ hj hij
    simp only [hs, mem_sigma, mem_Icc, mem_filter, mem_range] at hi hj
    refine one_div_sq_le_norm_unitAddCircle_div_sub_div hi.1.2 hj.1.2 hi.2.1 hj.2.1 hi.2.2
      hj.2.2 fun h ↦ hij ?_
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  have key := sum_norm_sum_fourierChar_sq_le s M H a (fun i ↦ (i.2 : ℝ) / i.1)
    (one_div_pos.2 (pow_pos hQ' 2)) hsep
  rwa [hs, sum_sigma, div_div_eq_mul_div, div_one] at key

/-- **The additive large sieve over reduced residues.** The inequality of
`sum_Icc_sum_filter_coprime_norm_sum_fourierChar_sq_le` with the moduli written `q + 1` for
`q < Q` and the reduced fractions indexed by the units `u` of `ZMod (q + 1)`, at the points
`u.val / (q + 1)`. -/
theorem sum_range_sum_units_norm_sum_fourierChar_sq_le (M : ℤ) (H Q : ℕ) (a : Fin H → ℂ) :
    ∑ q ∈ range Q, ∑ u : (ZMod (q + 1))ˣ,
        ‖∑ j : Fin H, a j * (Real.fourierChar
          (((M : ℝ) + (j : ℕ)) * (((u : ZMod (q + 1)).val : ℝ) / (q + 1 : ℕ))) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 * (Q : ℝ) ^ 2) * ∑ j : Fin H, ‖a j‖ ^ 2 := by
  refine le_of_eq_of_le ?_ (sum_Icc_sum_filter_coprime_norm_sum_fourierChar_sq_le M H Q a)
  refine sum_nbij' (· + 1) (· - 1) (fun q hq ↦ ?_) (fun q hq ↦ ?_) (fun q _ ↦ rfl)
    (fun q hq ↦ ?_) fun q _ ↦ ?_
  · exact mem_Icc.2 ⟨by omega, by have := mem_range.1 hq; omega⟩
  · exact mem_range.2 (by have := mem_Icc.1 hq; omega)
  · have := mem_Icc.1 hq
    omega
  · exact ZMod.sum_units_val_eq_sum_filter_coprime (q + 1) fun b ↦
      ‖∑ j : Fin H, a j * (Real.fourierChar
        (((M : ℝ) + (j : ℕ)) * ((b : ℝ) / (q + 1 : ℕ))) : ℂ)‖ ^ 2

end TauCeti
