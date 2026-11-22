/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.WienerIkehara.Chebyshev
import Mathlib.NumberTheory.LSeries.WienerIkehara
import TauCeti.Analysis.Asymptotics.Sum.Window

/-!
# The Wiener--Ikehara theorem

Let `a n ≥ 0` have Dirichlet series `F s = ∑ a n n⁻ˢ` convergent on `Re s > 1`, and suppose that
`F s - κ / (s - 1)` agrees on `Re s > 1` with a function `G` continuous on `Re s ≥ 1`. The
Wiener--Ikehara theorem says that the partial sums then grow like `κ x`:
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`.

The Chebyshev bound `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary` supplies the linear
growth bound required by Mathlib's `WienerIkehara.tendsto_sum_div`, which gives the sharp-cutoff
limit after absorbing and subtracting the `n = 0` term. (For the complex-valued smoothed asymptotic
on `(0, ∞)`, see `TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop` in
`TauCeti.NumberTheory.LSeries.WienerIkehara.Approximation`.)

For the sharp-cutoff theorems in this file, the coefficients are real and nonnegative, the
hypothesis on the series is `LSeriesHasSum` on the open half-plane (Mathlib's `LSeries` is a total
function, zero where the series diverges), and the continuous extension is a separately named
function `G`, so no junk value of `F` at `s = 1` or on the line `Re s = 1` is ever used. The sign
of `κ` is not assumed: it is forced by the conclusion.

## Main results

* `TauCeti.LSeries.wienerIkehara`: **the Wiener--Ikehara theorem**,
  `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ`.
* `TauCeti.LSeries.wienerIkehara_zero`: the case `κ = 0`, in which `F` itself extends continuously
  to `Re s ≥ 1` and the partial sums are `o(x)`.

## Provenance

`TauCeti.LSeries.wienerIkehara` delegates the sharp-cutoff Tauberian step to Mathlib's
`WienerIkehara.tendsto_sum_div` via the Chebyshev bound
`TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.LSeries

section Sharp

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}

/-- **The Wiener--Ikehara theorem.** Let `a n ≥ 0` have Dirichlet series with sum `F s` on
`Re s > 1`, and let `G` be continuous on `Re s ≥ 1` with `G s = F s - κ / (s - 1)` on `Re s > 1`.
Then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`. -/
theorem wienerIkehara (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 κ) := by
  -- The Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N`.
  obtain ⟨C₀, hC₀⟩ := exists_sum_Icc_le_mul_of_isBigO
    (isBigO_sum_Icc_norm_id_of_boundary (a := fun n ↦ (a n : ℂ)) (A := κ)
      (fun n ↦ by simpa using ha n) hG (fun z hz ↦ by rw [hGF z hz, (hF z hz).LSeries_eq])
      (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable))
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ C * N := fun N ↦ by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_)) ((hC₀ N).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) N.cast_nonneg))
    simp [abs_of_nonneg (ha n)]
  have hsplit (n : ℕ) : ∑ i ∈ Finset.Icc 0 n, a i = a 0 + ∑ i ∈ Finset.Icc 1 n, a i := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc n.zero_le, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  have hbound : ∀ N : ℕ, ∑ i ∈ Finset.range N, a i ≤ (C + a 0) * N := fun N ↦ by
    rcases N with _ | m
    · simp
    rw [Nat.range_succ_eq_Icc_zero, hsplit]
    have hm := hC m
    have ha0 : 0 ≤ a 0 := ha 0
    push_cast
    nlinarith
  have hmain := WienerIkehara.tendsto_sum_div (A := κ) hbound hG
    (fun s hs ↦ by dsimp only; rw [hGF s hs, (hF s hs).LSeries_eq]) ha
  have ha0 : Tendsto (fun x : ℝ ↦ a 0 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine (by simpa using hmain.sub ha0 : Tendsto _ atTop (𝓝 κ)).congr fun x ↦ ?_
  rw [hsplit, add_div, add_sub_cancel_left, div_eq_inv_mul]

/-- **The Wiener--Ikehara theorem with zero residue.** If the Dirichlet series `F` of `a n ≥ 0`
extends continuously from `Re s > 1` to `Re s ≥ 1`, then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → 0`. -/
theorem wienerIkehara_zero (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re}) (hGF : ∀ s : ℂ, 1 < s.re → G s = F s) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) :=
  wienerIkehara ha hF hG fun s hs ↦ by simp [hGF s hs]

end Sharp

end TauCeti.LSeries
