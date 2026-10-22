/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Antitone
public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic

/-!
# Exact coefficients of the principal-minor series from a dominant minor

The row bounds `‖A i j‖ ≤ r i` only bound the coefficients of the principal-minor series
`det (1 - T A) = ∑ cₙ Tⁿ` from above, by `‖cₙ‖ ≤ sup_{#s = n} ∏ i ∈ s, r i`
(`Matrix.norm_charCoeff_le`). This file gives a criterion under which that bound is attained and
the norm of each coefficient is known exactly.

Let `A : Matrix ℕ ℕ K` over a complete ultrametric normed field, and let `d : ℕ → K` have
strictly decreasing norms tending to zero, with `‖A i j‖ ≤ ‖d i‖`. Write `B` for the normalised
matrix with entries `(d i)⁻¹ * A i j`. If the leading principal minor of `B` on
`range n = {0, …, n - 1}` has norm one, then

`‖cₙ‖ = ∏ i ∈ range n, ‖d i‖` (`Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`).

The leading principal minor of `A` on `range n` has exactly this norm
(`Matrix.norm_principalMinor_eq_prod`), while every other principal minor of size `n` is
bounded by `(∏ i ∈ range (n - 1), ‖d i‖) * ‖d n‖`, which is strictly smaller because the norms
decrease strictly. By the ultrametric inequality the leading minor dominates the convergent sum
defining `cₙ`.

Over a dense value group strict decrease does not force the norms to tend to zero, and the decay
hypothesis is needed for the minors to be summable at all. For a row-compact operator on
`C₀(ℕ, K)` the decay follows from the normalisation of the leading minors; see
`TauCeti.Analysis.Normed.Operator.Nonarchimedean.DominantMinor`.

In valuation terms, with `‖x‖ = b ^ (-v x)`, the conclusion reads `v (cₙ) = ∑ i < n, v (d i)`,
so the exact coefficient valuations are read off from the increasing sequence `v (d i)`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Filter Finset Topology

namespace Matrix

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Matrix ℕ ℕ K} {d : ℕ → K}

/-- Every principal minor of size `n + 1` other than the leading one on `range (n + 1)` has norm
at most `(∏ i ∈ range n, ‖d i‖) * ‖d (n + 1)‖`, when `‖A i j‖ ≤ ‖d i‖` and the norms of `d`
decrease. -/
private theorem norm_principalMinor_le_prod_range_mul (hdec : Antitone fun i ↦ ‖d i‖)
    (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖) {s : Finset ℕ} {n : ℕ} (hs : #s = n + 1)
    (hne : s ≠ range (n + 1)) :
    ‖A.principalMinor s‖ ≤ (∏ i ∈ range n, ‖d i‖) * ‖d (n + 1)‖ :=
  (norm_principalMinor_le hA s).trans <| prod_le_prod_range_mul_of_not_subset
    (fun _ ↦ norm_nonneg _) hdec hs fun hsub ↦
      hne (eq_of_subset_of_card_le hsub (by rw [hs, card_range]))

/-- **Exact coefficients from a dominant minor.** Let `‖A i j‖ ≤ ‖d i‖`, where the norms of `d`
decrease strictly and tend to zero. If the normalised matrix with entries `(d i)⁻¹ * A i j` has
a principal minor of norm one on `range n`, then the `n`-th coefficient of the principal-minor
series `det (1 - T A)` has norm exactly `∏ i ∈ range n, ‖d i‖`. -/
theorem norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one [CompleteSpace K]
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0))
    (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖) {n : ℕ}
    (hminor : ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor (range n)‖ = 1) :
    ‖A.charCoeff n‖ = ∏ i ∈ range n, ‖d i‖ := by
  -- Strictly decreasing nonnegative norms are positive.
  have hpos (i : ℕ) : 0 < ‖d i‖ := (norm_nonneg _).trans_lt (hdec i.lt_succ_self)
  rcases n with _ | n
  · simp
  let f : {s : Finset ℕ // #s = n + 1} → K := fun s ↦ A.principalMinor s
  let s₀ : {s : Finset ℕ // #s = n + 1} := ⟨range (n + 1), card_range _⟩
  have hsum : Summable f :=
    summable_principalMinor hA (by rwa [Nat.cofinite_eq_atTop]) (n + 1)
  have hdom : ‖f s₀‖ = ∏ i ∈ range (n + 1), ‖d i‖ :=
    norm_principalMinor_eq_prod (fun i _ ↦ norm_pos_iff.1 (hpos i)) hminor
  -- The remaining minors are bounded by a constant strictly below the leading one.
  set C := (∏ i ∈ range n, ‖d i‖) * ‖d (n + 1)‖
  have hC₀ : 0 ≤ C := mul_nonneg (prod_nonneg fun i _ ↦ norm_nonneg _) (norm_nonneg _)
  have hrest : ‖∑' s, if s = s₀ then 0 else f s‖ ≤ C := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC₀ fun s ↦ ?_
    split_ifs with h
    · simpa using hC₀
    · exact norm_principalMinor_le_prod_range_mul hdec.antitone hA s.2
        fun h' ↦ h (Subtype.ext h')
  have hlt : C < ∏ i ∈ range (n + 1), ‖d i‖ := by
    rw [prod_range_succ]
    exact mul_lt_mul_of_pos_left (hdec n.lt_succ_self) (prod_pos fun i _ ↦ hpos i)
  rw [charCoeff_def, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    hsum.tsum_eq_add_tsum_ite s₀, ← hdom]
  rw [← hdom] at hlt
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hrest.trans_lt hlt).ne',
    max_eq_left (hrest.trans hlt.le)]

end Matrix
