/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.AbelSummation
public import TauCeti.NumberTheory.LSeries.WienerIkehara.SharpCutoff

/-!
# Variants of the Wiener--Ikehara theorem

`TauCeti.LSeries.wienerIkehara` treats nonnegative coefficients whose Dirichlet series has a
simple pole at `s = 1`, and reads the partial sums at a real cutoff. This file derives three
variants that arise when the theorem is applied.

* **Finitely many negative coefficients.** Only eventual nonnegativity of the coefficients is
  needed: changing finitely many coefficients subtracts a finite Dirichlet polynomial from both the
  series and its boundary remainder, which keeps the remainder continuous, and changes the partial
  sums by a bounded amount, which is invisible after division by `x`.
* **Natural cutoffs.** The same limit along the natural numbers `N → ∞`.
* **A pole at a positive abscissa.** If the series converges on `Re s > σ` for some `σ > 0` and
  `F s - κ / (s - σ)` extends continuously to `Re s ≥ σ`, then `x ^ (-σ) ∑_{1 ≤ n ≤ x} a n → κ / σ`.
  The coefficients `a n n ^ (1 - σ)` have the series `F (s + σ - 1)`, which has its pole at `1`, so
  the theorem at `1` shows that their partial sums grow like `κ x`; Abel summation against
  `t ^ (σ - 1)`, in the form `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`, then recovers the
  partial sums of `a` itself.

As in `TauCeti.LSeries.wienerIkehara`, the series hypothesis is `LSeriesHasSum` on the open
half-plane and the continuous boundary remainder is a separately named function `G`.

## Main results

* `TauCeti.LSeries.wienerIkehara_of_eventually_nonneg`: the theorem for eventually nonnegative
  coefficients.
* `TauCeti.LSeries.wienerIkehara_nat`: the same conclusion along natural cutoffs.
* `TauCeti.LSeries.wienerIkehara_rpow`: the theorem for a pole at `σ > 0`,
  `x ^ (-σ) ∑_{1 ≤ n ≤ x} a n → κ / σ`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.7.
-/

public section

open Complex Filter Set
open scoped Topology

namespace TauCeti.LSeries

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}

/-- **The Wiener--Ikehara theorem for eventually nonnegative coefficients.** Let `a n ≥ 0` for all
large `n`, let the Dirichlet series of `a` have sum `F s` on `Re s > 1`, and let `G` be continuous
on `Re s ≥ 1` with `G s = F s - κ / (s - 1)` on `Re s > 1`. Then
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`. -/
theorem wienerIkehara_of_eventually_nonneg (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 κ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  -- Discard the coefficients below `N`, and the Dirichlet polynomial `P` they contribute.
  set b : ℕ → ℝ := fun n ↦ if n < N then 0 else a n with hb
  set P : ℂ → ℂ := fun s ↦ ∑ n ∈ Finset.range N, _root_.LSeries.term (fun n ↦ (a n : ℂ)) s n
  have hb0 : 0 ≤ b := fun n ↦ by
    by_cases hn : n < N
    · simp [hb, hn]
    · simpa [hb, hn] using hN n (not_lt.mp hn)
  have hbF (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (fun n ↦ (b n : ℂ)) s (F s - P s) := by
    have hP : HasSum (fun n ↦ if n < N then _root_.LSeries.term (fun n ↦ (a n : ℂ)) s n else 0)
        (P s) := by
      have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
        (s := Finset.range N)
        (f := fun n ↦ if n < N then _root_.LSeries.term (fun n ↦ (a n : ℂ)) s n else 0)
        fun n hn ↦ by simp_all
      have hsum : ∑ n ∈ Finset.range N,
          (if n < N then _root_.LSeries.term (fun n ↦ (a n : ℂ)) s n else 0) = P s :=
        Finset.sum_congr rfl fun n hn ↦ by simp [Finset.mem_range.mp hn]
      rwa [hsum] at h
    refine ((hF s hs).sub hP).congr_fun fun n ↦ ?_
    by_cases hn : n < N
    · simp [hb, hn, _root_.LSeries.term_def]
    · simp [hb, hn, _root_.LSeries.term_def]
  -- `P` is a finite Dirichlet polynomial, hence continuous.
  have hP : Continuous P := by
    refine continuous_finsetSum _ fun n _ ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simpa only [_root_.LSeries.term_zero] using continuous_const
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp only [_root_.LSeries.term_of_ne_zero hn]
      exact continuous_const.div (continuous_id.const_cpow (Or.inl hn'))
        fun s ↦ cpow_ne_zero_iff.mpr (Or.inl hn')
  have hmain := LSeries.wienerIkehara (a := b) (F := fun s ↦ F s - P s) (G := fun s ↦ G s - P s)
    hb0 hbF (hG.sub hP.continuousOn) fun s hs ↦ by rw [hGF s hs]; ring
  -- The discarded coefficients change the partial sums by a constant `c`.
  set c : ℝ := ∑ n ∈ Finset.Icc 1 N, (if n < N then a n else 0)
  have hc : Tendsto (fun x : ℝ ↦ x⁻¹ * c) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const c
  refine (by simpa using hmain.add hc : Tendsto _ atTop (𝓝 κ)).congr' ?_
  filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
  have hNx : N ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if n < N then a n else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hn : n < N <;> simp [hb, hn]
  have hc' : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if n < N then a n else 0) = c := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hNx) fun n hn hn' ↦ ?_).symm
    have : ¬ n < N := fun h ↦ hn' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h.le⟩)
    simp [this]
  rw [hsplit, hc', mul_add]

/-- **The Wiener--Ikehara theorem at natural cutoffs.** Under the hypotheses of
`TauCeti.LSeries.wienerIkehara_of_eventually_nonneg`, `N⁻¹ ∑_{1 ≤ n ≤ N} a n → κ` as `N → ∞`
through the natural numbers. -/
theorem wienerIkehara_nat (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, a n) atTop (𝓝 κ) := by
  refine ((wienerIkehara_of_eventually_nonneg ha hF hG hGF).comp
    tendsto_natCast_atTop_atTop).congr fun N ↦ ?_
  simp

/-- **The Wiener--Ikehara theorem for a pole at a positive abscissa.** Let `σ > 0`, let `a n ≥ 0`
for all large `n`, let the Dirichlet series of `a` have sum `F s` on `Re s > σ`, and let `G` be
continuous on `Re s ≥ σ` with `G s = F s - κ / (s - σ)` on `Re s > σ`. Then
`x ^ (-σ) ∑_{1 ≤ n ≤ x} a n → κ / σ` as `x → ∞`.

For `σ = 1` this is `TauCeti.LSeries.wienerIkehara_of_eventually_nonneg`. -/
theorem wienerIkehara_rpow {σ : ℝ} (hσ : 0 < σ) (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hF : ∀ s : ℂ, σ < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | σ ≤ s.re})
    (hGF : ∀ s : ℂ, σ < s.re → G s = F s - κ / (s - σ)) :
    Tendsto (fun x : ℝ ↦ (x ^ σ)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 (κ / σ)) := by
  -- The coefficients `a n n ^ (1 - σ)` have the series `F (s + (σ - 1))`, with its pole at `1`.
  set b : ℕ → ℝ := fun n ↦ a n * (n : ℝ) ^ (1 - σ) with hb
  have hshift (s : ℂ) : (s + ((σ - 1 : ℝ) : ℂ)).re = s.re + (σ - 1) := by simp
  have hbF (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (b n : ℂ)) s (F (s + ((σ - 1 : ℝ) : ℂ))) := by
    refine (hF _ (by rw [hshift]; linarith)).congr_fun fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [_root_.LSeries.term_of_ne_zero hn, _root_.LSeries.term_of_ne_zero hn, hb,
      ofReal_mul, ofReal_cpow (Nat.cast_nonneg n), cpow_add _ _ hn', ofReal_natCast]
    have h1 : (n : ℂ) ^ ((1 - σ : ℝ) : ℂ) * (n : ℂ) ^ ((σ - 1 : ℝ) : ℂ) = 1 := by
      rw [← cpow_add _ _ hn']
      simp
    have h2 : (n : ℂ) ^ ((σ - 1 : ℝ) : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have h3 : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    field_simp
    linear_combination (a n : ℂ) * h1
  have hbG : ContinuousOn (fun s ↦ G (s + ((σ - 1 : ℝ) : ℂ))) {s : ℂ | 1 ≤ s.re} :=
    hG.comp (continuous_id.add continuous_const).continuousOn fun s hs ↦ by
      simp only [mem_ofPred_eq] at hs ⊢
      rw [hshift]
      linarith
  have hbGF (s : ℂ) (hs : 1 < s.re) :
      G (s + ((σ - 1 : ℝ) : ℂ)) = F (s + ((σ - 1 : ℝ) : ℂ)) - κ / (s - 1) := by
    rw [hGF _ (by rw [hshift]; linarith)]
    congr 2
    push_cast
    ring
  have hb0 : ∀ᶠ n in atTop, 0 ≤ b n := ha.mono fun n hn ↦
    mul_nonneg hn (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- Their partial sums grow like `κ x`; summing against `n ^ (σ - 1)` recovers those of `a`.
  have hmain := tendsto_rpow_inv_mul_sum_Icc_rpow_mul (by linarith : -1 < σ - 1)
    (wienerIkehara_of_eventually_nonneg hb0 hbF hbG hbGF)
  rw [sub_add_cancel] at hmain
  refine hmain.congr fun x ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [hb, mul_left_comm, ← Real.rpow_add hn0]
  simp

end TauCeti.LSeries
