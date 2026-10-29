/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.RCLike.Basic

/-!
# Regrouping a double series by the product of the indices

A sum over pairs of positive integers `(c, m)` can be regrouped according to the product
`n = c m`: the `n`-th group is the finite sum over `Nat.divisorsAntidiagonal n`. This is how a
double series `∑_{c, m ≥ 1} a(c) b(m) q^{c m}`, such as the `q`-expansion of an Eisenstein
series, becomes a power series `∑_n (∑_{c m = n} a(c) b(m)) q^n`.

Mathlib's `tsum_prod_pow_eq_tsum_sigma` proves one instance of this regrouping, for the terms
`m^k r^{c m}`; this file states the regrouping for an arbitrary summable family, through the
same equivalence `sigmaAntidiagonalEquivProd`.

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
* `TauCeti.hasSum_sum_divisors_mul_pow`: for bounded `g` and `‖r‖ < 1`, the Lambert-type series
  `∑_{c, m ≥ 1} g(m) r^{c m}` is the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ`.
-/

public section

variable {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α] [RegularSpace α]

/-- **Regrouping a double series by the product of the indices.** If the family
`(c, m) ↦ f c m` over pairs of positive integers sums to `a`, then so does the series over
`n ≥ 1` of the finite sums `∑_{c m = n} f c m`. -/
theorem HasSum.sum_divisorsAntidiagonal {f : ℕ → ℕ → α} {a : α}
    (hf : HasSum (fun p : ℕ+ × ℕ+ ↦ f p.1 p.2) a) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2) a := by
  refine (sigmaAntidiagonalEquivProd.hasSum_iff.mpr hf).sigma fun n ↦ ?_
  have h := hasSum_fintype fun x : (n : ℕ).divisorsAntidiagonal ↦ f x.1.1 x.1.2
  rw [Finset.univ_eq_attach, Finset.sum_attach _ fun x : ℕ × ℕ ↦ f x.1 x.2] at h
  simpa [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors] using h

namespace TauCeti

/-- **Lambert-type series as power series.** For a bounded sequence `g` and `‖r‖ < 1` in a
complete normed ring, the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ` sums to the double series
`∑_{c ≥ 1} ∑_{m ≥ 1} g(m) r^{c m}`. For instance `g(m) = m sᵐ` gives
`∑_{c ≥ 1} r^c s / (1 - r^c s)²` when `‖s‖ ≤ 1` in a non-archimedean field. -/
theorem hasSum_sum_divisors_mul_pow {K : Type*} [NormedRing K] [CompleteSpace K] {g : ℕ → K}
    {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) {r : K} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ m ∈ n.divisors, g m) * r ^ n)
      (∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1))) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  have hs : Summable (fun p : ℕ+ × ℕ+ ↦ g p.2 * r ^ ((p.1 : ℕ) * p.2)) := by
    refine Summable.of_norm_bounded (g := fun p : ℕ+ × ℕ+ ↦ C * ‖r‖ ^ ((p.1 : ℕ) * p.2)) ?_ ?_
    · simpa using (summable_prod_mul_pow 0 (r := ‖r‖) (by simpa using hr)).mul_left C
    · intro p
      calc ‖g p.2 * r ^ ((p.1 : ℕ) * p.2)‖ ≤ ‖g p.2‖ * ‖r ^ ((p.1 : ℕ) * p.2)‖ := norm_mul_le _ _
        _ ≤ C * ‖r‖ ^ ((p.1 : ℕ) * p.2) :=
          mul_le_mul (hg _) (norm_pow_le' _ (mul_pos p.1.2 p.2.2)) (norm_nonneg _) hC
  have hv : ∑' p : ℕ+ × ℕ+, g p.2 * r ^ ((p.1 : ℕ) * p.2) =
      ∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1)) := by
    rw [hs.tsum_prod, tsum_pnat_eq_tsum_succ (f := fun c ↦ ∑' m : ℕ+, g m * r ^ (c * m))]
    exact tsum_congr fun c ↦ tsum_pnat_eq_tsum_succ (f := fun m ↦ g m * r ^ ((c + 1) * m))
  have h := hs.hasSum.sum_divisorsAntidiagonal (f := fun c m ↦ g m * r ^ (c * m))
  rw [hv] at h
  -- the term `n = 0` vanishes, so the series over `ℕ` is the series over `ℕ+`
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.divisors_zero, Finset.sum_empty,
    zero_mul, sub_zero]
  rw [← hasSum_pnat_iff_hasSum_succ (f := fun n ↦ (∑ m ∈ n.divisors, g m) * r ^ n)]
  convert h using 2 with n
  rw [Nat.sum_divisorsAntidiagonal' (f := fun c m ↦ g m * r ^ (c * m)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]

end TauCeti
