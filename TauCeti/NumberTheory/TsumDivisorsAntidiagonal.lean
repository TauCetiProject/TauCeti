/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import TauCeti.Topology.Algebra.InfiniteSum.Sigma
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
* `TauCeti.summable_mul_pow_mul`: for bounded `f` and `‖r‖ < 1`, the double series
  `∑_{c, m ≥ 1} f(c, m) r^{c m}` is summable.
* `TauCeti.hasSum_sum_divisors_mul_pow`: for bounded `g` and `‖r‖ < 1`, the Lambert-type series
  `∑_{c, m ≥ 1} g(m) r^{c m}` is the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ`.
-/

public section

variable {α : Type*} [AddCommMonoid α] [TopologicalSpace α]

/-- **Regrouping a double series by the product of the indices.** If the family
`(c, m) ↦ f c m` over pairs of positive integers sums to `a`, then so does the series over
`n ≥ 1` of the finite sums `∑_{c m = n} f c m`. -/
theorem HasSum.sum_divisorsAntidiagonal {f : ℕ → ℕ → α} {a : α}
    (hf : HasSum (fun p : ℕ+ × ℕ+ ↦ f p.1 p.2) a) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2) a := by
  convert (sigmaAntidiagonalEquivProd.hasSum_iff.mpr hf).sigma_of_finite using 2 with n
  rw [Finset.univ_eq_attach]
  simpa [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors] using
    (Finset.sum_attach _ fun x : ℕ × ℕ ↦ f x.1 x.2).symm

namespace TauCeti

/-- A family `f` over pairs of positive integers bounded by `C`, times `r^(c m)` with `‖r‖ < 1`
in a complete seminormed ring, is summable. -/
theorem summable_mul_pow_mul {K : Type*} [SeminormedRing K] [CompleteSpace K] {r : K}
    (hr : ‖r‖ < 1) {C : ℝ} {f : ℕ+ × ℕ+ → K} (hf : ∀ p, ‖f p‖ ≤ C) :
    Summable fun p : ℕ+ × ℕ+ ↦ f p * r ^ ((p.1 : ℕ) * p.2) :=
  -- dominate termwise by `C ‖r‖^(c m)`, summable by Mathlib's `summable_prod_mul_pow` with `k = 0`
  .of_norm_bounded (g := fun p : ℕ+ × ℕ+ ↦ C * ‖r‖ ^ ((p.1 : ℕ) * p.2))
    (by simpa using (summable_prod_mul_pow 0 (r := ‖r‖) (by simpa using hr)).mul_left C)
    fun p ↦ norm_mul_le_of_le (hf p) (norm_pow_le' _ (mul_pos p.1.property p.2.property))

/-- **Lambert-type series as power series.** For a bounded sequence `g` and `‖r‖ < 1` in a
complete normed ring, the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ` sums to the double series
`∑_{c ≥ 1} ∑_{m ≥ 1} g(m) r^{c m}`. For instance `g(m) = m sᵐ` gives
`∑_{c ≥ 1} r^c s / (1 - r^c s)²` when `‖s‖ ≤ 1` in a non-archimedean field. -/
theorem hasSum_sum_divisors_mul_pow {K : Type*} [NormedRing K] [CompleteSpace K] {g : ℕ → K}
    {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) {r : K} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ m ∈ n.divisors, g m) * r ^ n)
      (∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1))) := by
  have hs : Summable (fun p : ℕ+ × ℕ+ ↦ g p.2 * r ^ ((p.1 : ℕ) * p.2)) :=
    summable_mul_pow_mul hr fun p ↦ hg p.2
  have hv : ∑' p : ℕ+ × ℕ+, g p.2 * r ^ ((p.1 : ℕ) * p.2) =
      ∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1)) := by
    rw [hs.tsum_prod, tsum_pnat_eq_tsum_succ (f := fun c ↦ ∑' m : ℕ+, g m * r ^ (c * m))]
    exact tsum_congr fun c ↦ tsum_pnat_eq_tsum_succ (f := fun m ↦ g m * r ^ ((c + 1) * m))
  -- group the double series by `n = c m`: every term of the `n`-th group carries `rⁿ`
  have h : HasSum (fun n : ℕ+ ↦ (∑ m ∈ (n : ℕ).divisors, g m) * r ^ (n : ℕ))
      (∑' p : ℕ+ × ℕ+, g p.2 * r ^ ((p.1 : ℕ) * p.2)) := by
    convert hs.hasSum.sum_divisorsAntidiagonal (f := fun c m ↦ g m * r ^ (c * m)) using 2 with n
    rw [← Nat.sum_divisorsAntidiagonal' fun _ m ↦ g m, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x hx ↦ by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  -- the term `n = 0` vanishes, so the series over `ℕ` is the series over `ℕ+`
  simpa [hv] using (hasSum_pnat_iff (f := fun n ↦ (∑ m ∈ n.divisors, g m) * r ^ n)).mp h

end TauCeti
