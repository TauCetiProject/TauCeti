/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Complex
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.Analysis.SpecificLimits.GeomSumProduct
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# Ramanujan's four-shift identity

For `α, β ∈ ℂ` and `Re s > max(1, 1 + Re α, 1 + Re β, 1 + Re(α + β))`, the Dirichlet series of
`σ_α(n) σ_β(n)` converges absolutely and

`∑ σ_α(n) σ_β(n) n^(-s) = ζ(s) ζ(s - α) ζ(s - β) ζ(s - α - β) / ζ(2s - α - β)`.

Absolute convergence follows from `‖σ_ν(n)‖ ≤ τ(n) n ^ max(Re ν, 0)` and the divisor bound
`τ(n) = O(n ^ ε)`. Both sides are Euler products. With `X = p^(-s)`, `a = p^α` and `b = p^β`, the
local factor of the left side at `p` is `∑_k S_a(k) S_b(k) Xᵏ`, where `S_a(k) = ∑_{i ≤ k} aⁱ`, and
`TauCeti.hasSum_geom_sum_mul_geom_sum_mul_geometric` evaluates it as
`(1 - a b X²) / ((1 - X) (1 - a X) (1 - b X) (1 - a b X))`; here `a X = p^(-(s - α))`,
`b X = p^(-(s - β))`, `a b X = p^(-(s - α - β))` and `a b X² = p^(-(2s - α - β))`.

At `α = β = 0` this is `∑ τ(n)² n^(-s) = ζ(s)⁴ / ζ(2s)`,
`TauCeti.LSeriesHasSum_card_divisors_sq`.

## Main results

* `TauCeti.LSeries.LSeries_sigmaC_mul_sigmaC`: Ramanujan's identity, with absolute convergence.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, (1.28).
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Chapter I.
* Alex Kontorovich, Terence Tao and contributors, [Prime Number Theorem and More][PNTRamanujan],
  `IwaniecKowalskiCh1.lean`, `zeta_mul_zeta_mul_zeta_mul_zeta_eq`.

[PNTRamanujan]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/301f8be/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

open ArithmeticFunction TauCeti.ArithmeticFunction

namespace TauCeti.LSeries

/-- The series of `σ_α(n) σ_β(n)` converges absolutely on the half-plane of Ramanujan's identity:
there `Re s > 1 + ρ` with `ρ = max(Re α, 0) + max(Re β, 0)`, and the coefficients are
`O(n ^ (ρ + 2ε))` for every `ε > 0`. -/
private theorem LSeriesSummable_sigmaC_mul_sigmaC {α β s : ℂ} (hs : 1 < s.re)
    (hα : 1 + α.re < s.re) (hβ : 1 + β.re < s.re) (hαβ : 1 + (α + β).re < s.re) :
    LSeriesSummable (fun n ↦ sigmaC α n * sigmaC β n) s := by
  set ρ := max α.re 0 + max β.re 0
  have hρ : 1 + ρ < s.re := by
    rw [Complex.add_re] at hαβ
    rcases le_total α.re 0 with ha | ha <;> rcases le_total β.re 0 with hb | hb <;>
      simp only [ρ, max_eq_left, max_eq_right, ha, hb] <;> linarith
  set ε := (s.re - 1 - ρ) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_pos_card_divisors_le_rpow hε
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1 + ρ + 2 * ε) (by simp only [ε]; linarith)
    ⟨C ^ 2, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hτ (ν : ℂ) : ‖sigmaC ν n‖ ≤ C * (n : ℝ) ^ ε * (n : ℝ) ^ max ν.re 0 :=
    (norm_sigmaC_le ν n).trans (by gcongr; exact hC n)
  rw [norm_mul]
  refine (mul_le_mul (hτ α) (hτ β) (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [show 1 + ρ + 2 * ε - 1 = ε + max α.re 0 + (ε + max β.re 0) by ring,
    Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_add hn0]
  ring

/-- The local factor of Ramanujan's identity at a prime `p`. -/
private theorem tsum_term_sigmaC_mul_sigmaC_prime_pow {α β s : ℂ} (hs : 0 < s.re)
    (hα : 0 < (s - α).re) (hβ : 0 < (s - β).re) (hαβ : 0 < (s - α - β).re) (p : Nat.Primes) :
    ∑' k : ℕ, _root_.LSeries.term (fun n ↦ sigmaC α n * sigmaC β n) s (p.val ^ k) =
      (1 - (p : ℂ) ^ (-(2 * s - α - β))) / ((1 - (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-(s - α))) *
        (1 - (p : ℂ) ^ (-(s - β))) * (1 - (p : ℂ) ^ (-(s - α - β)))) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hcpow (u v w : ℂ) (h : u + v = w) : (p : ℂ) ^ u * (p : ℂ) ^ v = (p : ℂ) ^ w := by
    rw [← Complex.cpow_add _ _ hp0, h]
  have hnorm {w : ℂ} (hw : 0 < w.re) : ‖(p : ℂ) ^ (-w)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hw)
  have ha := hcpow α (-s) (-(s - α)) (by ring)
  have hb := hcpow β (-s) (-(s - β)) (by ring)
  have hab : (p : ℂ) ^ α * (p : ℂ) ^ β * (p : ℂ) ^ (-s) = (p : ℂ) ^ (-(s - α - β)) := by
    rw [mul_assoc, hb, hcpow]
    ring
  have habx : (p : ℂ) ^ α * (p : ℂ) ^ β * ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (-(2 * s - α - β)) := by
    rw [sq, ← mul_assoc, hab, hcpow]
    ring
  have h := hasSum_geom_sum_mul_geom_sum_mul_geometric (hnorm hs) (ha ▸ hnorm hα)
    (hb ▸ hnorm hβ) (hab ▸ hnorm hαβ)
  rw [ha, hb, hab, habx] at h
  refine Eq.trans (tsum_congr fun k ↦ ?_) h.tsum_eq
  rw [term_pow _ p.prop.ne_zero, sigmaC_apply_prime_pow _ p.prop, sigmaC_apply_prime_pow _ p.prop]

/-- **Ramanujan's four-shift identity.** For `α, β ∈ ℂ` and
`Re s > max(1, 1 + Re α, 1 + Re β, 1 + Re(α + β))`, the series `∑ σ_α(n) σ_β(n) n^(-s)` converges
absolutely and equals `ζ(s) ζ(s - α) ζ(s - β) ζ(s - α - β) / ζ(2s - α - β)`. -/
theorem LSeries_sigmaC_mul_sigmaC {α β s : ℂ} (hs : 1 < s.re) (hα : 1 + α.re < s.re)
    (hβ : 1 + β.re < s.re) (hαβ : 1 + (α + β).re < s.re) :
    LSeriesSummable (fun n ↦ sigmaC α n * sigmaC β n) s ∧
      LSeries (fun n ↦ sigmaC α n * sigmaC β n) s =
        riemannZeta s * riemannZeta (s - α) * riemannZeta (s - β) * riemannZeta (s - α - β) /
          riemannZeta (2 * s - α - β) := by
  have hsum := LSeriesSummable_sigmaC_mul_sigmaC hs hα hβ hαβ
  refine ⟨hsum, ?_⟩
  simp only [Complex.add_re] at hαβ
  have h1 : 1 < (s - α).re := by rw [Complex.sub_re]; linarith
  have h2 : 1 < (s - β).re := by rw [Complex.sub_re]; linarith
  have h3 : 1 < (s - α - β).re := by simp only [Complex.sub_re]; linarith
  have h4 : 1 < (2 * s - α - β).re := by 
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
    linarith
  have hmul {m n : ℕ} (_ : m ≠ 0) (_ : n ≠ 0) (hmn : m.Coprime n) :
      sigmaC α (m * n) * sigmaC β (m * n) =
        sigmaC α m * sigmaC β m * (sigmaC α n * sigmaC β n) := by
    rw [(isMultiplicative_sigmaC α).map_mul_of_coprime hmn,
      (isMultiplicative_sigmaC β).map_mul_of_coprime hmn]
    ring
  have hL := EulerProduct.eulerProduct_hasProd (by simp) (term_mul_of_coprime hmul) hsum.norm
    (_root_.LSeries.term_zero _ s)
  have hζ := (((riemannZeta_eulerProduct_hasProd hs).mul (riemannZeta_eulerProduct_hasProd h1)).mul
    (riemannZeta_eulerProduct_hasProd h2)).mul (riemannZeta_eulerProduct_hasProd h3)
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h4), mul_comm]
  refine ((riemannZeta_eulerProduct_hasProd h4).mul hL).unique (hζ.congr_fun fun p ↦ ?_)
  rw [tsum_term_sigmaC_mul_sigmaC_prime_pow (by linarith) (by linarith) (by linarith)
      (by linarith),
    ← mul_div_assoc, inv_mul_cancel₀ (Complex.one_sub_prime_cpow_ne_zero p.prop h4)]
  simp only [one_div, mul_inv]

end TauCeti.LSeries
