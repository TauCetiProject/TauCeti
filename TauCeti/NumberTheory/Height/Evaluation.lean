/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.Height.LinearForm
public import TauCeti.NumberTheory.NumberField.Global.Places.Height
public import TauCeti.RingTheory.MvPolynomial.Abv.Eval

/-!
# Heights of values of integer polynomials

Let `P ∈ ℤ[X_i : i ∈ ι]` have partial degrees `degreeOf i P ≤ L i` and length
`ℓ(P) = ∑_s |c_s|`, the sum of the absolute values of its coefficients. For a point `x` of a
field `K`, the value `P(x) = ∑_s c_s ∏ i, x_i ^ s_i` is bounded place by place
(`AbsoluteValue.apply_aeval_le`, `IsNonarchimedean.apply_aeval_le`):

* at an arbitrary absolute value `v`, `v(P(x)) ≤ ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`;
* at a nonarchimedean `v`, the integer coefficients have `v(c_s) ≤ 1` and the ultrametric
  inequality removes the factor `ℓ(P)`: `v(P(x)) ≤ ∏ i, max(v(x_i), 1) ^ L i`.

Multiplying these local bounds over the admissible absolute values of `K` gives the height of the
value: `h(P(x)) ≤ totalWeight K * log ℓ(P) + ∑ i, L i * h(x_i)`.

Over a number field `totalWeight K = [K : ℚ]`. Combined with the product formula, in the form
`|ord_v(y)| log N(v) ≤ h(y)` at a finite place `v`, this bounds the order at `v` of a nonzero value
`P(x)`: `ord_v P(x) log N(v) ≤ [K : ℚ] log ℓ(P) + ∑ i, L i * h(x_i)`. This Liouville-type
estimate is the polynomial evaluation bound of Yu's theory of linear forms in `p`-adic logarithms:
the auxiliary polynomial values there are nonzero algebraic numbers whose order at the prime is
compared with an analytic upper bound.

## Main results

* `Height.mulHeight₁_aeval_le`: `H(P(x)) ≤ ℓ(P) ^ totalWeight K * ∏ i, H(x_i) ^ L i` for `P ≠ 0`.
* `Height.logHeight₁_aeval_le`: `h(P(x)) ≤ totalWeight K * log ℓ(P) + ∑ i, L i * h(x_i)`.
* `IsDedekindDomain.HeightOneSpectrum.neg_log_valuation_aeval_mul_log_absNorm_le`: the order bound
  `ord_v P(x) log N(v) ≤ [K : ℚ] log ℓ(P) + ∑ i, L i * h(x_i)` over a number field `K`.

## Implementation notes

The local bounds are aggregated over the places of `K` by the local-to-global bound
`Height.mulHeight₁_le_pow_mul_prod_mulHeightAff`, applied to the family consisting of `L i` copies
of the one-element tuple `![x i]` for each `i`.

## References

* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. **74** (1990), 15–113, §1,
  Lemma 1.3.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.5 and §1.6.
-/

public section

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι]

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues Real

/-- The multiplicative height of the value at `x` of a nonzero integer polynomial `P` with partial
degrees `degreeOf i P ≤ L i` is at most `ℓ(P) ^ totalWeight K * ∏ i, H(x_i) ^ L i`, where `ℓ(P)`
is the sum of the absolute values of the coefficients of `P`. -/
theorem mulHeight₁_aeval_le {P : MvPolynomial ι ℤ} (hP : P ≠ 0) {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → K) :
    mulHeight₁ (aeval x P) ≤
      (∑ s ∈ P.support, |(P.coeff s : ℝ)|) ^ totalWeight K * ∏ i, mulHeight₁ (x i) ^ L i := by
  -- Each `x i` enters as `L i` copies of the one-element tuple `![x i]`.
  have hloc (v : AbsoluteValue K ℝ) : ∏ p : (Σ i, Fin (L i)), max (⨆ j, v (![x p.1] j)) 1 =
      ∏ i, max (v (x i)) 1 ^ L i := by
    simp [Fintype.prod_sigma]
  have key := mulHeight₁_le_pow_mul_prod_mulHeightAff (one_le_sum_abs_coeff hP) (aeval x P)
    (fun p : Σ i, Fin (L i) ↦ ![x p.1])
    (fun v _ ↦ by rw [hloc]; exact v.apply_aeval_le hL x)
    fun v hv ↦ by rw [hloc]; exact (isNonarchimedean v hv).apply_aeval_le hL x
  simpa [Fintype.prod_sigma, mulHeightAff_fin_one] using key

/-- The logarithmic height of the value at `x` of an integer polynomial `P` with partial degrees
`degreeOf i P ≤ L i` is at most `totalWeight K * log ℓ(P) + ∑ i, L i * h(x_i)`, where `ℓ(P)` is
the sum of the absolute values of the coefficients of `P`. For `P = 0` the left side is `0` and
the right side is nonnegative, since `log 0 = 0`. -/
theorem logHeight₁_aeval_le {P : MvPolynomial ι ℤ} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → K) :
    logHeight₁ (aeval x P) ≤
      totalWeight K * log (∑ s ∈ P.support, |(P.coeff s : ℝ)|) +
        ∑ i, L i * logHeight₁ (x i) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simpa using sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (zero_le_logHeight₁ (x i))
  have hA : 0 < ∑ s ∈ P.support, |(P.coeff s : ℝ)| :=
    zero_lt_one.trans_le (one_le_sum_abs_coeff hP)
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_pow, ← sum_congr rfl fun i _ ↦ log_pow (mulHeight₁ (x i)) (L i),
    ← log_prod fun i _ ↦ by positivity, ← log_mul (by positivity) (by positivity)]
  exact log_le_log (mulHeight₁_pos _) (mulHeight₁_aeval_le hP hL x)

end Height

namespace IsDedekindDomain.HeightOneSpectrum

open NumberField Real

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality for values of integer polynomials at a finite place.** Let `P` be an
integer polynomial with partial degrees `degreeOf i P ≤ L i` and let `x` be a point of a number
field `K`. The order of `P(x)` at a finite place `v`, weighted by `log N(v)`, is at most
`[K : ℚ] log ℓ(P) + ∑ i, L i * h(x_i)`, where `ℓ(P)` is the sum of the absolute values of the
coefficients of `P` and `h` is the logarithmic height `logHeight₁`, relative to `K`.

The bound is meaningful for `P(x) ≠ 0`; for `P(x) = 0` the left side is `0`. Writing
`N(v) = p ^ f` and `h(x_i) = [K : ℚ] h_abs(x_i)` with the absolute height, this is
`ord_v P(x) ≤ [K : ℚ] / (f log p) * (log ℓ(P) + ∑ i, L i * h_abs(x_i))`. -/
theorem neg_log_valuation_aeval_mul_log_absNorm_le (v : HeightOneSpectrum (𝓞 K))
    {P : MvPolynomial ι ℤ} {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → K) :
    -WithZero.log (v.valuation K (aeval x P)) * log (Ideal.absNorm v.asIdeal) ≤
      Module.finrank ℚ K * log (∑ s ∈ P.support, |(P.coeff s : ℝ)|) +
        ∑ i, L i * Height.logHeight₁ (x i) := by
  rw [← totalWeight_eq_finrank]
  have hneg : -((WithZero.log (v.valuation K (aeval x P)) : ℤ) : ℝ) ≤
      |WithZero.log (v.valuation K (aeval x P))| := by
    exact_mod_cast neg_le_abs _
  exact (mul_le_mul_of_nonneg_right hneg (log_natCast_nonneg _)).trans <|
    (v.abs_log_valuation_mul_log_absNorm_le_logHeight₁ _).trans (Height.logHeight₁_aeval_le hL x)

end IsDedekindDomain.HeightOneSpectrum
