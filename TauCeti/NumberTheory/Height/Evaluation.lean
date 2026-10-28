/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.Global.Places.Height
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Heights of values of integer polynomials

Let `P ∈ ℤ[X_i : i ∈ ι]` have partial degrees `degreeOf i P ≤ L i` and length
`ℓ(P) = ∑_s |c_s|`, the sum of the absolute values of its coefficients. For a point `x` of a
field `K`, the value `P(x) = ∑_s c_s ∏ i, x_i ^ s_i` is bounded place by place:

* at an arbitrary absolute value `v`, `v(P(x)) ≤ ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`;
* at a nonarchimedean `v`, the integer coefficients have `v(c_s) ≤ 1` and the ultrametric
  inequality removes the factor `ℓ(P)`: `v(P(x)) ≤ ∏ i, max(v(x_i), 1) ^ L i`.

Multiplying these local bounds over the admissible absolute values of `K` gives the height of the
value: `h(P(x)) ≤ totalWeight K * log ℓ(P) + ∑ i, L i * h(x_i)`.

Over a number field `totalWeight K = [K : ℚ]`. Combined with the product formula, in the form
`ord_v(y) log N(v) ≤ h(y)` at a finite place `v`, this bounds the order at `v` of a nonzero value
`P(x)`: `ord_v P(x) log N(v) ≤ [K : ℚ] log ℓ(P) + ∑ i, L i * h(x_i)`. This Liouville-type
estimate is the polynomial evaluation bound of Yu's theory of linear forms in `p`-adic logarithms:
the auxiliary polynomial values there are nonzero algebraic numbers whose order at the prime is
compared with an analytic upper bound.

## Main results

* `AbsoluteValue.apply_prod_pow_le`: `v(∏ i, x_i ^ s_i) ≤ ∏ i, max(v(x_i), 1) ^ L i` for `s ≤ L`.
* `AbsoluteValue.apply_aeval_le`: `v(P(x)) ≤ ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`.
* `IsNonarchimedean.apply_aeval_le`: `v(P(x)) ≤ ∏ i, max(v(x_i), 1) ^ L i` for nonarchimedean `v`.
* `Height.mulHeight₁_aeval_le`: `H(P(x)) ≤ ℓ(P) ^ totalWeight K * ∏ i, H(x_i) ^ L i` for `P ≠ 0`.
* `Height.logHeight₁_aeval_le`: `h(P(x)) ≤ totalWeight K * log ℓ(P) + ∑ i, L i * h(x_i)`.
* `IsDedekindDomain.HeightOneSpectrum.neg_log_valuation_aeval_mul_log_absNorm_le`: the order bound
  `ord_v P(x) log N(v) ≤ [K : ℚ] log ℓ(P) + ∑ i, L i * h(x_i)` over a number field `K`.

## References

* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. **74** (1990), 15–113, §1,
  Lemma 1.3.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.5 and §1.6.
-/

public section

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι]

namespace AbsoluteValue

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- A monomial `∏ i, x_i ^ s_i` with exponents `s_i ≤ L i` has absolute value at most
`∏ i, max(v(x_i), 1) ^ L i`. -/
theorem apply_prod_pow_le (v : AbsoluteValue R ℝ) {s L : ι → ℕ} (hs : ∀ i, s i ≤ L i)
    (x : ι → R) : v (∏ i, x i ^ s i) ≤ ∏ i, max (v (x i)) 1 ^ L i := by
  rw [map_prod]
  refine prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  rw [v.map_pow]
  exact (pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _).trans
    (pow_le_pow_right₀ (le_max_right _ _) (hs i))

/-- The value of an integer polynomial `P` with partial degrees `degreeOf i P ≤ L i` at a point
`x` has absolute value at most `ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`, where `ℓ(P)` is the sum of the
absolute values of the coefficients of `P`. -/
theorem apply_aeval_le (v : AbsoluteValue R ℝ) {P : MvPolynomial ι ℤ} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → R) :
    v (aeval x P) ≤ (∑ s ∈ P.support, |(P.coeff s : ℝ)|) * ∏ i, max (v (x i)) 1 ^ L i := by
  rw [aeval_def, eval₂_eq', sum_mul]
  refine (v.sum_le _ _).trans <| sum_le_sum fun s hs ↦ ?_
  have hc : v (P.coeff s : R) ≤ |(P.coeff s : ℝ)| := by
    rw [← v.apply_natAbs_eq]
    exact (v.apply_nat_le_self _).trans_eq (by rw [Nat.cast_natAbs, Int.cast_abs])
  rw [v.map_mul, algebraMap_int_eq, eq_intCast]
  exact mul_le_mul hc (v.apply_prod_pow_le
    (fun i ↦ (monomial_le_degreeOf i hs).trans (hL i)) x) (v.nonneg _) (abs_nonneg _)

end AbsoluteValue

namespace IsNonarchimedean

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- At a nonarchimedean absolute value the value of an integer polynomial `P` with partial
degrees `degreeOf i P ≤ L i` at a point `x` has absolute value at most
`∏ i, max(v(x_i), 1) ^ L i`: the integer coefficients have absolute value at most `1`. -/
theorem apply_aeval_le {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v)
    {P : MvPolynomial ι ℤ} {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → R) :
    v (aeval x P) ≤ ∏ i, max (v (x i)) 1 ^ L i := by
  rcases P.support.eq_empty_or_nonempty with hP | hP
  · rw [support_eq_empty.mp hP, map_zero, v.map_zero]
    positivity
  rw [aeval_def, eval₂_eq']
  refine (hv.apply_sum_le_sup hP).trans <| sup'_le _ _ fun s hs ↦ ?_
  rw [v.map_mul, algebraMap_int_eq, eq_intCast]
  exact (mul_le_mul (hv.apply_intCast_le_one (by simp) v.map_one v.map_neg)
    (v.apply_prod_pow_le (fun i ↦ (monomial_le_degreeOf i hs).trans (hL i)) x) (v.nonneg _)
    zero_le_one).trans_eq (one_mul _)

end IsNonarchimedean

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues Real

/-- Only finitely many nonarchimedean admissible absolute values of `x` exceed `1`. -/
-- Mathlib's `Height.hasFiniteMulSupport_max_nonarchAbsVal` states this but is private.
@[fun_prop]
private theorem hasFiniteMulSupport_max_one (x : K) :
    (fun v : nonarchAbsVal ↦ max (v.val x) 1).HasFiniteMulSupport := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Function.HasFiniteMulSupport]
  exact (hasFiniteMulSupport hx).max (by simp [Function.HasFiniteMulSupport])

/-- The multiplicative height of the value at `x` of a nonzero integer polynomial `P` with partial
degrees `degreeOf i P ≤ L i` is at most `ℓ(P) ^ totalWeight K * ∏ i, H(x_i) ^ L i`, where `ℓ(P)`
is the sum of the absolute values of the coefficients of `P`. -/
theorem mulHeight₁_aeval_le {P : MvPolynomial ι ℤ} (hP : P ≠ 0) {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → K) :
    mulHeight₁ (aeval x P) ≤
      (∑ s ∈ P.support, |(P.coeff s : ℝ)|) ^ totalWeight K * ∏ i, mulHeight₁ (x i) ^ L i := by
  set A := ∑ s ∈ P.support, |(P.coeff s : ℝ)|
  -- `ℓ(P) ≥ 1`, since `P` has a nonzero integer coefficient.
  have hA : 1 ≤ A := by
    obtain ⟨s, hs⟩ := support_nonempty.mpr hP
    refine le_trans ?_ (single_le_sum (fun s _ ↦ abs_nonneg _) hs)
    exact_mod_cast Int.one_le_abs (mem_support_iff.mp hs)
  set g : AbsoluteValue K ℝ → ℝ := fun v ↦ ∏ i, max (v (x i)) 1 ^ L i
  have hg (v : AbsoluteValue K ℝ) : 1 ≤ g v :=
    one_le_prod₀ fun i _ ↦ one_le_pow₀ (le_max_right _ _)
  -- The archimedean factor: `∏_v max(v(P(x)), 1) ≤ ℓ(P) ^ totalWeight K * ∏_v g v`.
  have harch : (archAbsVal.map fun v ↦ max (v (aeval x P)) 1).prod ≤
      A ^ totalWeight K * ∏ i, (archAbsVal.map fun v ↦ max (v (x i)) 1).prod ^ L i := by
    calc (archAbsVal.map fun v ↦ max (v (aeval x P)) 1).prod
        ≤ (archAbsVal.map fun v ↦ A * g v).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun v _ ↦
            max_le (v.apply_aeval_le hL x) (one_le_mul_of_one_le_of_one_le hA (hg v))
      _ = _ := by
          rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
            Multiset.prod_map_prod]
          simp only [Multiset.prod_map_pow, totalWeight]
  -- The nonarchimedean factor: `∏ᶠ_v max(v(P(x)), 1) ≤ ∏ᶠ_v g v`.
  have hnonarch : (∏ᶠ v : nonarchAbsVal, max (v.val (aeval x P)) 1) ≤
      ∏ i, (∏ᶠ v : nonarchAbsVal, max (v.val (x i)) 1) ^ L i := by
    rw [prod_congr rfl fun i _ ↦ finprod_pow
      (f := fun v : nonarchAbsVal ↦ max (v.val (x i)) 1) (by fun_prop) (L i),
      ← finprod_prod_comm _ _ fun i _ ↦ by fun_prop]
    exact finprod_le_finprod₀ (by fun_prop) (fun _ ↦ by positivity) (by fun_prop) fun v ↦
      max_le ((isNonarchimedean v.val v.prop).apply_aeval_le hL x) (hg v.val)
  rw [mulHeight₁_eq]
  simp_rw [mulHeight₁_eq, mul_pow, prod_mul_distrib, ← mul_assoc]
  gcongr
  · exact finprod_nonneg fun _ ↦ by positivity
  · refine mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) <|
      prod_nonneg fun i _ ↦ pow_nonneg (Multiset.prod_nonneg fun a ha ↦ ?_) _
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    positivity

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
  have hA : 0 < ∑ s ∈ P.support, |(P.coeff s : ℝ)| := by
    obtain ⟨s, hs⟩ := support_nonempty.mpr hP
    exact sum_pos' (fun s _ ↦ abs_nonneg _) ⟨s, hs, by simpa using mem_support_iff.mp hs⟩
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
  exact (v.neg_log_valuation_mul_log_absNorm_le_logHeight₁ _).trans
    (Height.logHeight₁_aeval_le hL x)

end IsDedekindDomain.HeightOneSpectrum
