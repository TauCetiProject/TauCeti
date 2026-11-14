/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.NumberTheory.NewtonPolygon.Irreducible
public import TauCeti.NumberTheory.Padics.LogGauge
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Finite
import TauCeti.RingTheory.Valuation.LinearIndependent
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# A ramified quadratic base extension: `X ^ 2 + 2 X + 2` over `ℚ_[2]` and `ℚ_[2](i)`

The polynomial `ξ₂ = X ^ 2 + 2 X + 2` is Eisenstein at `2`. Over `ℚ_[2]`, with the valuation
`TauCeti.padicRealValuation 2` normalised by `v(2) = 1`, its Newton polygon is the segment from
`(0, 1)` to `(2, 0)`, with the slope `-1 / 2` of multiplicity two, and it is irreducible.

Over any ring containing a square root `i` of `-1` it factors as

```text
ξ₂ = (X - (i - 1)) * (X - (-i - 1)),
```

since `(X + 1) ^ 2 - i ^ 2 = X ^ 2 + 2 X + 2`. Both factors are monic of degree one. In a normed
extension `K` of `ℚ_[2]` the element `i` has norm one, so the factorisation takes place in the
valuation ring of `K`, where `ξ₂` is therefore reducible. The roots `i - 1` and `-i - 1` have
norm `2 ^ (-1 / 2)`, because `(i - 1) ^ 2 = -2 i`.

The Newton polygon depends on the chosen normalisation of the valuation of `K`.

* In the base-`2` normalisation, `‖x‖ = 2 ^ (-w x)`, which restricts to the valuation of
  `ℚ_[2]`, the coefficients still have values `1, 1, 0`, so `ξ₂` has the slope `-1 / 2` of
  multiplicity two, and the roots have value `1 / 2`.
* In the normalisation at `i - 1`, `‖x‖ = √2 ^ (-w x)`, the element `i - 1` has value one and
  `w 2 = 2`, so the slope is `-1` with multiplicity two.

In a quadratic extension `K` of `ℚ_[2]`, such as `ℚ_[2](i)`, every nonzero element has squared
norm in `2 ^ ℤ`: for an element `x` of squared norm outside `2 ^ ℤ`, the norms of `1`, `x` and
`x ^ 2` would lie in three distinct classes of `ℝ>0 / 2 ^ ℤ`, and these three elements would be
linearly independent over `ℚ_[2]`. Hence the normalisation at `i - 1` is integer valued: it is the
integral normalisation of `K`, and `i - 1` is a uniformiser of the valuation ring of `K`. The
slope `-1` in that normalisation is integral, so the irreducibility criterion for pure polynomials
of slope `a / d` with `gcd(a, d) = 1` does not apply over `K`; it must be read in the base
normalisation of `ℚ_[2]`, where the slope `-1 / 2` has denominator two.

## Main results

* `isEisensteinAt_X_sq_add_two_mul_X_add_two`: `ξ₂` is Eisenstein at the maximal ideal of `ℤ_[2]`.
* `newtonSlopes_X_sq_add_two_mul_X_add_two` and `irreducible_X_sq_add_two_mul_X_add_two`: over
  `ℚ_[2]`, `ξ₂` is pure of slope `-1 / 2` and irreducible.
* `X_sq_add_two_mul_X_add_two_eq_mul`, `not_irreducible_X_sq_add_two_mul_X_add_two` and
  `not_irreducible_X_sq_add_two_mul_X_add_two_integer`: the factorisation over a ring containing
  `i`, and reducibility there, in particular in the valuation ring of a normed extension of
  `ℚ_[2]` containing `i`.
* `newtonSlopes_X_sq_add_two_mul_X_add_two_of_norm_eq_two_rpow`,
  `map_sub_one_of_norm_eq_two_rpow`: in the base-`2` normalisation the slope is `-1 / 2` and the
  root `i - 1` has value `1 / 2`.
* `newtonSlopes_X_sq_add_two_mul_X_add_two_of_norm_eq_sqrt_two_rpow`,
  `map_sub_one_of_norm_eq_sqrt_two_rpow`, `map_two_of_norm_eq_sqrt_two_rpow`: in the
  normalisation at `i - 1` the slope is `-1`, with `w (i - 1) = 1` and `w 2 = 2`.
* `exists_norm_sq_eq_zpow`: in a quadratic extension of `ℚ_[p]`, squared norms lie in `p ^ ℤ`.
* `irreducible_sub_one` and `exists_int_of_norm_eq_sqrt_two_rpow`: in `ℚ_[2](i)`, `i - 1` is a
  uniformiser of the valuation ring and the normalisation at `i - 1` is integer valued.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §§6–7,
  for Newton polygons, Eisenstein polynomials and ramification in local fields.
-/

public section

open Polynomial TauCeti

namespace TauCeti.NewtonPolygonRamifiedQuadraticExample

/-! ### The base field `ℚ_[2]` -/

section Base

variable {R : Type*} [CommRing R]

/-- The constant coefficient of `X ^ 2 + 2 X + 2` is `2`. -/
private theorem coeff_zero_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : R[X]).coeff 0 = 2 := by
  simp

/-- The linear coefficient of `X ^ 2 + 2 X + 2` is `2`. -/
private theorem coeff_one_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : R[X]).coeff 1 = 2 := by
  simp

/-- `X ^ 2 + 2 X + 2` has degree two over any nontrivial commutative ring. -/
private theorem natDegree_X_sq_add_two_mul_X_add_two [Nontrivial R] :
    (X ^ 2 + 2 * X + 2 : R[X]).natDegree = 2 := by
  compute_degree!

/-- `X ^ 2 + 2 X + 2` is monic over any commutative ring. -/
private theorem monic_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : R[X]).Monic := by
  monicity!

/-- **`X ^ 2 + 2 X + 2` is Eisenstein at `2`.** Its leading coefficient is a unit of `ℤ_[2]`, its
other coefficients lie in the maximal ideal `(2)`, and its constant coefficient `2` does not lie
in the square `(4)` of that ideal. -/
theorem isEisensteinAt_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : ℤ_[2][X]).IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[2]) := by
  have h2 : (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (by simp)
  refine ⟨?_, fun {n} hn => ?_, ?_⟩
  · rw [monic_X_sq_add_two_mul_X_add_two.leadingCoeff]
    exact Ideal.ne_top_iff_one _ |>.mp (IsLocalRing.maximalIdeal.isMaximal ℤ_[2]).ne_top
  · rw [natDegree_X_sq_add_two_mul_X_add_two] at hn
    interval_cases n
    · rwa [coeff_zero_X_sq_add_two_mul_X_add_two]
    · rwa [coeff_one_X_sq_add_two_mul_X_add_two]
  · rw [coeff_zero_X_sq_add_two_mul_X_add_two, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h2' : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by simpa using PadicInt.norm_p (p := 2)
    have hnorm := congrArg norm hc
    rw [norm_mul, norm_pow, Nat.cast_ofNat, h2'] at hnorm
    nlinarith [c.norm_le_one]

/-- **`X ^ 2 + 2 X + 2` is pure of slope `-1 / 2` over `ℚ_[2]`.** With `v(2) = 1`, its Newton
polygon is the Eisenstein segment from `(0, 1)` to `(2, 0)`. -/
theorem newtonSlopes_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : ℚ_[2][X]).newtonSlopes (padicRealValuation 2) =
      Multiset.replicate 2 (-2⁻¹) := by
  have hv2 : padicRealValuation 2 (2 : ℚ_[2]) = 1 := by
    simpa using padicRealValuation_p (p := 2)
  rw [newtonSlopes_eq_replicate_of_eisenstein, natDegree_X_sq_add_two_mul_X_add_two]
  · norm_num
  · rw [monic_X_sq_add_two_mul_X_add_two.leadingCoeff, AddValuation.map_one]
  · rw [coeff_zero_X_sq_add_two_mul_X_add_two, hv2]
  · intro n hn hn2
    rw [natDegree_X_sq_add_two_mul_X_add_two] at hn2
    obtain rfl : n = 1 := by omega
    rw [coeff_one_X_sq_add_two_mul_X_add_two, hv2]

/-- **`X ^ 2 + 2 X + 2` is irreducible over `ℚ_[2]`**, by the Newton polygon irreducibility
criterion for the slope `-1 / 2`, whose denominator is the degree. -/
theorem irreducible_X_sq_add_two_mul_X_add_two :
    Irreducible (X ^ 2 + 2 * X + 2 : ℚ_[2][X]) := by
  refine irreducible_of_forall_mem_newtonSlopes_eq_div
    (fun _ hx => exists_int_padicRealValuation hx) (by simp) (by
      rw [natDegree_X_sq_add_two_mul_X_add_two]; norm_num) (a := -1) (by
      rw [natDegree_X_sq_add_two_mul_X_add_two]; decide) fun m hm => ?_
  rw [newtonSlopes_X_sq_add_two_mul_X_add_two, Multiset.mem_replicate] at hm
  rw [hm.2, natDegree_X_sq_add_two_mul_X_add_two]
  norm_num

end Base

/-! ### The factorisation over a ring containing `i` -/

section Factorisation

variable {R : Type*} [Ring R] {i : R}

/-- **`X ^ 2 + 2 X + 2` splits over a ring containing a square root `i` of `-1`**, with roots
`i - 1` and `-i - 1`. -/
theorem X_sq_add_two_mul_X_add_two_eq_mul (hi : i ^ 2 = -1) :
    (X ^ 2 + 2 * X + 2 : R[X]) = (X - C (i - 1)) * (X - C (-i - 1)) := by
  have hCi : C i * C i = -1 := by rw [← C_mul, ← sq, hi, C_neg, C_1]
  simp only [map_sub, map_neg, map_one, sub_mul, mul_sub, mul_neg, one_mul, mul_one, X_mul_C, hCi]
  noncomm_ring
  simp

/-- Over a ring containing a square root of `-1`, `X ^ 2 + 2 X + 2` is the product of two monic
linear polynomials, so it is not irreducible. -/
theorem not_irreducible_X_sq_add_two_mul_X_add_two (hi : i ^ 2 = -1) :
    ¬Irreducible (X ^ 2 + 2 * X + 2 : R[X]) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact fun h => h.not_isUnit (isUnit_of_subsingleton _)
  rw [X_sq_add_two_mul_X_add_two_eq_mul hi]
  exact fun h => (h.isUnit_or_isUnit rfl).elim (not_isUnit_X_sub_C _) (not_isUnit_X_sub_C _)

end Factorisation

/-! ### Normed extensions of `ℚ_[2]` containing `i` -/

section Extension

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[2] K] {i : K}

/-- If `i ^ 2 = -1`, then `‖i - 1‖ = 1 / √2`, because `(i - 1) ^ 2 = -2 i`. -/
theorem norm_sub_one_eq_inv_sqrt_two (hi : i ^ 2 = -1) : ‖i - 1‖ = (√2)⁻¹ := by
  have hsq : (i - 1) ^ 2 = -(2 * i) := by linear_combination hi
  -- `i` has finite order, so norm one
  have hi1 : ‖i‖ = 1 := (isOfFinOrder_iff_pow_eq_one.2
      ⟨4, four_pos, by rw [show 4 = 2 * 2 from rfl, pow_mul, hi, neg_one_sq]⟩).norm_eq_one
  have h2 : ‖(2 : K)‖ = 2⁻¹ := by
    rw [← map_ofNat (algebraMap ℚ_[2] K) 2, norm_algebraMap']
    simpa using Padic.norm_p (p := 2)
  have h : ‖i - 1‖ ^ 2 = 2⁻¹ := by
    rw [← norm_pow, hsq, norm_neg, norm_mul, h2, hi1, mul_one]
  rw [← Real.sqrt_inv, ← h, Real.sqrt_sq (norm_nonneg _)]

omit [NormedAlgebra ℚ_[2] K] in
/-- In the valuation ring of a nonarchimedean normed field containing a square root `i` of `-1`,
for instance a normed extension of `ℚ_[2]` containing `i`, the polynomial `X ^ 2 + 2 X + 2` is
reducible: `i` has norm one, so `X ^ 2 + 2 X + 2 = (X - (i - 1)) * (X - (-i - 1))` there. -/
theorem not_irreducible_X_sq_add_two_mul_X_add_two_integer [IsUltrametricDist K]
    (hi : i ^ 2 = -1) :
    ¬Irreducible (X ^ 2 + 2 * X + 2 : (NormedField.valuation (K := K)).integer[X]) := by
  -- `i` has finite order, so norm one
  have hi1 : ‖i‖ = 1 := (isOfFinOrder_iff_pow_eq_one.2
      ⟨4, four_pos, by rw [show 4 = 2 * 2 from rfl, pow_mul, hi, neg_one_sq]⟩).norm_eq_one
  have hmem : i ∈ (NormedField.valuation (K := K)).integer := by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnNorm,
      hi1]
  exact not_irreducible_X_sq_add_two_mul_X_add_two (i := ⟨i, hmem⟩) (Subtype.ext hi)

/-- **Base-`2` normalisation.** For an additive valuation `w` on `K` with `‖x‖ = 2 ^ (-w x)`, the
image in `K` of `x : ℚ_[2]` has the value of `x` for `padicRealValuation 2`. -/
theorem map_algebraMap_of_norm_eq_two_rpow {w : AddValuation K (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = (2 : ℝ) ^ (-(w x).untop₀)) (x : ℚ_[2]) :
    w (algebraMap ℚ_[2] K x) = padicRealValuation 2 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← WithTop.coe_untop₀_of_ne_top ((padicRealValuation 2).ne_top_iff.mpr hx), ← neg_neg
    (padicRealValuation 2 x).untop₀, ← w.norm_eq_rpow_iff one_lt_two hw, norm_algebraMap',
    norm_eq_rpow_neg_padicRealValuation hx, Nat.cast_ofNat]

/-- Mapping `X ^ 2 + 2 X + 2` from `ℚ_[2]` to `K` gives `X ^ 2 + 2 X + 2`. -/
private theorem map_X_sq_add_two_mul_X_add_two :
    (X ^ 2 + 2 * X + 2 : ℚ_[2][X]).map (algebraMap ℚ_[2] K) = X ^ 2 + 2 * X + 2 := by
  simp

/-- **Base-`2` normalisation.** For an additive valuation `w` on `K` with `‖x‖ = 2 ^ (-w x)`,
which restricts to `padicRealValuation 2`, the polynomial `X ^ 2 + 2 X + 2` is pure of slope
`-1 / 2` over `K`. -/
theorem newtonSlopes_X_sq_add_two_mul_X_add_two_of_norm_eq_two_rpow
    {w : AddValuation K (WithTop ℝ)} (hw : ∀ x ≠ 0, ‖x‖ = (2 : ℝ) ^ (-(w x).untop₀)) :
    (X ^ 2 + 2 * X + 2 : K[X]).newtonSlopes w = Multiset.replicate 2 (-2⁻¹) := by
  rw [← map_X_sq_add_two_mul_X_add_two, newtonSlopes_map _ _ _
    (map_algebraMap_of_norm_eq_two_rpow hw), newtonSlopes_X_sq_add_two_mul_X_add_two]

/-- **Base-`2` normalisation.** If `i ^ 2 = -1`, the root `i - 1` of `X ^ 2 + 2 X + 2` has
value `1 / 2` for an additive valuation `w` on `K` with `‖x‖ = 2 ^ (-w x)`. -/
theorem map_sub_one_of_norm_eq_two_rpow {w : AddValuation K (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = (2 : ℝ) ^ (-(w x).untop₀)) (hi : i ^ 2 = -1) :
    w (i - 1) = (2⁻¹ : ℝ) := by
  rw [← neg_neg (2⁻¹ : ℝ), ← w.norm_eq_rpow_iff one_lt_two hw, norm_sub_one_eq_inv_sqrt_two hi,
    Real.rpow_neg zero_le_two, Real.sqrt_eq_rpow, one_div]

/-- **Normalisation at `i - 1`.** If `i ^ 2 = -1` and the additive valuation `w` on `K` satisfies
`‖x‖ = √2 ^ (-w x)`, then `w (i - 1) = 1`. -/
theorem map_sub_one_of_norm_eq_sqrt_two_rpow {w : AddValuation K (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = √2 ^ (-(w x).untop₀)) (hi : i ^ 2 = -1) : w (i - 1) = 1 := by
  have h := (w.norm_eq_rpow_iff Real.one_lt_sqrt_two hw (σ := -1)).mp (by
    rw [norm_sub_one_eq_inv_sqrt_two hi, Real.rpow_neg_one])
  simpa using h

/-- **Normalisation at `i - 1`.** For an additive valuation `w` on `K` with `‖x‖ = √2 ^ (-w x)`,
the image in `K` of `x : ℚ_[2]` has twice the value of `x` for `padicRealValuation 2`. -/
theorem map_algebraMap_of_norm_eq_sqrt_two_rpow {w : AddValuation K (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = √2 ^ (-(w x).untop₀)) (x : ℚ_[2]) :
    w (algebraMap ℚ_[2] K x) = (padicRealValuation 2 x).map (2 * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← WithTop.coe_untop₀_of_ne_top ((padicRealValuation 2).ne_top_iff.mpr hx), WithTop.map_coe,
    ← neg_neg (2 * (padicRealValuation 2 x).untop₀), ← w.norm_eq_rpow_iff Real.one_lt_sqrt_two hw,
    norm_algebraMap', norm_eq_rpow_neg_padicRealValuation hx, Nat.cast_ofNat, ← mul_neg,
    Real.rpow_mul (Real.sqrt_nonneg 2), Real.rpow_two, Real.sq_sqrt zero_le_two]

/-- **Normalisation at `i - 1`.** For an additive valuation `w` on `K` with `‖x‖ = √2 ^ (-w x)`,
the element `2` has value `2`. -/
theorem map_two_of_norm_eq_sqrt_two_rpow {w : AddValuation K (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = √2 ^ (-(w x).untop₀)) : w 2 = 2 := by
  have hv2 : padicRealValuation 2 (2 : ℚ_[2]) = 1 := by
    simpa using padicRealValuation_p (p := 2)
  rw [← map_ofNat (algebraMap ℚ_[2] K) 2, map_algebraMap_of_norm_eq_sqrt_two_rpow hw, hv2]
  norm_num

/-- **Normalisation at `i - 1`.** For an additive valuation `w` on `K` with `‖x‖ = √2 ^ (-w x)`,
the polynomial `X ^ 2 + 2 X + 2` is pure of the integral slope `-1`. -/
theorem newtonSlopes_X_sq_add_two_mul_X_add_two_of_norm_eq_sqrt_two_rpow
    {w : AddValuation K (WithTop ℝ)} (hw : ∀ x ≠ 0, ‖x‖ = √2 ^ (-(w x).untop₀)) :
    (X ^ 2 + 2 * X + 2 : K[X]).newtonSlopes w = Multiset.replicate 2 (-1) := by
  rw [← map_X_sq_add_two_mul_X_add_two, newtonSlopes_map_eq_map_mul _ _ _ two_pos
    (map_algebraMap_of_norm_eq_sqrt_two_rpow hw), newtonSlopes_X_sq_add_two_mul_X_add_two,
    Multiset.map_replicate]
  norm_num

end Extension

/-! ### The ramified quadratic extension `ℚ_[2](i)` -/

section QuadraticExtension

/-- **Squared norms in a quadratic extension of `ℚ_[p]`.** If `K` has degree two over `ℚ_[p]`,
every nonzero element of `K` has squared norm an integer power of `p`. Otherwise `1`, `x` and
`x ^ 2` would have norms in three distinct classes modulo the norms `p ^ ℤ` of `ℚ_[p]`, and so
would be linearly independent over `ℚ_[p]`. -/
theorem exists_norm_sq_eq_zpow {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (hK : Module.finrank ℚ_[p] K = 2) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ‖x‖ ^ 2 = (p : ℝ) ^ m := by
  by_contra H
  simp only [not_exists] at H
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : Module.Finite ℚ_[p] K := Module.finite_of_finrank_eq_succ hK
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- neither `‖x‖` nor `‖x‖ ^ 2` lies in `p ^ ℤ`
  have H' {d : ℕ} (hd0 : 0 < d) (hd2 : d ≤ 2) (m : ℤ) : ‖x‖ ^ d ≠ (p : ℝ) ^ m := by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    · refine fun h => H (2 * m) ?_
      rw [pow_one] at h
      rw [h, ← zpow_natCast, ← zpow_mul, mul_comm, Nat.cast_ofNat]
    · exact H m
  -- so nonzero multiples of `x ^ j` and `x ^ k`, for `j < k ≤ 2`, have different norms
  have key {j k : ℕ} (hjk : j < k) (hk : k ≤ 2) {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) :
      ‖a‖ * ‖x‖ ^ j ≠ ‖b‖ * ‖x‖ ^ k := by
    intro h
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ‖a‖ = (p : ℝ) ^ m := ⟨_, Padic.norm_eq_zpow_neg_valuation ha⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖b‖ = (p : ℝ) ^ n := ⟨_, Padic.norm_eq_zpow_neg_valuation hb⟩
    refine H' (d := k - j) (by omega) (by omega) (m - n) ?_
    rw [zpow_sub₀ (by positivity), ← hm, ← hn, eq_div_iff (norm_ne_zero_iff.mpr hb)]
    refine mul_right_cancel₀ (pow_ne_zero j hx0.ne') ?_
    rw [h, ← Nat.sub_add_cancel hjk.le, pow_add, Nat.add_sub_cancel]
    ring
  let f : Fin 3 → K := fun j => x ^ (j : ℕ)
  have hli : LinearIndependent ℚ_[p] f := by
    refine (NormedField.valuation (K := K)).linearIndependent_of_map_smul_ne
      (fun j a ha => Valuation.ne_zero_iff _ |>.mpr (smul_ne_zero ha (pow_ne_zero _ hx)))
      fun j k hjk a b ha hb h => ?_
    have h' : ‖a‖ * ‖x‖ ^ (j : ℕ) = ‖b‖ * ‖x‖ ^ (k : ℕ) := by
      simpa [f, NormedField.valuation_apply, norm_smul] using congrArg NNReal.toReal h
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with hlt | hlt
    · exact key hlt (by omega) ha hb h'
    · exact key hlt (by omega) hb ha h'.symm
  simpa [hK] using hli.fintype_card_le_finrank

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[2] K] {i : K}

/-- If `i ^ 2 = -1`, then `i - 1` lies in the valuation ring of `K`. -/
theorem sub_one_mem_integer [IsUltrametricDist K] (hi : i ^ 2 = -1) :
    i - 1 ∈ (NormedField.valuation (K := K)).integer := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnNorm,
    norm_sub_one_eq_inv_sqrt_two hi]
  exact inv_le_one_of_one_le₀ Real.one_lt_sqrt_two.le

/-- **`i - 1` is a uniformiser of `ℚ_[2](i)`.** If `K` has degree two over `ℚ_[2]` and contains a
square root `i` of `-1`, then `i - 1` is irreducible in the valuation ring of `K`. -/
theorem irreducible_sub_one [IsUltrametricDist K] (hK : Module.finrank ℚ_[2] K = 2)
    (hi : i ^ 2 = -1) :
    Irreducible (⟨i - 1, sub_one_mem_integer hi⟩ : (NormedField.valuation (K := K)).integer) := by
  have hi1 : ‖i - 1‖ ^ 2 = 2⁻¹ := by
    rw [norm_sub_one_eq_inv_sqrt_two hi, inv_pow, Real.sq_sqrt zero_le_two]
  -- a non-unit of the valuation ring has squared norm at most `1 / 2`
  have hnu {a : (NormedField.valuation (K := K)).integer} (ha : a ≠ 0) (hu : ¬IsUnit a) :
      ‖(a : K)‖ ^ 2 ≤ 2⁻¹ := by
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one, NormedField.valuation_apply,
      ← NNReal.coe_lt_one, coe_nnNorm] at hu
    obtain ⟨m, hm⟩ := exists_norm_sq_eq_zpow hK (Subtype.coe_ne_coe.mpr ha)
    have hm0 : m < 0 := by
      rw [← zpow_lt_one_iff_right₀ (one_lt_two (α := ℝ)), ← Nat.cast_ofNat (R := ℝ), ← hm]
      exact pow_lt_one₀ (norm_nonneg _) hu two_ne_zero
    rw [hm, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ one_le_two (by omega)
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ?_ hu
    have h1 : ‖i - 1‖ < 1 := by
      rw [norm_sub_one_eq_inv_sqrt_two hi]
      exact inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
    simpa [NormedField.valuation_apply, ← NNReal.coe_lt_one] using h1
  have hab' : ‖i - 1‖ ^ 2 = ‖(a : K)‖ ^ 2 * ‖(b : K)‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, ← Subring.coe_mul, ← hab]
  by_contra hne
  rw [not_or] at hne
  have ha : a ≠ 0 := by rintro rfl; simp [hi1] at hab'
  have hb : b ≠ 0 := by rintro rfl; simp [hi1] at hab'
  nlinarith [hnu ha hne.1, hnu hb hne.2, sq_nonneg ‖(a : K)‖, sq_nonneg ‖(b : K)‖]

/-- **The normalisation at `i - 1` is integral on `ℚ_[2](i)`.** If `K` has degree two over
`ℚ_[2]`, an additive valuation `w` on `K` with `‖x‖ = √2 ^ (-w x)` takes integer values on the
nonzero elements of `K`. When `K` contains a square root `i` of `-1`, it is normalised by
`w (i - 1) = 1`. -/
theorem exists_int_of_norm_eq_sqrt_two_rpow (hK : Module.finrank ℚ_[2] K = 2)
    {w : AddValuation K (WithTop ℝ)} (hw : ∀ x ≠ 0, ‖x‖ = √2 ^ (-(w x).untop₀)) {x : K}
    (hx : x ≠ 0) : ∃ n : ℤ, w x = ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨m, hm⟩ := exists_norm_sq_eq_zpow hK hx
  refine ⟨-m, ?_⟩
  rw [Int.cast_neg, ← w.norm_eq_rpow_iff Real.one_lt_sqrt_two hw, Real.rpow_intCast]
  refine (pow_left_inj₀ (norm_nonneg x) (by positivity) two_ne_zero).mp ?_
  rw [hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    Real.sq_sqrt zero_le_two, Nat.cast_ofNat]

end QuadraticExtension

end TauCeti.NewtonPolygonRamifiedQuadraticExample
