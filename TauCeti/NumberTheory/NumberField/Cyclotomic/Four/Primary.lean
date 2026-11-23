/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Quadratic

/-!
# Primary Gaussian integers

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`. An element `α` of `𝓞 K` is *primary* if `α ≡ 1 (mod (1 + i)³)`. This is the
normalisation of the quartic residue symbol used in the statement of biquadratic reciprocity:
every element of odd norm has exactly one primary associate. The congruence does not depend on
the choice of the primitive fourth root of unity `i`, since `1 - i = -i (1 + i)`.

The unit `1` is primary: prime-level Jacobi and Gauss sum evaluations add a `Prime` or `IsMaximal`
hypothesis separately, whereas the supplementary and biquadratic reciprocity laws hold at `1`
without a nonunit hypothesis.

## Main definitions and results

* `TauCeti.IsPrimaryGaussian`: the predicate `(1 + i)³ ∣ α - 1` on `𝓞 K`.
* `IsPrimitiveRoot.isPrimaryGaussian_iff`: the predicate computed with any primitive fourth root
  of unity.
* `IsPrimitiveRoot.isPrimaryGaussian_add_mul_iff`: `a + b i` is primary if and only if
  `a ≡ 1` and `b ≡ 0`, or `a ≡ 3` and `b ≡ 2`, modulo `4`.
* `TauCeti.isPrimaryGaussian_intCast_iff`: a rational integer is primary exactly when it is `1`
  modulo `4`.
* `TauCeti.IsPrimaryGaussian.mul`, `TauCeti.IsPrimaryGaussian.mul_left_iff`,
  `TauCeti.IsPrimaryGaussian.of_intCast_mul`,
  `TauCeti.IsPrimaryGaussian.exists_intCast_mul_add_mul_isCoprime`: primary elements are closed
  under products and under division by a primary factor (in particular by a rational integer
  `m ≡ 1 (mod 4)`), and every primary element factors out a signed rational integer `m ≡ 1 (mod 4)`
  leaving a primary quotient with coprime coordinates.
* `TauCeti.IsPrimaryGaussian.map`: the image of a primary element under a ring endomorphism of
  `𝓞 K`, such as complex conjugation, is primary.
* `TauCeti.IsPrimaryGaussian.odd_norm`, `TauCeti.IsPrimaryGaussian.ne_zero`,
  `TauCeti.IsPrimaryGaussian.eq_one_of_isUnit`: a primary element has odd norm (hence is nonzero),
  and the only primary unit is `1`.
* `TauCeti.existsUnique_unit_mul_isPrimaryGaussian`: an element of odd norm has exactly one
  primary multiple by a unit.
* `TauCeti.IsPrimaryGaussian.norm_sub_one_div_four`: for primary `a + b i`,
  `(N(a + b i) - 1) / 4 ≡ (a - 1) / 2 (mod 2)`;
  `TauCeti.IsPrimaryGaussian.norm_sub_one_div_four_modEq_four` refines this to
  `(N(a + b i) - 1) / 4 ≡ -((a - 1) / 2) (mod 4)`.
* `TauCeti.IsPrimaryGaussian.add_modEq_one`, `TauCeti.IsPrimaryGaussian.sub_modEq_one`,
  `TauCeti.IsPrimaryGaussian.four_dvd_sub_sub_sq_sub_one`,
  `TauCeti.IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_modEq_add`: for primary `a + b i`,
  `a + b ≡ 1 (mod 4)`, `a - b ≡ 1 (mod 4)`, `4 ∣ a - b - b² - 1`, and the exponent
  `(a - b - b² - 1) / 4` is additive modulo `4` under multiplication of primary elements.
* `TauCeti.IsPrimaryGaussian.absNorm_span_singleton_coprime_four`: a primary element generates
  an ideal of norm prime to `4`, and `TauCeti.IsPrimaryGaussian.natCast_absNorm_sub_one_div_four`
  identifies `(N(λ 𝓞 K) - 1) / 4` with the integer `(N(λ) - 1) / 4`.
* `TauCeti.IsPrimaryGaussian.absNorm_span_singleton_modEq_one_or_five`,
  `TauCeti.IsPrimaryGaussian.absNorm_span_singleton_add_mul_modEq_one_iff`,
  `TauCeti.IsPrimaryGaussian.absNorm_span_singleton_add_mul_modEq_five_iff`: a primary element
  generates an ideal of norm `1` or `5` modulo `8`, distinguished for `a + b i` by `a ≡ 1` versus
  `a ≡ 3` modulo `4`.
* `TauCeti.IsPrimaryGaussian.exists_multiset_prod_eq`,
  `TauCeti.IsPrimaryGaussian.induction_on_prime`: a primary element is a product of primary
  primes, giving an induction principle on primary prime factorisations.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §7.
* N. Xu, *Reciprocity Laws*, §5, Proposition 5.1, Definitions 5.3–5.4 and Propositions 5.5–5.6.
-/

public section

open NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- An element `α` of `𝓞 K = ℤ[i]` is *primary* if `α ≡ 1 (mod (1 + i)³)`, where `i` is a
primitive fourth root of unity; by `IsPrimitiveRoot.isPrimaryGaussian_iff` the choice of `i` does
not matter. Every element of odd norm has a unique primary associate, normalising the generators of
odd ideals in biquadratic reciprocity. The unit `1` is primary: prime-level Gauss and Jacobi sum
lemmas add a `Prime` or `IsMaximal` hypothesis, while the reciprocity and supplementary laws hold at
`1` without a nonunit hypothesis. -/
def IsPrimaryGaussian (x : 𝓞 K) : Prop :=
  (1 + (IsCyclotomicExtension.zeta_spec 4 ℚ K).toInteger) ^ 3 ∣ x - 1

/-- The defining congruence of `IsPrimaryGaussian`, computed with any primitive fourth root of
unity `ζ`. -/
theorem _root_.IsPrimitiveRoot.isPrimaryGaussian_iff {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {x : 𝓞 K} : IsPrimaryGaussian x ↔ (1 + hζ.toInteger) ^ 3 ∣ x - 1 :=
  (associated_one_add_of_sq_eq_neg_one
    (IsCyclotomicExtension.zeta_spec 4 ℚ K).toInteger_isPrimitiveRoot.sq_eq_neg_one
    hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one).pow_pow.dvd_iff_dvd_left

/-- **The coordinate criterion for primary Gaussian integers.** For integers `a` and `b`, the
element `a + b ζ` of `𝓞 K = ℤ[ζ]` is primary if and only if `a ≡ 1` and `b ≡ 0`, or `a ≡ 3` and
`b ≡ 2`, modulo `4`. -/
@[simp]
theorem _root_.IsPrimitiveRoot.isPrimaryGaussian_add_mul_iff {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b : ℤ} : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) ↔
      a ≡ 1 [ZMOD 4] ∧ b ≡ 0 [ZMOD 4] ∨ a ≡ 3 [ZMOD 4] ∧ b ≡ 2 [ZMOD 4] := by
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have h : ((a : 𝓞 K) + b * hζ.toInteger - 1) * (1 + hζ.toInteger) =
      ((a - 1 - b : ℤ) : 𝓞 K) + ((a - 1 + b : ℤ) : 𝓞 K) * hζ.toInteger := by
    push_cast
    linear_combination (b : 𝓞 K) * hsq
  rw [hζ.isPrimaryGaussian_iff, one_add_pow_three_dvd_iff_four_dvd_mul two_ne_zero hsq, h,
    ← Int.cast_ofNat, hζ.intCast_dvd_intCast_add_intCast_mul_toInteger_iff (by decide)]
  simp only [Int.ModEq]
  omega

variable {x y : 𝓞 K}

/-- The unit `1` is primary. -/
@[simp]
theorem isPrimaryGaussian_one : IsPrimaryGaussian (1 : 𝓞 K) := by
  simp [IsPrimaryGaussian]

/-- The product of two primary elements is primary. -/
theorem IsPrimaryGaussian.mul (hx : IsPrimaryGaussian x) (hy : IsPrimaryGaussian y) :
    IsPrimaryGaussian (x * y) := by
  have h : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [IsPrimaryGaussian, h]
  exact dvd_add (dvd_mul_of_dvd_left hx y) hy

/-- If `x` is primary, then `x * y` is primary exactly when `y` is: a primary element is
congruent to `1` modulo `(1 + i)³`. -/
theorem IsPrimaryGaussian.mul_left_iff (hx : IsPrimaryGaussian x) :
    IsPrimaryGaussian (x * y) ↔ IsPrimaryGaussian y := by
  refine ⟨fun hxy ↦ ?_, hx.mul⟩
  have h : y - 1 = (x * y - 1) - (x - 1) - (x - 1) * (y - 1) := by ring
  rw [IsPrimaryGaussian, h]
  exact dvd_sub (dvd_sub hxy hx) (dvd_mul_of_dvd_left hx _)

/-- Absorbing a unit twist: if `u * p` and `v * (p * y)` are primary, then so is `(v * u⁻¹) * y`. -/
private theorem IsPrimaryGaussian.unit_mul_inv_mul {u v : (𝓞 K)ˣ} {p : 𝓞 K}
    (hu : IsPrimaryGaussian ((u : 𝓞 K) * p)) (hv : IsPrimaryGaussian ((v : 𝓞 K) * (p * y))) :
    IsPrimaryGaussian (((v * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * y) := by
  refine hu.mul_left_iff.mp ?_
  convert hv using 1
  push_cast
  linear_combination ((v : 𝓞 K) * p * y) * u.mul_inv

/-- The image of a primary element under a ring endomorphism of `𝓞 K`, such as complex
conjugation, is primary. -/
theorem IsPrimaryGaussian.map (hx : IsPrimaryGaussian x) (σ : 𝓞 K →+* 𝓞 K) :
    IsPrimaryGaussian (σ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hσ : σ hζ.toInteger ^ 2 = -1 := by rw [← map_pow, hsq, map_neg, map_one]
  have h := map_dvd σ hx
  rw [map_pow, map_add, map_one, map_sub, map_one] at h
  exact (associated_one_add_of_sq_eq_neg_one hsq hσ).pow_pow.dvd_iff_dvd_left.mpr h

/-- A primary element has odd norm; in particular no element of even norm, such as `1 + i`, is
primary. -/
theorem IsPrimaryGaussian.odd_norm (hx : IsPrimaryGaussian x) : Odd (Algebra.norm ℤ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  rw [hζ.odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four, Int.odd_iff]
  simp only [Int.ModEq] at hx
  omega

/-- A primary element of `𝓞 K = ℤ[i]` is nonzero. -/
theorem IsPrimaryGaussian.ne_zero (hx : IsPrimaryGaussian x) : x ≠ 0 :=
  fun h ↦ absurd (h ▸ hx.odd_norm) (by simp)

/-- **The norm congruence of a primary Gaussian integer.** For primary `a + b i`, the quotient
`(N(a + b i) - 1) / 4` has the parity of `(a - 1) / 2`. This is the exponent comparison used in
the supplementary laws of quartic reciprocity. -/
theorem IsPrimaryGaussian.norm_sub_one_div_four {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    (Algebra.norm ℤ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) - 1) / 4 ≡ (a - 1) / 2 [ZMOD 2] := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
  simp only [Int.ModEq] at hx
  rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 1 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l := ⟨b / 4, by omega⟩
    rw [show (4 * k + 1) ^ 2 + (4 * l) ^ 2 - 1 = 4 * (4 * k ^ 2 + 2 * k + 4 * l ^ 2) by ring,
      show 4 * k + 1 - 1 = 2 * (2 * k) by ring, Int.mul_ediv_cancel_left _ (by norm_num),
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact Int.modEq_iff_dvd.mpr ⟨-2 * k ^ 2 - 2 * l ^ 2, by ring⟩
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 3 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l + 2 := ⟨b / 4, by omega⟩
    rw [show (4 * k + 3) ^ 2 + (4 * l + 2) ^ 2 - 1 =
        4 * (4 * k ^ 2 + 6 * k + 4 * l ^ 2 + 4 * l + 3) by ring,
      show 4 * k + 3 - 1 = 2 * (2 * k + 1) by ring, Int.mul_ediv_cancel_left _ (by norm_num),
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact Int.modEq_iff_dvd.mpr ⟨-2 * k ^ 2 - 2 * k - 2 * l ^ 2 - 2 * l - 1, by ring⟩

/-- **The norm congruence of a primary Gaussian integer modulo `4`.** For primary `a + b i`,
`(N(a + b i) - 1) / 4 ≡ -((a - 1) / 2) (mod 4)`. This is the exponent comparison of the
supplementary law for `i` in quartic reciprocity. -/
theorem IsPrimaryGaussian.norm_sub_one_div_four_modEq_four {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b : ℤ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    (Algebra.norm ℤ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) - 1) / 4 ≡ -((a - 1) / 2)
      [ZMOD 4] := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four, Int.ModEq]
  simp only [Int.ModEq] at hx
  rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 1 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l := ⟨b / 4, by omega⟩
    ring_nf
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 3 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l + 2 := ⟨b / 4, by omega⟩
    ring_nf
    omega

/-- For primary `a + b i`, the sum of coordinates satisfies `a + b ≡ 1 (mod 4)`. -/
theorem IsPrimaryGaussian.add_modEq_one {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    a + b ≡ 1 [ZMOD 4] := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  simp only [Int.ModEq] at hx ⊢
  omega

/-- For primary `a + b i`, the difference of coordinates satisfies `a - b ≡ 1 (mod 4)`. -/
theorem IsPrimaryGaussian.sub_modEq_one {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    a - b ≡ 1 [ZMOD 4] := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  simp only [Int.ModEq] at hx ⊢
  omega

/-- **Integrality of the `1 + i` supplement exponent.** For primary `a + b i`, the integer
`a - b - b ^ 2 - 1` is divisible by `4`. -/
theorem IsPrimaryGaussian.four_dvd_sub_sub_sq_sub_one {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b : ℤ} (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    4 ∣ a - b - b ^ 2 - 1 := by
  have hsub := hx.sub_modEq_one
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  obtain ⟨m, rfl⟩ : ∃ m, b = 2 * m := ⟨b / 2, by simp only [Int.ModEq] at hx; omega⟩
  obtain ⟨k, hk⟩ := hsub.symm.dvd
  exact ⟨k - m ^ 2, by linear_combination hk⟩

/-- **Additivity modulo `4` of the `1 + i` supplement exponent.** For primary elements
`a₁ + b₁ i` and `a₂ + b₂ i`, the exponent `(a - b - b ^ 2 - 1) / 4` of their product
`(a₁ a₂ - b₁ b₂) + (a₁ b₂ + b₁ a₂) i` is congruent modulo `4` to the sum of their exponents. -/
theorem IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_modEq_add {ζ : K}
    {hζ : IsPrimitiveRoot ζ 4} {a₁ b₁ a₂ b₂ : ℤ}
    (hx : IsPrimaryGaussian ((a₁ : 𝓞 K) + (b₁ : 𝓞 K) * hζ.toInteger))
    (hy : IsPrimaryGaussian ((a₂ : 𝓞 K) + (b₂ : 𝓞 K) * hζ.toInteger)) :
    ((a₁ * a₂ - b₁ * b₂) - (a₁ * b₂ + b₁ * a₂) - (a₁ * b₂ + b₁ * a₂) ^ 2 - 1) / 4 ≡
      (a₁ - b₁ - b₁ ^ 2 - 1) / 4 + (a₂ - b₂ - b₂ ^ 2 - 1) / 4 [ZMOD 4] := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx hy
  simp only [Int.ModEq] at hx hy
  obtain ⟨u₁, rfl⟩ : ∃ u₁, a₁ = 2 * u₁ + 1 := ⟨(a₁ - 1) / 2, by omega⟩
  obtain ⟨v₁, rfl⟩ : ∃ v₁, b₁ = 2 * v₁ := ⟨b₁ / 2, by omega⟩
  obtain ⟨r₁, rfl⟩ : ∃ r₁, v₁ = u₁ + 2 * r₁ := ⟨(v₁ - u₁) / 2, by omega⟩
  obtain ⟨u₂, rfl⟩ : ∃ u₂, a₂ = 2 * u₂ + 1 := ⟨(a₂ - 1) / 2, by omega⟩
  obtain ⟨v₂, rfl⟩ : ∃ v₂, b₂ = 2 * v₂ := ⟨b₂ / 2, by omega⟩
  obtain ⟨r₂, rfl⟩ : ∃ r₂, v₂ = u₂ + 2 * r₂ := ⟨(v₂ - u₂) / 2, by omega⟩
  have hsingle (u r : ℤ) :
      ((2 * u + 1) - 2 * (u + 2 * r) - (2 * (u + 2 * r)) ^ 2 - 1) / 4 =
        -r - (u + 2 * r) ^ 2 := by
    have h4 : (2 * u + 1) - 2 * (u + 2 * r) - (2 * (u + 2 * r)) ^ 2 - 1 =
        4 * (-r - (u + 2 * r) ^ 2) := by ring
    rw [h4, Int.mul_ediv_cancel_left _ (by decide)]
  set t : ℤ := 2 * u₁ * u₂ + r₁ + r₂ + 2 * u₁ * r₂ + 2 * u₂ * r₁
  have hprod :
      (((2 * u₁ + 1) * (2 * u₂ + 1) - 2 * (u₁ + 2 * r₁) * (2 * (u₂ + 2 * r₂))) -
        ((2 * u₁ + 1) * (2 * (u₂ + 2 * r₂)) + 2 * (u₁ + 2 * r₁) * (2 * u₂ + 1)) -
        ((2 * u₁ + 1) * (2 * (u₂ + 2 * r₂)) + 2 * (u₁ + 2 * r₁) * (2 * u₂ + 1)) ^ 2 - 1) =
      4 * (-2 * u₁ * u₂ - r₁ - r₂ - 4 * u₁ * r₂ - 4 * u₂ * r₁ - 4 * r₁ * r₂ -
        (u₁ + u₂ + 2 * t) ^ 2) := by
    simp only [t]
    ring
  rw [hprod, Int.mul_ediv_cancel_left _ (by decide), hsingle, hsingle]
  exact Int.modEq_iff_dvd.mpr
    ⟨u₁ * u₂ - u₁ * r₁ - r₁ ^ 2 - u₂ * r₂ - r₂ ^ 2 + u₁ * r₂ + u₂ * r₁ + r₁ * r₂ +
      (u₁ + u₂) * t + t ^ 2, by ring⟩

/-- A primary element of `𝓞 K = ℤ[i]` generates an ideal whose norm is odd, hence prime to `4`. -/
theorem IsPrimaryGaussian.absNorm_span_singleton_coprime_four (hx : IsPrimaryGaussian x) :
    (Ideal.absNorm (Ideal.span {x})).Coprime 4 := by
  rw [Ideal.absNorm_span_singleton]
  -- `4 = 2 ^ 2` holds by `rfl`, so coprimality to `2` suffices.
  exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hx.odd_norm))

/-- For primary `x`, the natural number `(N(x 𝓞 K) - 1) / 4`, with `N` the absolute ideal norm,
is the integer `(N(x) - 1) / 4` of `IsPrimaryGaussian.norm_sub_one_div_four`. This converts the
exponent of a power residue symbol at `x 𝓞 K` into the integer exponent whose congruences are
computed above. -/
theorem IsPrimaryGaussian.natCast_absNorm_sub_one_div_four (hx : IsPrimaryGaussian x) :
    (((Ideal.absNorm (Ideal.span {x}) - 1) / 4 : ℕ) : ℤ) =
      (Algebra.norm ℤ x - 1) / 4 := by
  have hcop := hx.absNorm_span_singleton_coprime_four
  have hN : (Ideal.absNorm (Ideal.span {x}) : ℤ) = Algebra.norm ℤ x :=
    RingOfIntegers.natCast_absNorm_span_singleton_of_four x
  have h₀ : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcop
    exact absurd hcop (by norm_num)
  omega

/-- Every primary element of `𝓞 K = ℤ[i]` generates an ideal of norm congruent to `1` or `5`
modulo `8`. -/
theorem IsPrimaryGaussian.absNorm_span_singleton_modEq_one_or_five (hx : IsPrimaryGaussian x) :
    Ideal.absNorm (Ideal.span {x}) ≡ 1 [MOD 8] ∨
      Ideal.absNorm (Ideal.span {x}) ≡ 5 [MOD 8] := by
  have h := absNorm_modEq_one hx.absNorm_span_singleton_coprime_four
  simp only [Nat.ModEq] at h ⊢
  omega

/-- A primary Gaussian integer `a + b i` generates an ideal of norm congruent to `1` modulo `8`
if and only if `a ≡ 1 (mod 4)`. -/
theorem IsPrimaryGaussian.absNorm_span_singleton_add_mul_modEq_one_iff
    {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    Ideal.absNorm (Ideal.span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) ≡ 1 [MOD 8] ↔
      a ≡ 1 [ZMOD 4] := by
  have h4 := absNorm_modEq_one hx.absNorm_span_singleton_coprime_four
  have hdiv := hx.norm_sub_one_div_four
  rw [← hx.natCast_absNorm_sub_one_div_four] at hdiv
  have hprim := hζ.isPrimaryGaussian_add_mul_iff.mp hx
  simp only [Nat.ModEq, Int.ModEq] at h4 hdiv hprim ⊢
  omega

/-- A primary Gaussian integer `a + b i` generates an ideal of norm congruent to `5` modulo `8`
if and only if `a ≡ 3 (mod 4)`. -/
theorem IsPrimaryGaussian.absNorm_span_singleton_add_mul_modEq_five_iff
    {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    Ideal.absNorm (Ideal.span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) ≡ 5 [MOD 8] ↔
      a ≡ 3 [ZMOD 4] := by
  have h8 := hx.absNorm_span_singleton_modEq_one_or_five
  have h1 := hx.absNorm_span_singleton_add_mul_modEq_one_iff
  have hprim := hζ.isPrimaryGaussian_add_mul_iff.mp hx
  simp only [Nat.ModEq, Int.ModEq] at h8 h1 hprim ⊢
  omega

/-- A rational integer is primary exactly when it is congruent to `1` modulo `4`. -/
@[simp]
theorem isPrimaryGaussian_intCast_iff {m : ℤ} :
    IsPrimaryGaussian (m : 𝓞 K) ↔ m ≡ 1 [ZMOD 4] := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have h : (m : 𝓞 K) = (m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger := by simp
  rw [h, hζ.isPrimaryGaussian_add_mul_iff]
  simp [Int.ModEq]

/-- A natural number is primary exactly when it is congruent to `1` modulo `4`. -/
@[simp]
theorem isPrimaryGaussian_natCast_iff {n : ℕ} :
    IsPrimaryGaussian (n : 𝓞 K) ↔ n ≡ 1 [MOD 4] := by
  rw [← Int.cast_natCast, isPrimaryGaussian_intCast_iff]
  exact Int.natCast_modEq_iff

/-- A numeral is primary exactly when it is congruent to `1` modulo `4`. -/
@[simp]
theorem isPrimaryGaussian_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    IsPrimaryGaussian (ofNat(n) : 𝓞 K) ↔ ofNat(n) ≡ 1 [MOD 4] :=
  isPrimaryGaussian_natCast_iff

/-- If `m * x` is primary for a rational integer `m ≡ 1 (mod 4)`, then `x` is primary. -/
theorem IsPrimaryGaussian.of_intCast_mul {m : ℤ} (hmx : IsPrimaryGaussian ((m : 𝓞 K) * x))
    (hm : m ≡ 1 [ZMOD 4]) : IsPrimaryGaussian x :=
  (isPrimaryGaussian_intCast_iff.mpr hm).mul_left_iff.mp hmx

/-- Every primary element `x` of `𝓞 K = ℤ[i]` factors as `m * (a + b i)` with `m ≡ 1 (mod 4)` a
rational integer, `a` and `b` coprime, and `a + b i` primary. -/
theorem IsPrimaryGaussian.exists_intCast_mul_add_mul_isCoprime {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {x : 𝓞 K} (hx : IsPrimaryGaussian x) :
    ∃ m a b : ℤ, m ≡ 1 [ZMOD 4] ∧ IsCoprime a b ∧
      IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) ∧
      x = (m : 𝓞 K) * ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) := by
  obtain ⟨a₀, b₀, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hodd : Odd (a₀ + b₀) :=
    (hζ.odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four (a := a₀) (b := b₀)).mp hx.odd_norm
  set g : ℕ := a₀.gcd b₀ with hg_def
  have hg_odd : Odd g := by
    by_contra hg_even
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hg_even
    have hdvd : (2 : ℤ) ∣ a₀ + b₀ :=
      dvd_trans ⟨k, by omega⟩ (dvd_add (Int.gcd_dvd_left a₀ b₀) (Int.gcd_dvd_right a₀ b₀))
    obtain ⟨u, hu⟩ := hodd
    omega
  obtain ⟨a₁, b₁, hcop₁, ha₀, hb₀⟩ := Int.exists_gcd_one hg_odd.pos
  rw [← hg_def] at ha₀ hb₀
  have hcop : IsCoprime a₁ b₁ := Int.isCoprime_iff_gcd_eq_one.mpr hcop₁
  have hg_mod : (g : ℤ) ≡ 1 [ZMOD 4] ∨ (-(g : ℤ)) ≡ 1 [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hg_odd
    simp only [Int.ModEq, ht]
    push_cast
    omega
  rcases hg_mod with hg1 | hg3
  · have hmul : (a₀ : 𝓞 K) + (b₀ : 𝓞 K) * hζ.toInteger =
        ((g : ℤ) : 𝓞 K) * ((a₁ : 𝓞 K) + (b₁ : 𝓞 K) * hζ.toInteger) := by
      rw [ha₀, hb₀]
      push_cast
      ring
    exact ⟨g, a₁, b₁, hg1, hcop, IsPrimaryGaussian.of_intCast_mul (hmul ▸ hx) hg1, hmul⟩
  · set m : ℤ := -(g : ℤ)
    have hmul : (a₀ : 𝓞 K) + (b₀ : 𝓞 K) * hζ.toInteger =
        (m : 𝓞 K) * (((-a₁ : ℤ) : 𝓞 K) + ((-b₁ : ℤ) : 𝓞 K) * hζ.toInteger) := by
      simp only [m]
      rw [ha₀, hb₀]
      push_cast
      ring
    exact ⟨m, -a₁, -b₁, hg3, hcop.neg_left.neg_right,
      IsPrimaryGaussian.of_intCast_mul (hmul ▸ hx) hg3, hmul⟩

/-- The only primary unit of `𝓞 K = ℤ[i]` is `1`: of the units `±1, ±i`, only `1` is congruent
to `1` modulo `(1 + i)³`. -/
theorem IsPrimaryGaussian.eq_one_of_isUnit (hx : IsPrimaryGaussian x) (hu : IsUnit x) :
    x = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hx
  rw [hζ.isUnit_intCast_add_intCast_mul_toInteger_iff_of_four] at hu
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a]
  simp only [Int.ModEq] at hx
  obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 0 := by omega
  simp

/-- **Primary associates in `ℤ[i]`.** An element of `𝓞 K = ℤ[i]` of odd norm has exactly one
primary multiple by a unit. -/
theorem existsUnique_unit_mul_isPrimaryGaussian (hx : Odd (Algebra.norm ℤ x)) :
    ∃! u : (𝓞 K)ˣ, IsPrimaryGaussian ((u : 𝓞 K) * x) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, IsPrimaryGaussian ((u : 𝓞 K) * x) := by
    obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
    rw [hζ.odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four, Int.odd_iff] at hx
    set i := hζ.toInteger
    have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    have hi : IsUnit i := hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num)
    -- A unit `u` with `u * (a + b i) = a' + b' i` for primary coordinates `a', b'` works.
    have key (u : (𝓞 K)ˣ) (a' b' : ℤ)
        (h : (u : 𝓞 K) * ((a : 𝓞 K) + (b : 𝓞 K) * i) = (a' : 𝓞 K) + (b' : 𝓞 K) * i)
        (h' : a' % 4 = 1 ∧ b' % 4 = 0 ∨ a' % 4 = 3 ∧ b' % 4 = 2) :
        ∃ u : (𝓞 K)ˣ, IsPrimaryGaussian ((u : 𝓞 K) * ((a : 𝓞 K) + (b : 𝓞 K) * i)) :=
      ⟨u, by rw [h, hζ.isPrimaryGaussian_add_mul_iff]; exact h'⟩
    rcases (by omega : (a % 4 = 1 ∧ b % 4 = 0 ∨ a % 4 = 3 ∧ b % 4 = 2) ∨
        (a % 4 = 3 ∧ b % 4 = 0 ∨ a % 4 = 1 ∧ b % 4 = 2) ∨
        (a % 4 = 0 ∧ b % 4 = 3 ∨ a % 4 = 2 ∧ b % 4 = 1) ∨
        (a % 4 = 0 ∧ b % 4 = 1 ∨ a % 4 = 2 ∧ b % 4 = 3)) with h | h | h | h
    · exact key 1 a b (by simp) h
    · exact key (-1) (-a) (-b) (by push_cast; ring) (by omega)
    · exact key hi.unit (-b) a
        (by push_cast [IsUnit.unit_spec]; linear_combination (b : 𝓞 K) * hsq) (by omega)
    · exact key (-hi.unit) b (-a)
        (by push_cast [Units.val_neg, IsUnit.unit_spec]; linear_combination (-b : 𝓞 K) * hsq)
        (by omega)
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  have h := hu.unit_mul_inv_mul (y := 1) (by rwa [mul_one])
  rw [mul_one] at h
  exact mul_inv_eq_one.mp (Units.val_eq_one.mp (h.eq_one_of_isUnit (v * u⁻¹).isUnit))

/-- **Factorisation into primary primes.** A primary element of `𝓞 K = ℤ[i]` is a product of
primary primes. A primary nonunit is therefore a nonempty such product; the unit `1` is the empty
product. -/
theorem IsPrimaryGaussian.exists_multiset_prod_eq (hx : IsPrimaryGaussian x) :
    ∃ s : Multiset (𝓞 K), (∀ p ∈ s, Prime p ∧ IsPrimaryGaussian p) ∧ s.prod = x := by
  have := isPrincipalIdealRing_ringOfIntegers_four K
  -- Induct on a prime factorisation, allowing a unit twist `v` so that the primary normalisation
  -- of each prime factor can be absorbed into the cofactor.
  suffices h : ∀ v : (𝓞 K)ˣ, IsPrimaryGaussian ((v : 𝓞 K) * x) →
      ∃ s : Multiset (𝓞 K), (∀ p ∈ s, Prime p ∧ IsPrimaryGaussian p) ∧ s.prod = v * x by
    simpa using h 1 (by simpa using hx)
  clear hx
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro v hv
    exact absurd hv.odd_norm (by simp)
  | h₂ y hy =>
    intro v hv
    exact ⟨0, by simp, by rw [Multiset.prod_zero, hv.eq_one_of_isUnit (v.isUnit.mul hy)]⟩
  | h₃ y p _ hp ih =>
    intro v hv
    have hodd : Odd (Algebra.norm ℤ p) := by
      have h := hv.odd_norm
      rw [map_mul, map_mul, Int.odd_mul, Int.odd_mul] at h
      exact h.2.1
    obtain ⟨u, hu, -⟩ := existsUnique_unit_mul_isPrimaryGaussian hodd
    obtain ⟨s, hs, hprod⟩ := ih _ (hu.unit_mul_inv_mul hv)
    refine ⟨(u * p) ::ₘ s, ?_, ?_⟩
    · intro q hq
      rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact ⟨Associated.prime ⟨u, mul_comm _ _⟩ hp, hu⟩
      · exact hs q hq
    · rw [Multiset.prod_cons, hprod]
      push_cast
      linear_combination ((v : 𝓞 K) * p * y) * u.mul_inv

/-- **Prime-factorisation induction for primary Gaussian integers.** To prove a property of a
primary element of `𝓞 K = ℤ[i]`, it suffices to prove it for `1` and for `p * y` where `p` is a
primary prime and `y` is a primary element satisfying the property. -/
@[elab_as_elim]
theorem IsPrimaryGaussian.induction_on_prime
    {motive : (x : 𝓞 K) → IsPrimaryGaussian x → Prop} {x : 𝓞 K} (hx : IsPrimaryGaussian x)
    (one : motive 1 isPrimaryGaussian_one)
    (mul : ∀ p y, Prime p → (hp : IsPrimaryGaussian p) → (hy : IsPrimaryGaussian y) →
      motive y hy → motive (p * y) (hp.mul hy)) :
    motive x hx := by
  obtain ⟨s, hs, hprod⟩ := hx.exists_multiset_prod_eq
  induction s using Multiset.induction_on generalizing x with
  | empty =>
    rw [Multiset.prod_zero] at hprod
    subst hprod
    exact one
  | cons p s ih =>
    rw [Multiset.prod_cons] at hprod
    subst hprod
    obtain ⟨hp, hp_prim⟩ := hs p (Multiset.mem_cons_self p s)
    have hs' : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q := fun q hq ↦
      hs q (Multiset.mem_cons_of_mem hq)
    have hs_prim : IsPrimaryGaussian s.prod := hp_prim.mul_left_iff.mp hx
    exact mul p s.prod hp hp_prim hs_prim (ih hs_prim hs' rfl)

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- `-1 + 2i` and `-1 - 2i`, the two primary primes above `5`, and `3 + 2i`, of norm `13`, are
primary; `1 + 2i` is not, although its real part is odd and its imaginary part even, and neither
is `1 + i`, of norm `2`. -/
example : IsPrimaryGaussian (((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
  rw [hζ.isPrimaryGaussian_add_mul_iff]; decide

example : IsPrimaryGaussian (((-1 : ℤ) : 𝓞 K) + ((-2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
  rw [hζ.isPrimaryGaussian_add_mul_iff]; decide

example : IsPrimaryGaussian (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
  rw [hζ.isPrimaryGaussian_add_mul_iff]; decide

example : ¬ IsPrimaryGaussian (((1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
  rw [hζ.isPrimaryGaussian_add_mul_iff]; decide

example : ¬ IsPrimaryGaussian (((1 : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * hζ.toInteger) := by
  rw [hζ.isPrimaryGaussian_add_mul_iff]; decide

/- The norm of `3 + 2i` is `13`, and `(13 - 1) / 4 = 3` has the parity of `(3 - 1) / 2 = 1`. -/
example : Algebra.norm ℤ (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) = 13 := by
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; norm_num

end Examples

/- The rational prime `3` is not primary, while its associate `-3` is; `5` is primary. -/
example : ¬ IsPrimaryGaussian (3 : 𝓞 K) := by simp [Nat.ModEq]

example : IsPrimaryGaussian ((-3 : ℤ) : 𝓞 K) := by
  rw [isPrimaryGaussian_intCast_iff]; decide

example : IsPrimaryGaussian (5 : 𝓞 K) := by simp [Nat.ModEq]

end TauCeti
