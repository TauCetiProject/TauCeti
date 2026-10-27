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

The unit `1` is primary, so the reciprocity statements carry their nonunit hypotheses separately.

## Main definitions and results

* `TauCeti.IsPrimaryGaussian`: the predicate `(1 + i)³ ∣ α - 1` on `𝓞 K`.
* `IsPrimitiveRoot.isPrimaryGaussian_iff`: the predicate computed with any primitive fourth root
  of unity.
* `IsPrimitiveRoot.isPrimaryGaussian_add_mul_iff`: `a + b i` is primary if and only if
  `a ≡ 1` and `b ≡ 0`, or `a ≡ 3` and `b ≡ 2`, modulo `4`.
* `TauCeti.isPrimaryGaussian_intCast_iff`: a rational integer is primary exactly when it is `1`
  modulo `4`.
* `TauCeti.IsPrimaryGaussian.mul`, `TauCeti.IsPrimaryGaussian.mul_left_iff`,
  `TauCeti.IsPrimaryGaussian.of_intCast_mul`: primary elements are closed under products, and
  under division by a primary factor, in particular by a rational integer `m ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.map`: the image of a primary element under a ring endomorphism of
  `𝓞 K`, such as complex conjugation, is primary.
* `TauCeti.IsPrimaryGaussian.odd_norm`, `TauCeti.IsPrimaryGaussian.eq_one_of_isUnit`: a primary
  element has odd norm, and the only primary unit is `1`.
* `TauCeti.existsUnique_unit_mul_isPrimaryGaussian`: an element of odd norm has exactly one
  primary multiple by a unit.
* `TauCeti.IsPrimaryGaussian.norm_sub_one_div_four`: for primary `a + b i`,
  `(N(a + b i) - 1) / 4 ≡ (a - 1) / 2 (mod 2)`.
* `TauCeti.IsPrimaryGaussian.exists_multiset_prod_eq`: a primary element is a product of primary
  primes.

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
not matter. This is the normalisation of primes used in biquadratic reciprocity. The unit `1` is
primary, so the predicate is used together with a nonunit hypothesis. -/
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
