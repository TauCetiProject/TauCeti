/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Primary elements of `ℤ[ζ_p]`

Let `p` be an odd prime, `K = ℚ(ζ_p)` and `ζ` a primitive `p`-th root of unity, so that
`𝓞 K = ℤ[ζ]` and `λ = ζ - 1` generates the unique prime above `p`. An element `α` of `𝓞 K` is
*primary* if it is prime to `λ` and congruent to a rational integer modulo `λ ^ 2`. This is the
normalisation used in the statement of the Eisenstein reciprocity law: every `α` prime to `p` has
exactly one primary multiple `ζ ^ c * α` with `c ∈ ℤ/p`.

The predicate `TauCeti.IsEisensteinPrimary ζ α` is stated for an arbitrary element `ζ` of a
commutative ring, where it is already closed under products (`IsEisensteinPrimary.mul`). It is not
to be confused with `TauCeti.IsPrimaryEisenstein`, the normalisation `α ≡ 2 (mod 3)` of the
Eisenstein integers `ℤ[ω]` used in cubic reciprocity. Its content is for `ℚ(ζ_p)`:

* `IsPrimitiveRoot.exists_toInteger_sub_one_sq_dvd_sub_intCast_add_intCast_mul`: every `α` in
  `𝓞 K` is congruent to `a + b λ` modulo `λ ^ 2` for some integers `a` and `b`;
* `IsPrimitiveRoot.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff`: for `p` odd,
  `λ ^ 2 ∣ m + e λ` with `m, e ∈ ℤ` if and only if `p ∣ m` and `p ∣ e`, so the coordinates `a`
  and `b` above are unique modulo `p`;
* `IsPrimitiveRoot.isEisensteinPrimary_intCast_iff`: a rational integer is primary exactly when
  it is prime to `p`, with versions for natural numbers and numerals;
* `IsPrimitiveRoot.isEisensteinPrimary_toInteger_pow_mul_iff`: if `α ≡ a + b λ (mod λ ^ 2)`, then
  `ζ ^ c * α` is primary if and only if `p ∣ b + c a`;
* `IsPrimitiveRoot.existsUnique_isEisensteinPrimary_toInteger_pow_mul`: for `α` prime to `λ`
  there is exactly one `c ∈ ℤ/p` such that `ζ ^ c * α` is primary.

The predicate does not depend on the choice of `ζ`
(`IsPrimitiveRoot.isEisensteinPrimary_toInteger_iff`), and being prime to `λ` is the same as being
prime to `p` (`IsPrimitiveRoot.isCoprime_toInteger_sub_one_iff_isCoprime_natCast`).

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, (19)–(22).
* N. Xu, *Reciprocity Laws*, §6, Definition 6.7 and Proposition 6.8.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2.
-/

public section

open NumberField

namespace TauCeti

variable {R : Type*} [CommRing R] {ζ x y : R}

/-- An element `x` of a commutative ring is *primary* with respect to `ζ` if it is coprime to
`ζ - 1` and congruent to a rational integer modulo `(ζ - 1) ^ 2`. For a primitive `p`-th root of
unity `ζ` in `ℤ[ζ_p]`, `p` an odd prime, this is the normalisation of elements prime to `p` used in
the Eisenstein reciprocity law. -/
def IsEisensteinPrimary (ζ x : R) : Prop :=
  IsCoprime x (ζ - 1) ∧ ∃ a : ℤ, (ζ - 1) ^ 2 ∣ x - a

/-- Unfolding `IsEisensteinPrimary`. -/
theorem isEisensteinPrimary_iff :
    IsEisensteinPrimary ζ x ↔ IsCoprime x (ζ - 1) ∧ ∃ a : ℤ, (ζ - 1) ^ 2 ∣ x - a :=
  Iff.rfl

/-- The unit `1` is primary. -/
@[simp]
theorem isEisensteinPrimary_one : IsEisensteinPrimary ζ 1 :=
  ⟨isCoprime_one_left, 1, by simp⟩

/-- The product of two primary elements is primary. -/
theorem IsEisensteinPrimary.mul (hx : IsEisensteinPrimary ζ x) (hy : IsEisensteinPrimary ζ y) :
    IsEisensteinPrimary ζ (x * y) := by
  obtain ⟨hx, a, s, hs⟩ := hx
  obtain ⟨hy, b, t, ht⟩ := hy
  refine ⟨hx.mul_left hy, a * b, (ζ - 1) ^ 2 * s * t + a * t + b * s, ?_⟩
  push_cast
  linear_combination y * hs + (a + (ζ - 1) ^ 2 * s) * ht

end TauCeti

namespace IsPrimitiveRoot

open TauCeti IsCyclotomicExtension.Rat

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit hp in
include hζ in
/-- For any primitive `p`-th root of unity `ζ`, every element of `𝓞 K = ℤ[ζ]` is congruent to
`a + b (ζ - 1)` modulo `(ζ - 1) ^ 2` for some integers `a` and `b`. When `p` is prime, `ζ - 1`
generates the prime above `p`, and `a`, `b` are the first two `(ζ - 1)`-adic digits. -/
theorem exists_toInteger_sub_one_sq_dvd_sub_intCast_add_intCast_mul [NeZero p] (x : 𝓞 K) :
    ∃ a b : ℤ, (hζ.toInteger - 1) ^ 2 ∣ x - (a + b * (hζ.toInteger - 1)) := by
  have hgen : hζ.subOneIntegralPowerBasis.gen = hζ.toInteger - 1 := by
    ext
    simp only [subOneIntegralPowerBasis_gen, RingOfIntegers.map_mk, map_sub, map_one,
      sub_left_inj]
    -- `algebraMap (𝓞 K) K` is the coercion `𝓞 K → K`
    exact hζ.coe_toInteger.symm
  obtain ⟨f, rfl⟩ := hζ.subOneIntegralPowerBasis.exists_eq_aeval' x
  obtain ⟨g, hg⟩ := Polynomial.X_dvd_sub_C (p := f)
  obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := g)
  refine ⟨f.coeff 0, g.coeff 0, Polynomial.aeval (hζ.toInteger - 1) h, ?_⟩
  -- Peel off the constant term twice: `f = a + X * (b + X * h)`.
  generalize f.coeff 0 = a at hg ⊢
  generalize g.coeff 0 = b at hh ⊢
  obtain rfl : f = Polynomial.C a + Polynomial.X * (Polynomial.C b + Polynomial.X * h) := by
    linear_combination hg + Polynomial.X * hh
  rw [hgen]
  simp only [map_add, map_mul, map_intCast, Polynomial.aeval_X, eq_intCast]
  ring

include hζ in
/-- For an odd prime `p`, an integer is divisible by `(ζ - 1) ^ 2` in `ℤ[ζ_p]` if and only if it
is divisible by `p`. -/
theorem toInteger_sub_one_sq_dvd_intCast_iff (hp2 : p ≠ 2) {n : ℤ} :
    (hζ.toInteger - 1) ^ 2 ∣ (n : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  refine ⟨fun h ↦ (zeta_sub_one_dvd_intCast_iff' p hζ).1 ((dvd_pow_self _ two_ne_zero).trans h),
    ?_⟩
  rintro ⟨k, rfl⟩
  have h2 : 2 ≤ p - 1 := by
    have := hp.out.two_le
    omega
  calc (hζ.toInteger - 1) ^ 2 ∣ (hζ.toInteger - 1) ^ (p - 1) := pow_dvd_pow _ h2
    _ ∣ (p : 𝓞 K) := (associated_zeta_sub_one_pow_prime p hζ).dvd
    _ ∣ ((p * k : ℤ) : 𝓞 K) := by
      push_cast
      exact dvd_mul_right _ _

include hζ in
/-- For an odd prime `p` and integers `m` and `e`, `(ζ - 1) ^ 2` divides `m + e (ζ - 1)` in
`ℤ[ζ_p]` if and only if `p` divides both `m` and `e`. In particular, the coordinates of
`exists_toInteger_sub_one_sq_dvd_sub_intCast_add_intCast_mul` are unique modulo `p`. -/
theorem toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff (hp2 : p ≠ 2) {m e : ℤ} :
    (hζ.toInteger - 1) ^ 2 ∣ (m : 𝓞 K) + e * (hζ.toInteger - 1) ↔ (p : ℤ) ∣ m ∧ (p : ℤ) ∣ e := by
  have hl1 : hζ.toInteger - 1 ∣ (hζ.toInteger - 1) ^ 2 := dvd_pow_self _ two_ne_zero
  constructor
  · intro h
    have hm : (p : ℤ) ∣ m := by
      rw [← zeta_sub_one_dvd_intCast_iff' p hζ]
      exact (dvd_add_left (dvd_mul_left _ _)).1 (hl1.trans h)
    refine ⟨hm, ?_⟩
    have he : (hζ.toInteger - 1) * (hζ.toInteger - 1) ∣ (hζ.toInteger - 1) * e := by
      rw [← sq, mul_comm]
      exact (dvd_add_right ((hζ.toInteger_sub_one_sq_dvd_intCast_iff hp2).2 hm)).1 h
    rw [← zeta_sub_one_dvd_intCast_iff' p hζ]
    exact (mul_dvd_mul_iff_left hζ.zeta_sub_one_prime'.ne_zero).1 he
  · rintro ⟨hm, he⟩
    refine dvd_add ((hζ.toInteger_sub_one_sq_dvd_intCast_iff hp2).2 hm) ?_
    rw [sq]
    exact mul_dvd_mul_right ((zeta_sub_one_dvd_intCast_iff' p hζ).2 he) _

include hζ in
/-- In `ℤ[ζ_p]`, an element is coprime to the prime `ζ - 1` if and only if `ζ - 1` does not
divide it. -/
theorem isCoprime_toInteger_sub_one_iff {x : 𝓞 K} :
    IsCoprime x (hζ.toInteger - 1) ↔ ¬ hζ.toInteger - 1 ∣ x := by
  refine ⟨fun h hx ↦ hζ.zeta_sub_one_prime'.not_isUnit (h.isUnit_of_dvd' hx dvd_rfl), fun h ↦ ?_⟩
  exact (isCoprime_of_not_zeta_sub_one_dvd p hζ h).symm.of_isCoprime_of_dvd_right
    hζ.toInteger_sub_one_dvd_prime'

include hζ in
/-- In `ℤ[ζ_p]`, an element is coprime to `ζ - 1` if and only if it is coprime to `p`. -/
theorem isCoprime_toInteger_sub_one_iff_isCoprime_natCast {x : 𝓞 K} :
    IsCoprime x (hζ.toInteger - 1) ↔ IsCoprime x (p : 𝓞 K) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_isCoprime_of_dvd_right hζ.toInteger_sub_one_dvd_prime'⟩
  exact (isCoprime_of_not_zeta_sub_one_dvd p hζ (hζ.isCoprime_toInteger_sub_one_iff.1 h)).symm

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Being primary does not depend on the choice of the primitive `p`-th root of unity. -/
theorem isEisensteinPrimary_toInteger_iff [NeZero p] {η : K} (hη : IsPrimitiveRoot η p)
    {x : 𝓞 K} :
    IsEisensteinPrimary hζ.toInteger x ↔ IsEisensteinPrimary hη.toInteger x := by
  obtain ⟨u, hu⟩ : Associated (hζ.toInteger - 1) (hη.toInteger - 1) :=
    associated_sub_one_of_isPrimitiveRoot p hζ hη
  rw [isEisensteinPrimary_iff, isEisensteinPrimary_iff, ← hu,
    isCoprime_mul_unit_right_right u.isUnit, mul_pow, ← Units.val_pow_eq_pow_val]
  simp only [Units.mul_right_dvd]

include hζ in
/-- In `ℤ[ζ_p]`, a rational integer is primary if and only if it is prime to `p`. -/
@[simp]
theorem isEisensteinPrimary_intCast_iff {a : ℤ} :
    IsEisensteinPrimary hζ.toInteger (a : 𝓞 K) ↔ ¬ (p : ℤ) ∣ a := by
  rw [isEisensteinPrimary_iff, isCoprime_toInteger_sub_one_iff hζ,
    zeta_sub_one_dvd_intCast_iff' p hζ]
  exact and_iff_left ⟨a, by simp⟩

include hζ in
/-- In `ℤ[ζ_p]`, a natural number is primary if and only if it is prime to `p`. -/
@[simp]
theorem isEisensteinPrimary_natCast_iff {n : ℕ} :
    IsEisensteinPrimary hζ.toInteger (n : 𝓞 K) ↔ ¬ p ∣ n := by
  rw [← Int.cast_natCast, hζ.isEisensteinPrimary_intCast_iff, Int.natCast_dvd_natCast]

include hζ in
/-- In `ℤ[ζ_p]`, a numeral is primary if and only if it is prime to `p`. -/
@[simp]
theorem isEisensteinPrimary_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    IsEisensteinPrimary hζ.toInteger (ofNat(n) : 𝓞 K) ↔ ¬ p ∣ ofNat(n) :=
  hζ.isEisensteinPrimary_natCast_iff

include hζ in
/-- For an odd prime `p`, the root of unity `ζ` is not primary in `ℤ[ζ_p]`. -/
theorem not_isEisensteinPrimary_toInteger (hp2 : p ≠ 2) :
    ¬ IsEisensteinPrimary hζ.toInteger hζ.toInteger := by
  rintro ⟨-, a, ha⟩
  have h : hζ.toInteger - (a : 𝓞 K) =
      ((1 - a : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * (hζ.toInteger - 1) := by
    push_cast
    ring
  rw [h, hζ.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff hp2] at ha
  exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) ha.2)

include hζ in
/-- The prime `1 - ζ` above `p` is not primary in `ℤ[ζ_p]`. -/
theorem not_isEisensteinPrimary_one_sub_toInteger :
    ¬ IsEisensteinPrimary hζ.toInteger (1 - hζ.toInteger) := by
  rintro ⟨h, -⟩
  exact hζ.isCoprime_toInteger_sub_one_iff.1 h ⟨-1, by ring⟩

include hζ in
/-- **The primary multiples of an element of `ℤ[ζ_p]`.** Let `p` be an odd prime and `x` an
element of `ℤ[ζ_p]` prime to `ζ - 1`, with `x ≡ a + b (ζ - 1)` modulo `(ζ - 1) ^ 2`. Then
`ζ ^ c * x` is primary if and only if `p ∣ b + c a`. -/
theorem isEisensteinPrimary_toInteger_pow_mul_iff (hp2 : p ≠ 2) {x : 𝓞 K}
    (hx : ¬ hζ.toInteger - 1 ∣ x) {a b : ℤ}
    (hab : (hζ.toInteger - 1) ^ 2 ∣ x - (a + b * (hζ.toInteger - 1))) (c : ℕ) :
    IsEisensteinPrimary hζ.toInteger (hζ.toInteger ^ c * x) ↔ (p : ℤ) ∣ b + c * a := by
  set l := hζ.toInteger - 1 with hl
  -- `ζ ^ c ≡ 1 + c (ζ - 1)`, so `ζ ^ c * x ≡ a + (b + c a) (ζ - 1)` modulo `(ζ - 1) ^ 2`.
  have hc : l ^ 2 ∣ hζ.toInteger ^ c - (1 + c * l) := by
    convert sq_dvd_add_pow_sub_sub l 1 c using 1
    simp only [hl, add_sub_cancel, one_pow]
    ring
  have key : l ^ 2 ∣ hζ.toInteger ^ c * x - (a + ((b + c * a : ℤ) : 𝓞 K) * l) := by
    obtain ⟨s, hs⟩ := hc
    obtain ⟨t, ht⟩ := hab
    refine ⟨s * x + (1 + c * l) * t + c * b, ?_⟩
    push_cast
    linear_combination x * hs + (1 + c * l) * ht
  have hunit : IsUnit (hζ.toInteger ^ c) :=
    (hζ.toInteger_isPrimitiveRoot.isUnit hp.out.ne_zero).pow c
  constructor
  · rintro ⟨-, m, hm⟩
    have h : l ^ 2 ∣ ((a - m : ℤ) : 𝓞 K) + ((b + c * a : ℤ) : 𝓞 K) * l := by
      have h := dvd_sub hm key
      rw [sub_sub_sub_cancel_left] at h
      convert h using 1
      push_cast
      ring
    exact ((hζ.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff hp2).1 h).2
  · intro h
    refine ⟨(isCoprime_mul_unit_left_left hunit _ _).2
      (hζ.isCoprime_toInteger_sub_one_iff.2 hx), a, ?_⟩
    have h' : l ^ 2 ∣ ((0 : ℤ) : 𝓞 K) + ((b + c * a : ℤ) : 𝓞 K) * l :=
      (hζ.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff hp2).2 ⟨dvd_zero _, h⟩
    convert dvd_add key h' using 1
    push_cast
    ring

include hζ in
/-- **The unique primary multiple by a power of `ζ`.** Let `p` be an odd prime. For every element
`x` of `ℤ[ζ_p]` prime to `ζ - 1` there is exactly one `c ∈ ℤ/p` such that `ζ ^ c * x` is
primary. -/
theorem existsUnique_isEisensteinPrimary_toInteger_pow_mul (hp2 : p ≠ 2) {x : 𝓞 K}
    (hx : ¬ hζ.toInteger - 1 ∣ x) :
    ∃! c : ZMod p, IsEisensteinPrimary hζ.toInteger (hζ.toInteger ^ c.val * x) := by
  obtain ⟨a, b, hab⟩ := hζ.exists_toInteger_sub_one_sq_dvd_sub_intCast_add_intCast_mul x
  have ha : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, ← zeta_sub_one_dvd_intCast_iff' p hζ]
    refine fun h ↦ hx ?_
    have h' := (dvd_pow_self _ two_ne_zero).trans hab
    convert dvd_add (dvd_add h' h) (dvd_mul_left (hζ.toInteger - 1) (b : 𝓞 K)) using 1
    ring
  simp_rw [hζ.isEisensteinPrimary_toInteger_pow_mul_iff hp2 hx hab,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  refine ⟨-b / a, by field_simp; ring, fun c hc ↦ ?_⟩
  field_simp
  linear_combination hc

end IsPrimitiveRoot
