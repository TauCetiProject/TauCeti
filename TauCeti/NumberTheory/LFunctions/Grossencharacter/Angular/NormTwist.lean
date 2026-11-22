/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Angular.Basic
import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Splitting

/-!
# Evaluation at `(2 + i)` and absence of pure norm twists for Hecke's angular characters

For a fourth cyclotomic extension `F` of `ℚ` with primitive fourth root of unity `ζ ∈ F`, the
principal ideal `(2 + ζ)` of `𝓞 F ≅ ℤ[i]` is a split Gaussian prime of absolute norm `5`. At this
ideal, Hecke's angular Größencharakter `angularGrossencharacter F k` takes the value
`((3 ± 4i) / 5) ^ (2 * k)`, whose imaginary part is nonzero whenever `k ≠ 0` because every positive
power of `3 + 4i` is congruent to `3 + 4i` modulo `5`.

This explicit nonreal value has two consequences:

* By Hecke's unit relation (`Grossencharacter.compatibility_inv`), the ideal value at `(2 + ζ)`
  equals the **inverse** of the archimedean monomial `∏ τ, τ(2 + ζ) ^ n_τ`, and for `k ≠ 0` is
  strictly distinct from the uninverted monomial because its square `((3 ± 4i) / 5) ^ (4 * k)` is
  not `1`.
* For `k ≠ 0`, the unitary ideal weight of `angularGrossencharacter F k` is not an imaginary norm
  twist `N(I) ^ (u * i)` on its good ideals: the conjugate ideals `(2 + ζ)` and `(2 - ζ)` share
  absolute norm `5` and multiply to `(5)`, on which the angular weight is `1`, whereas the square of
  the weight at `(2 + ζ)` is nonreal.

## Main results

* `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger`: explicit value
  `((3 + 4i) / 5) ^ (± 2 * k)` at `(2 + hζ.toInteger)`.
* `TauCeti.LFunctions.im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero`: for
  `k ≠ 0`, the ideal value at `(2 + hζ.toInteger)` has nonzero imaginary part.
* `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger_eq_inv_prod`,
  `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_prod`: positive and
  negative halves of Hecke's unit-relation sign check at `2 + ζ`.
* `TauCeti.LFunctions.angularGrossencharacter_not_isNormTwist`: for `k ≠ 0`, the unitary ideal
  weight of `angularGrossencharacter F k` is not an imaginary norm twist on good ideals.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen*,
  Math. Z. **1** (1918), 357–376, and **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section
noncomputable section

open NumberField
open scoped NumberField

namespace TauCeti.LFunctions

open GlobalNumberFields

private theorem norm_two_add_toInteger_of_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) :
    Algebra.norm ℤ ((2 : 𝓞 F) + hζ.toInteger) = 5 := by
  simpa using hζ.norm_intCast_add_intCast_mul_toInteger_of_four 2 1

private theorem two_add_toInteger_ne_zero_of_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) :
    (2 : 𝓞 F) + hζ.toInteger ≠ 0 := by
  intro h0
  have hnorm := norm_two_add_toInteger_of_four hζ
  rw [h0, Algebra.norm_zero] at hnorm
  omega

private theorem unitaryWeight_angularGrossencharacter_apply_sq {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (I : Ideal (𝓞 F)) :
    ((angularGrossencharacter F k).unitaryWeight.val I) ^ 2 =
      (angularGrossencharacter F (2 * k)).unitaryWeight.val I := by
  have hp := congrArg (fun w : UnitaryIdealWeight F ↦ w.val I)
    (unitaryWeight_angularGrossencharacter_pow F k 2)
  rw [UnitaryIdealWeight.val_pow, MultiplicativeIdealWeight.pow_apply _ (by decide)] at hp
  simpa only [Nat.cast_ofNat] using hp

/-- **Value of `angularGrossencharacter F k` at `(2 + i)`**: for a primitive fourth root of unity
`ζ ∈ F`, the unitary weight at `Ideal.span {2 + hζ.toInteger}` is `((3 + 4i) / 5) ^ (2 * k)` or
`((3 + 4i) / 5) ^ (-(2 * k))` according to which square root of `-1` the chosen embedding
selects. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
        (((3 : ℂ) + 4 * Complex.I) / 5) ^ (2 * k) ∨
      (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
        (((3 : ℂ) + 4 * Complex.I) / 5) ^ (-(2 * k)) := by
  let w : {w : InfinitePlace F // w.IsComplex} :=
    ⟨Classical.arbitrary (InfinitePlace F),
      (IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)).isComplex _⟩
  rw [unitaryWeight_angularGrossencharacter_span_singleton k w
    (two_add_toInteger_ne_zero_of_four hζ)]
  set τ := w.val.embedding
  have h2I : (2 + Complex.I) / (2 - Complex.I) = ((3 : ℂ) + 4 * Complex.I) / 5 := by
    have hne : (2 : ℂ) - Complex.I ≠ 0 := fun h ↦ by simpa using congrArg Complex.im h
    rw [div_eq_div_iff hne (by norm_num)]
    linear_combination 4 * Complex.I_sq
  have hτI : τ (hζ.toInteger : F) = Complex.I ∨ τ (hζ.toInteger : F) = -Complex.I := by
    have hz : algebraMap (𝓞 F) F hζ.toInteger = ζ := hζ.coe_toInteger
    have hsq : (τ (hζ.toInteger : F)) ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq, RingOfIntegers.coe_eq_algebraMap, hz, ← map_pow,
        hζ.sq_eq_neg_one, map_neg, map_one]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hτα_sum : τ (((2 : 𝓞 F) + hζ.toInteger : 𝓞 F) : F) = 2 + τ (hζ.toInteger : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_ofNat]
  rcases hτI with hI | hnegI
  · left
    have hconj : starRingEnd ℂ (2 + Complex.I) = 2 - Complex.I := by
      simp [map_ofNat, sub_eq_add_neg]
    rw [hτα_sum, hI, hconj, h2I]
  · right
    have hconj : starRingEnd ℂ (2 - Complex.I) = 2 + Complex.I := by
      simp [map_ofNat]
    have h2I_inv : (2 - Complex.I) / (2 + Complex.I) = (((3 : ℂ) + 4 * Complex.I) / 5)⁻¹ := by
      rw [← h2I, inv_div]
    rw [hτα_sum, hnegI, ← sub_eq_add_neg, hconj, h2I_inv, inv_zpow, ← zpow_neg]

/-- **Nonreal value at `(2 + i)`**: for `k ≠ 0`, `angularGrossencharacter F k` takes a nonreal
value at `(2 + hζ.toInteger)`. -/
theorem im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4)
    {k : ℤ} (hk : k ≠ 0) :
    ((angularGrossencharacter F k).unitaryWeight.val
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger})).im ≠ 0 := by
  rcases unitaryWeight_angularGrossencharacter_two_add_toInteger hζ k with h | h <;> rw [h]
  · exact TauCeti.NumberField.GaussianRationals.im_three_add_four_I_div_five_zpow_ne_zero
      (mul_ne_zero two_ne_zero hk)
  · exact TauCeti.NumberField.GaussianRationals.im_three_add_four_I_div_five_zpow_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hk))

private theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_sq_ne_one {F : Type*}
    [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 4) {k : ℤ} (hk : k ≠ 0) :
    ((angularGrossencharacter F k).unitaryWeight.val
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger})) ^ 2 ≠ 1 := by
  intro hsq1
  have him2 : (((angularGrossencharacter F k).unitaryWeight.val
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger})) ^ 2).im ≠ 0 := by
    rw [unitaryWeight_angularGrossencharacter_apply_sq]
    exact im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero hζ
      (mul_ne_zero two_ne_zero hk)
  exact him2 (by rw [hsq1, Complex.one_im])

/-- **Sign check at `2 + i` (positive half)**: by Hecke's unit relation, the ideal value of
`angularGrossencharacter F k` at `(2 + ζ)` equals the **inverse** of the archimedean monomial
`∏ τ, τ(2 + ζ) ^ n_τ`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_eq_inv_prod {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
      (∏ τ : F →+* ℂ, τ (2 + ζ) ^ (angularGrossencharacter F k).infinityType τ)⁻¹ := by
  set α : 𝓞 F := (2 : 𝓞 F) + hζ.toInteger
  have hαF : (algebraMap (𝓞 F) F α) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr
      (two_add_toInteger_ne_zero_of_four hζ)
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F α) hαF
  have hcompat := (angularGrossencharacter F k).compatibility_inv x (isCongrOne_one x) α rfl
  have hxval : (x : F) = 2 + ζ := by
    simp [x, α, map_ofNat, hζ.coe_toInteger]
  simpa [idealShift_angularGrossencharacter, hxval] using hcompat

/-- **Sign check at `2 + i` (negative half)**: for `k ≠ 0`, the ideal value of
`angularGrossencharacter F k` at `(2 + ζ)` is **not** equal to the uninverted archimedean monomial
`∏ τ, τ(2 + ζ) ^ n_τ`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_prod {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4)
    {k : ℤ} (hk : k ≠ 0) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) ≠
      ∏ τ : F →+* ℂ, τ (2 + ζ) ^ (angularGrossencharacter F k).infinityType τ := by
  intro heq
  have hinv := unitaryWeight_angularGrossencharacter_two_add_toInteger_eq_inv_prod hζ k
  set wval :=
    (angularGrossencharacter F k).unitaryWeight.val
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) with hwval
  have hw0 : wval ≠ 0 := fun h0 ↦
    im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero hζ hk
      (by simpa [hwval] using congrArg Complex.im h0)
  have hsq1 : wval ^ 2 = 1 := by
    rw [sq, ← mul_inv_cancel₀ hw0]
    exact congrArg (wval * ·) (hinv.trans (congrArg Inv.inv heq.symm))
  exact unitaryWeight_angularGrossencharacter_two_add_toInteger_sq_ne_one hζ hk hsq1

/-- **For `k ≠ 0`, `angularGrossencharacter F k` is not an imaginary norm twist on good ideals.**
The conjugate Gaussian primes `(2 + i)` and `(2 - i)` both have absolute norm `5` and multiply to
`(5)`, on which the angular weight is `1`; a norm twist `N(I) ^ (u * i)` would assign them the same
value `w`, forcing `w ^ 2 = 1`, whereas `w ^ 2 = ((3 ± 4i) / 5) ^ (4 * k)` is nonreal. -/
theorem angularGrossencharacter_not_isNormTwist
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {k : ℤ} (hk : k ≠ 0)
    (u : ℝ) :
    ¬ TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood
      (angularGrossencharacter F k).unitaryWeight.val u := by
  intro htwist
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  let w : {w : InfinitePlace F // w.IsComplex} :=
    ⟨Classical.arbitrary (InfinitePlace F),
      (IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)).isComplex _⟩
  set α : 𝓞 F := (2 : 𝓞 F) + hζ.toInteger
  set β : 𝓞 F := (2 : 𝓞 F) - hζ.toInteger
  have hNα : Ideal.absNorm (Ideal.span {α}) = 5 := by
    exact_mod_cast (RingOfIntegers.natCast_absNorm_span_singleton_of_four α).trans
      (norm_two_add_toInteger_of_four hζ)
  have hNβ : Ideal.absNorm (Ideal.span {β}) = 5 := by
    have hβ' : β = (2 : ℤ) + (-1 : ℤ) * hζ.toInteger := by simp [β, sub_eq_add_neg]
    have hn : Algebra.norm ℤ β = 5 := by
      rw [hβ', hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; norm_num
    exact_mod_cast (RingOfIntegers.natCast_absNorm_span_singleton_of_four β).trans hn
  have hnormTwist := htwist.eq_normTwist (badPrimes_unitaryWeight_angularGrossencharacter F k)
  have hαprime : Ideal.IsPrimeTo (Ideal.span {α}) ∅ :=
    Ideal.isPrimeTo_empty.mpr (Ideal.absNorm_eq_zero_iff.not.mp (by omega))
  have hβprime : Ideal.IsPrimeTo (Ideal.span {β}) ∅ :=
    Ideal.isPrimeTo_empty.mpr (Ideal.absNorm_eq_zero_iff.not.mp (by omega))
  have heqαβ : (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α}) =
      (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {β}) := by
    rw [DFunLike.congr_fun hnormTwist (Ideal.span {α}),
      DFunLike.congr_fun hnormTwist (Ideal.span {β}),
      MultiplicativeIdealWeight.normTwist_apply, MultiplicativeIdealWeight.normTwist_apply,
      MultiplicativeIdealWeight.ofBadPrimes_apply, MultiplicativeIdealWeight.ofBadPrimes_apply,
      hNα, hNβ]
    simp [hαprime, hβprime]
  have hmul5 : α * β = (5 : 𝓞 F) := by
    simp only [α, β]; linear_combination -hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hval5 : (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(5 : 𝓞 F)}) = 1 := by
    rw [unitaryWeight_angularGrossencharacter_span_singleton k w (by norm_num)]
    simp [map_ofNat]
  have hsq1 : ((angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α})) ^ 2 = 1 := by
    rw [sq, ← hval5, ← hmul5, ← Ideal.span_singleton_mul_span_singleton, map_mul, heqαβ]
  exact unitaryWeight_angularGrossencharacter_two_add_toInteger_sq_ne_one hζ hk hsq1

end TauCeti.LFunctions
