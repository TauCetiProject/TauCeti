/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Angular.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Splitting
import TauCeti.RingTheory.RootsOfUnity.Complex

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

* `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_I`,
  `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_neg_I`
  and `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger`: explicit value
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

open GlobalNumberFields TauCeti.NumberField

private theorem unitaryWeight_angularGrossencharacter_apply_sq {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (I : Ideal (𝓞 F)) :
    ((angularGrossencharacter F k).unitaryWeight.val I) ^ 2 =
      (angularGrossencharacter F (2 * k)).unitaryWeight.val I := by
  have hp := congrArg (fun w : UnitaryIdealWeight F ↦ w.val I)
    (unitaryWeight_angularGrossencharacter_pow F k 2)
  rw [UnitaryIdealWeight.val_pow, MultiplicativeIdealWeight.pow_apply _ (by decide)] at hp
  simpa only [Nat.cast_ofNat] using hp

/-- **Value of `angularGrossencharacter F k` at `(2 + i)` when `w.val.embedding ζ = i`**:
for a primitive fourth root of unity `ζ ∈ F` sent to `Complex.I` by `w.val.embedding`, the
unitary weight at `Ideal.span {2 + hζ.toInteger}` equals `((3 + 4i) / 5) ^ (2 * k)`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_I {F : Type*}
    [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) {w : {w : InfinitePlace F // w.IsComplex}}
    (hτ : w.val.embedding ζ = Complex.I) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
      (((3 : ℂ) + 4 * Complex.I) / 5) ^ (2 * k) := by
  rw [unitaryWeight_angularGrossencharacter_span_singleton k w
    (GaussianRationals.two_add_ne_zero hζ.minpoly_toInteger_eq_X_sq_add_one)]
  have hτα : w.val.embedding (((2 : 𝓞 F) + hζ.toInteger : 𝓞 F) : F) = 2 + Complex.I := by
    simp [RingOfIntegers.coe_eq_algebraMap, map_ofNat, hζ.coe_toInteger, hτ]
  have hconj : starRingEnd ℂ (2 + Complex.I) = 2 - Complex.I := by
    simp [map_ofNat, sub_eq_add_neg]
  rw [hτα, hconj, Complex.two_add_I_div_two_sub_I]

/-- **Value of `angularGrossencharacter F k` at `(2 + i)` when `w.val.embedding ζ = -i`**:
for a primitive fourth root of unity `ζ ∈ F` sent to `-Complex.I` by `w.val.embedding`, the
unitary weight at `Ideal.span {2 + hζ.toInteger}` equals `((3 + 4i) / 5) ^ (-(2 * k))`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_neg_I {F : Type*}
    [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) {w : {w : InfinitePlace F // w.IsComplex}}
    (hτ : w.val.embedding ζ = -Complex.I) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
      (((3 : ℂ) + 4 * Complex.I) / 5) ^ (-(2 * k)) := by
  rw [unitaryWeight_angularGrossencharacter_span_singleton k w
    (GaussianRationals.two_add_ne_zero hζ.minpoly_toInteger_eq_X_sq_add_one)]
  have hτα : w.val.embedding (((2 : 𝓞 F) + hζ.toInteger : 𝓞 F) : F) = 2 - Complex.I := by
    simp [RingOfIntegers.coe_eq_algebraMap, map_ofNat, hζ.coe_toInteger, hτ, sub_eq_add_neg]
  have hconj : starRingEnd ℂ (2 - Complex.I) = 2 + Complex.I := by
    simp [map_ofNat]
  have h2I_inv : (2 - Complex.I) / (2 + Complex.I) = (((3 : ℂ) + 4 * Complex.I) / 5)⁻¹ := by
    rw [← Complex.two_add_I_div_two_sub_I, inv_div]
  rw [hτα, hconj, h2I_inv, inv_zpow, ← zpow_neg]

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
  let w := complexPlaceFour F
  rcases Complex.isPrimitiveRoot_four_iff.mp (hζ.map_of_injective w.val.embedding.injective) with
    hI | hnegI
  · exact Or.inl
      (unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_I hζ k hI)
  · exact Or.inr
      (unitaryWeight_angularGrossencharacter_two_add_toInteger_of_embedding_eq_neg_I hζ k hnegI)

/-- **Nonreal value at `(2 + i)`**: for `k ≠ 0`, `angularGrossencharacter F k` takes a nonreal
value at `(2 + hζ.toInteger)`. -/
theorem im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4)
    {k : ℤ} (hk : k ≠ 0) :
    ((angularGrossencharacter F k).unitaryWeight.val
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger})).im ≠ 0 := by
  rcases unitaryWeight_angularGrossencharacter_two_add_toInteger hζ k with h | h <;> rw [h]
  · exact Complex.im_three_add_four_I_div_five_zpow_ne_zero (mul_ne_zero two_ne_zero hk)
  · exact Complex.im_three_add_four_I_div_five_zpow_ne_zero
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
  rw [unitaryWeight_angularGrossencharacter_span_singleton_eq_inv_prod k
    (GaussianRationals.two_add_ne_zero hζ.minpoly_toInteger_eq_X_sq_add_one)]
  simp [hζ.coe_toInteger, map_ofNat]

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
  set α : 𝓞 F := (2 : 𝓞 F) + hζ.toInteger
  set β : 𝓞 F := (2 : 𝓞 F) - hζ.toInteger
  have hNα : Ideal.absNorm (Ideal.span {α}) = 5 :=
    GaussianRationals.absNorm_span_two_add hζ.minpoly_toInteger_eq_X_sq_add_one
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
  have hNβ : Ideal.absNorm (Ideal.span {β}) = 5 :=
    GaussianRationals.absNorm_span_two_sub hζ.minpoly_toInteger_eq_X_sq_add_one
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
  have hgood {I : Ideal (𝓞 F)} (hI : Ideal.absNorm I ≠ 0) :
      (angularGrossencharacter F k).unitaryWeight.val.IsGood I :=
    (Grossencharacter.isGood_unitaryWeight_modulus_one_iff _ _).mpr
      (Ideal.absNorm_eq_zero_iff.not.mp hI)
  have heqαβ : (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α}) =
      (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {β}) :=
    htwist.eq_of_absNorm_eq (hgood (by omega)) (hgood (by omega)) (hNα.trans hNβ.symm)
  have hmul5 : α * β = (5 : 𝓞 F) :=
    GaussianRationals.two_add_mul_two_sub_eq_five hζ.minpoly_toInteger_eq_X_sq_add_one
  have hval5 : (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {(5 : 𝓞 F)}) = 1 := by
    rw [unitaryWeight_angularGrossencharacter_span_singleton k (complexPlaceFour F) (by norm_num)]
    simp [map_ofNat]
  have hsq1 : ((angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α})) ^ 2 = 1 := by
    rw [sq, ← hval5, ← hmul5, ← Ideal.span_singleton_mul_span_singleton, map_mul, heqαβ]
  exact unitaryWeight_angularGrossencharacter_two_add_toInteger_sq_ne_one hζ hk hsq1

end TauCeti.LFunctions
