/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Orders.IntAddMulOrder
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor
public import TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

/-!
# The order of conductor `f` in a quadratic field

In a quadratic number field `K` with discriminant `D`, the order `O_f = ℤ + f 𝓞 K` has index `f`,
conductor `f 𝓞 K` and discriminant `f² D`, and every order of `K` is `O_f` for exactly one `f ≥ 1`,
namely its index. In particular an order of `K` is determined by its conductor.

Since the residue ring of `O_f` modulo its conductor is `ℤ / f`, the class number formula for
orders becomes

```text
#Pic O_f · [(𝓞 K)ˣ : O_fˣ] · φ(f) = h_K · #(𝓞 K ⧸ f 𝓞 K)ˣ.
```

Counting the residue units `(𝓞 K ⧸ f 𝓞 K)ˣ` through the splitting of the primes dividing `f`
(`TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod`) turns this identity into the
classical formula

```text
h(O_f) = h_K f / [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} (1 - χ_D(p) / p)
```

(Cox, Theorem 7.24), where `χ_D = TauCeti.Multiquadratic.fundamentalDiscriminantChar D` is the
quadratic character of `K`, with `χ_D(p) = 0` at the ramified primes.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.conductor_intAddMulOrder`: the conductor of
  `O_f` is `f 𝓞 K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.discr_intAddMulOrder_of_finrank_eq_two`: the
  discriminant of `O_f` is `f² D`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.eq_intAddMulOrder_iff`: an order is `O_f` exactly
  when its index is `f`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.conductor_injective`: an order of a quadratic field
  is determined by its conductor.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_intAddMulOrder_mul_index_mul_totient`:
  the class number formula for `O_f` in terms of the residue units modulo `f`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_intAddMulOrder_mul_index_mul_prod` and
  `TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_intAddMulOrder_eq`: the class number of
  `O_f` in terms of `h_K`, `f`, the unit index and `χ_D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Lemma 7.2 and Theorem 7.24.
-/

public section
noncomputable section

open NumberField
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr)

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

/-- The conductor of the order `ℤ + f 𝓞 K` of a quadratic field is `f 𝓞 K`. -/
theorem conductor_intAddMulOrder (hK : Module.finrank ℚ K = 2) (f : ℕ) [NeZero f] :
    (intAddMulOrder K f).conductor = Ideal.span {(f : 𝓞 K)} := by
  rw [conductor_eq_span_index _ hK, index_intAddMulOrder, hK, pow_one]

/-- The order `ℤ + f 𝓞 K` of a quadratic field of discriminant `D` has discriminant `f² D`. -/
theorem discr_intAddMulOrder_of_finrank_eq_two (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] : (intAddMulOrder K f).discr = (f : ℤ) ^ 2 * NumberField.discr K := by
  rw [discr_intAddMulOrder, hK]

/-- **Every order of a quadratic field is `ℤ + f 𝓞 K`**, with `f` its index. -/
theorem eq_intAddMulOrder_index (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    O = intAddMulOrder K O.index := by
  refine toRingOfIntegers_injective (Subalgebra.ext fun x ↦ ?_)
  rw [O.mem_toRingOfIntegers_iff_exists_int_add_index_mul hK, mem_toRingOfIntegers_intAddMulOrder]

/-- **The order of conductor `f` is unique.** An order of a quadratic field is `ℤ + f 𝓞 K`
exactly when its index is `f`. -/
theorem eq_intAddMulOrder_iff (hK : Module.finrank ℚ K = 2) {O : NumberFieldOrder K} {f : ℕ}
    [NeZero f] : O = intAddMulOrder K f ↔ O.index = f := by
  constructor
  · rintro rfl
    rw [index_intAddMulOrder, hK, pow_one]
  · rintro rfl
    exact eq_intAddMulOrder_index hK O

/-- **An order of a quadratic field is determined by its conductor.** -/
theorem conductor_injective (hK : Module.finrank ℚ K = 2) :
    Function.Injective (conductor : NumberFieldOrder K → Ideal (𝓞 K)) := by
  intro O O' h
  rw [conductor_eq_span_index _ hK, conductor_eq_span_index _ hK,
    Ideal.span_singleton_eq_span_singleton] at h
  have hindex : O.index = O'.index := Nat.dvd_antisymm
    (RingOfIntegers.natCast_dvd_natCast.mp h.dvd)
    (RingOfIntegers.natCast_dvd_natCast.mp h.symm.dvd)
  exact ((eq_intAddMulOrder_iff hK).mpr hindex).trans (eq_intAddMulOrder_index hK O').symm

/-- The residue ring of `ℤ + f 𝓞 K` modulo its conductor has `φ(f)` units. -/
theorem card_units_quotient_conductor_intAddMulOrder (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    Nat.card ((intAddMulOrder K f).toRingOfIntegers ⧸ (intAddMulOrder K f).conductor.comap
      ((intAddMulOrder K f).toRingOfIntegers.val :
        (intAddMulOrder K f).toRingOfIntegers →+* 𝓞 K))ˣ = f.totient := by
  rw [conductor_intAddMulOrder hK, card_units_quotientIntAddMulOrder]

/-- **The class number formula for the order of conductor `f`.** For the order `O_f = ℤ + f 𝓞 K`
of a quadratic field,

`#Pic O_f · [(𝓞 K)ˣ : O_fˣ] · φ(f) = h_K · #(𝓞 K ⧸ f 𝓞 K)ˣ`,

where `O_fˣ` is the image of the units of `O_f` in `(𝓞 K)ˣ`. -/
theorem card_pic_intAddMulOrder_mul_index_mul_totient (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    Nat.card (Pic (intAddMulOrder K f)) *
        (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
          (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index * f.totient =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ Ideal.span {(f : 𝓞 K)})ˣ := by
  have h := (intAddMulOrder K f).card_pic_mul_index_mul_card_units
  rwa [card_units_quotient_conductor_intAddMulOrder hK, conductor_intAddMulOrder hK] at h

/-- **The class number of the order of conductor `f`**, without denominators. For the order
`O_f = ℤ + f 𝓞 K` of a quadratic field `K` with discriminant `D`,

`#Pic O_f · [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} p = h_K · f · ∏_{p ∣ f} (p - χ_D(p))`. -/
theorem card_pic_intAddMulOrder_mul_index_mul_prod (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    (Nat.card (Pic (intAddMulOrder K f)) : ℤ) *
        (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
          (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index *
        ∏ p ∈ f.primeFactors, (p : ℤ) =
      Nat.card (ClassGroup (𝓞 K)) * f * ∏ p ∈ f.primeFactors,
        ((p : ℤ) - fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK)
          p) := by
  have hf : f ≠ 0 := NeZero.ne f
  have hA := congrArg (Nat.cast : ℕ → ℤ) (card_pic_intAddMulOrder_mul_index_mul_totient hK f)
  push_cast at hA
  have hT : (f.totient : ℤ) * ∏ p ∈ f.primeFactors, (p : ℤ) =
      f * ∏ p ∈ f.primeFactors, ((p : ℤ) - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.totient_mul_prod_primeFactors f)
    push_cast at h
    rw [h, Finset.prod_congr rfl fun p hp ↦ Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos]
  have hU := TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod hK hf
  rw [Finset.prod_pow, Finset.prod_mul_distrib] at hU
  have hY : ∏ p ∈ f.primeFactors, ((p : ℤ) - 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    sub_ne_zero.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.ne')
  have hX : ∏ p ∈ f.primeFactors, (p : ℤ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  -- Multiply through by `f ∏ (p - 1) ∏ p = φ(f) (∏ p)²` and combine the formula with residue
  -- units `hA`, the totient product `hT` and the residue-unit count `hU`.
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hf) hY) hX) ?_
  linear_combination
    (-((Nat.card (Pic (intAddMulOrder K f)) : ℤ) *
        (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
          (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index *
        (∏ p ∈ f.primeFactors, (p : ℤ)) ^ 2)) * hT +
      (∏ p ∈ f.primeFactors, (p : ℤ)) ^ 3 * hA +
      (Nat.card (ClassGroup (𝓞 K)) * ∏ p ∈ f.primeFactors, (p : ℤ)) * hU

/-- **The class number of the order of conductor `f`** (Cox, Theorem 7.24). For the order
`O_f = ℤ + f 𝓞 K` of a quadratic field `K` with discriminant `D`,

`h(O_f) = h_K · f / [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} (1 - χ_D(p) / p)`,

in any field of characteristic zero. -/
theorem card_pic_intAddMulOrder_eq {F : Type*} [Field F] [CharZero F]
    (hK : Module.finrank ℚ K = 2) (f : ℕ) [NeZero f] :
    (Nat.card (Pic (intAddMulOrder K f)) : F) =
      Nat.card (ClassGroup (𝓞 K)) * f /
          (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
            (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index *
        ∏ p ∈ f.primeFactors,
          (1 - (fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p :
            F) / p) := by
  have hf : f ≠ 0 := NeZero.ne f
  -- The unit index is nonzero, since `h_K` and the number of residue units are.
  have hI : ((Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index : F) ≠ 0 := by
    have : Finite (𝓞 K ⧸ Ideal.span {(f : 𝓞 K)}) :=
      Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hf)
    have h := card_pic_intAddMulOrder_mul_index_mul_totient hK f
    refine Nat.cast_ne_zero.mpr fun h0 ↦ ?_
    rw [h0, mul_zero, zero_mul] at h
    exact (Nat.mul_pos Nat.card_pos Nat.card_pos).ne' h.symm
  have hX : ∏ p ∈ f.primeFactors, (p : F) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have key := congrArg (Int.cast : ℤ → F) (card_pic_intAddMulOrder_mul_index_mul_prod hK f)
  push_cast at key
  have hprod : (∏ p ∈ f.primeFactors,
      (1 - (fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p :
        F) / p)) * ∏ p ∈ f.primeFactors, (p : F) = ∏ p ∈ f.primeFactors,
      ((p : F) - fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK)
        p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  refine mul_right_cancel₀ (mul_ne_zero hI hX) ?_
  rw [← mul_assoc, key, ← hprod]
  field_simp

end TauCeti.GlobalNumberFields.NumberFieldOrder
