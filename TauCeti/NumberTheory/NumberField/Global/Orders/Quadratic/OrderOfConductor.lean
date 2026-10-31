/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Orders.IntAddMulOrder
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor
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
turns this identity into the classical formula
`h(O_f) = h_K f / [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} (1 - (D / p) / p)` (Cox, Theorem 7.24).

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

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Lemma 7.2 and Theorem 7.24.
-/

public section
noncomputable section

open NumberField

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

end TauCeti.GlobalNumberFields.NumberFieldOrder
