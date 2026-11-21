/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Stickelberger.Ideal
import TauCeti.Data.ZMod.Units

/-!
# Positive smoothing of the Stickelberger element

For a natural number `b`, the **positively smoothed Stickelberger element** is the element

`s_{m,b} = ∑_{a ∈ (ZMod m)ˣ} ⌊b a₀ / m⌋ [a⁻¹]`

of the integral group ring `ℤ[(ZMod m)ˣ]`, where `a₀` is the least nonnegative representative of
`a`. Its coefficients are natural-number quotients, hence nonnegative. When `b` is prime to `m`,
its image in the rational group ring is `(b - [b]) θ_m`, so `s_{m,b}` lies in the integral
Stickelberger ideal. These are the elements of the Stickelberger ideal whose action on ideal
classes is computed from Gauss sums in the proof of Stickelberger's theorem.

The sign is the opposite of that of the generators `[b] - b` of the denominator ideal: it makes the
coefficients nonnegative. At `m = 5`, `b = 2` the coefficients at `[3]` and `[2]` are `0` and `1`.

## Main definitions

* `TauCeti.smoothedStickelberger m b`: the positively smoothed Stickelberger element `s_{m,b}`.

## Main results

* `TauCeti.coeff_smoothedStickelberger`: the coefficient of `s_{m,b}` at `[c]` is `⌊b (c⁻¹)₀ / m⌋`.
* `TauCeti.mapRingHom_smoothedStickelberger`: for `b` prime to `m`, `s_{m,b} = (b - [b]) θ_m`.
* `TauCeti.mapRingHom_smoothedStickelberger_self`: `s_{m,m} = m θ_m`.
* `TauCeti.smoothedStickelberger_mem_stickelbergerIdeal`: for `b` prime to `m`, `s_{m,b}` lies in
  the integral Stickelberger ideal.
* `TauCeti.smoothedStickelberger_zero`, `TauCeti.smoothedStickelberger_one`: `s_{m,0} = 0` and
  `s_{m,1} = 0`.
* `TauCeti.smoothedStickelberger_add_self`: `s_{m,b+m} = s_{m,b} + s_{m,m}`.
* `TauCeti.smoothedStickelberger_mul`: for `d` prime to `m` and every natural `b`,
  `s_{m,bd} = b s_{m,d} + [d] s_{m,b}`.
* `TauCeti.stickelbergerIdeal_three_eq_top`: at conductor three, `s_{3,2} = [2]` is a unit, so the
  integral Stickelberger ideal is the whole group ring.

## References

* R. Sharifi, *Iwasawa theory* (lecture notes), Lemma 4.5.2 and its proof.
* L. C. Washington, *Introduction to Cyclotomic Fields*, §6.2.
* C. Birkbeck, AINTLIB, module `BernoulliRegular.Stickelberger` (see the references of
  `TauCeti.NumberTheory.Cyclotomic.Stickelberger.Basic` for the commit): at a prime `m = p`, the
  identity `mapRingHom_smoothedStickelberger_self` is AINTLIB's `smul_stickelbergerElement`, and
  `smoothedStickelberger p p` has the coefficients of its `stickelbergerScaled p`. The code here
  is not copied from it.
-/

public section

open MonoidAlgebra

namespace TauCeti

variable (m : ℕ) [NeZero m]

/-- The **positively smoothed Stickelberger element** `s_{m,b} = ∑_a ⌊b a₀ / m⌋ [a⁻¹]` of
`ℤ[(ZMod m)ˣ]`, where `a₀` is the least nonnegative representative of `a`. The floor is the
natural-number quotient. For `b` prime to `m` it equals `(b - [b]) θ_m`. -/
noncomputable def smoothedStickelberger (b : ℕ) : MonoidAlgebra ℤ (ZMod m)ˣ :=
  ∑ a : (ZMod m)ˣ, single a⁻¹ ((b * (a : ZMod m).val / m : ℕ) : ℤ)

/-- The defining finite sum of the positively smoothed Stickelberger element. -/
theorem smoothedStickelberger_def (b : ℕ) :
    smoothedStickelberger m b = ∑ a : (ZMod m)ˣ, single a⁻¹ ((b * (a : ZMod m).val / m : ℕ) : ℤ) :=
  (rfl)

/-- The coefficient of `s_{m,b}` at `[c]` is `⌊b (c⁻¹)₀ / m⌋`. -/
@[simp]
theorem coeff_smoothedStickelberger (b : ℕ) (c : (ZMod m)ˣ) :
    (smoothedStickelberger m b).coeff c =
      ((b * ((c⁻¹ : (ZMod m)ˣ) : ZMod m).val / m : ℕ) : ℤ) := by
  classical
  simp [smoothedStickelberger_def, coeff_sum, coeff_single, Finsupp.single_apply,
    inv_eq_iff_eq_inv]

/-- Smoothing with `b = 0` gives zero. -/
@[simp]
theorem smoothedStickelberger_zero : smoothedStickelberger m 0 = 0 := by
  simp [smoothedStickelberger_def]

/-- Smoothing with `b = 1` gives zero: every representative is less than `m`. -/
@[simp]
theorem smoothedStickelberger_one : smoothedStickelberger m 1 = 0 := by
  ext c
  simp [Nat.div_eq_of_lt (ZMod.val_lt _)]

/-- Adding `m` to `b` adds `s_{m,m}`, the integral element `m θ_m`
(`mapRingHom_smoothedStickelberger_self`). -/
theorem smoothedStickelberger_add_self (b : ℕ) :
    smoothedStickelberger m (b + m) = smoothedStickelberger m b + smoothedStickelberger m m := by
  ext c
  simp [add_mul, Nat.add_mul_div_left _ _ (NeZero.pos m),
    Nat.mul_div_cancel_left _ (NeZero.pos m)]

/-- The smoothing `s_{m,m}` is `m θ_m`, the integral element `∑_a a₀ [a⁻¹]`. -/
theorem mapRingHom_smoothedStickelberger_self :
    mapRingHom _ (Int.castRingHom ℚ) (smoothedStickelberger m m) = m * stickelberger m := by
  ext c
  have hm : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  simp [coeff_natCast_mul, Nat.mul_div_cancel_left _ (NeZero.pos m), mul_div_cancel₀ _ hm]

variable {m}

/-- **The rational smoothing identity.** For `b` prime to `m`, the image of `s_{m,b}` in the
rational group ring is `(b - [b]) θ_m`. -/
theorem mapRingHom_smoothedStickelberger {b : ℕ} (hb : b.Coprime m) :
    mapRingHom _ (Int.castRingHom ℚ) (smoothedStickelberger m b) =
      ((b : MonoidAlgebra ℚ (ZMod m)ˣ) - single (ZMod.unitOfCoprime b hb) 1) * stickelberger m := by
  ext c
  have hm : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  set v := ((c⁻¹ : (ZMod m)ˣ) : ZMod m).val
  -- The representative of `c⁻¹ b` is `b v mod m`, and `b v = m ⌊b v / m⌋ + (b v mod m)`.
  have hval : (((ZMod.unitOfCoprime b hb)⁻¹ * c)⁻¹ : (ZMod m)ˣ).val.val = b * v % m := by
    simp [v, mul_comm, ZMod.coe_unitOfCoprime, ZMod.val_mul, ZMod.val_natCast]
  have h : (m : ℚ) * (b * v / m : ℕ) + (b * v % m : ℕ) = b * v := by
    exact_mod_cast Nat.div_add_mod (b * v) m
  simp only [coeff_mapRingHom, coeff_smoothedStickelberger, sub_mul, coeff_sub, Finsupp.sub_apply,
    coeff_natCast_mul, coeff_single_mul_apply, coeff_stickelberger, hval, Int.coe_castRingHom,
    Int.cast_natCast, one_mul]
  field_simp
  linear_combination h

/-- For `b` prime to `m`, the smoothing `s_{m,b}` lies in the integral Stickelberger ideal: it is
`x θ_m` for `x = b - [b]`. -/
theorem smoothedStickelberger_mem_stickelbergerIdeal {b : ℕ} (hb : b.Coprime m) :
    smoothedStickelberger m b ∈ stickelbergerIdeal m :=
  mem_stickelbergerIdeal.2 ⟨(b : MonoidAlgebra ℤ (ZMod m)ˣ) - single (ZMod.unitOfCoprime b hb) 1,
    by simp [mapRingHom_smoothedStickelberger hb]⟩

/-- **Product relation for smoothings.** For `d` prime to `m` and every natural number `b`,
`s_{m,bd} = b s_{m,d} + [d] s_{m,b}`. -/
theorem smoothedStickelberger_mul (b : ℕ) {d : ℕ} (hd : d.Coprime m) :
    smoothedStickelberger m (b * d) =
      (b : MonoidAlgebra ℤ (ZMod m)ˣ) * smoothedStickelberger m d +
        single (ZMod.unitOfCoprime d hd) 1 * smoothedStickelberger m b := by
  ext c
  set v := ((c⁻¹ : (ZMod m)ˣ) : ZMod m).val
  -- The representative of `c⁻¹ d` is `d v mod m`; write `d v = m q + r` with `r = d v mod m`.
  have hval : (((ZMod.unitOfCoprime d hd)⁻¹ * c)⁻¹ : (ZMod m)ˣ).val.val = d * v % m := by
    simp [v, mul_comm, ZMod.coe_unitOfCoprime, ZMod.val_mul, ZMod.val_natCast]
  simp only [coeff_smoothedStickelberger, coeff_add, Finsupp.add_apply, coeff_natCast_mul,
    coeff_single_mul_apply, hval, one_mul]
  conv_lhs => rw [mul_assoc, ← Nat.div_add_mod (d * v) m, mul_add, ← mul_assoc, mul_comm b m,
    mul_assoc, Nat.mul_add_div (NeZero.pos m)]
  push_cast
  ring

/-- At conductor three the floors of `2 a₀ / 3` are `0` and `1`, so `s_{3,2} = [2⁻¹] = [2]`. -/
theorem smoothedStickelberger_three_two :
    smoothedStickelberger 3 2 = single (ZMod.unitOfCoprime 2 (by decide)) 1 := by
  ext c
  rw [coeff_smoothedStickelberger, coeff_single, Finsupp.single_apply]
  revert c
  decide

/-- At conductor three the integral Stickelberger ideal is the whole group ring: it contains the
unit `s_{3,2} = [2]`. By contrast the denominator ideal `J_3` is proper
(`stickelbergerDenominatorIdeal_ne_top`), so the two ideals differ. -/
theorem stickelbergerIdeal_three_eq_top : stickelbergerIdeal 3 = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _
    (smoothedStickelberger_mem_stickelbergerIdeal (b := 2) (by decide)) ?_
  rw [smoothedStickelberger_three_two]
  refine IsUnit.of_mul_eq_one (single (ZMod.unitOfCoprime 2 (by decide)) 1) ?_
  rw [single_mul_single, mul_one, one_def]
  congr 1
  decide

end TauCeti
