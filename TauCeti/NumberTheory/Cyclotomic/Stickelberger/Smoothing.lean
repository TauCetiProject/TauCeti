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
* `TauCeti.smoothedStickelberger_add_self`: `s_{m,b+m} = s_{m,b} + s_{m,m}`; the smoothing is not a
  function of the residue of `b`.
* `TauCeti.smoothedStickelberger_mul`: for `b, d` prime to `m`,
  `s_{m,bd} = b s_{m,d} + [d] s_{m,b}`.
* `TauCeti.stickelbergerIdeal_three_eq_top`: at conductor three, `s_{3,2} = [2]` is a unit, so the
  integral Stickelberger ideal is the whole group ring.

## References

* R. Sharifi, *Iwasawa theory* (lecture notes), Lemma 4.5.2 and its proof.
* L. C. Washington, *Introduction to Cyclotomic Fields*, §6.2.
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
  rw [smoothedStickelberger_def, coeff_sum, Finset.sum_apply',
    Finset.sum_eq_single_of_mem c⁻¹ (Finset.mem_univ _) fun a _ hac ↦ ?_]
  · simp
  · rw [coeff_single, Finsupp.single_eq_of_ne (by rintro rfl; simp at hac)]

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
(`mapRingHom_smoothedStickelberger_self`). In particular the smoothing depends on `b` and not only
on its residue modulo `m`. -/
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
  set v := ((c⁻¹ : (ZMod m)ˣ) : ZMod m).val with hv
  -- The representative of `c⁻¹ b` is `b v mod m`.
  have hval : (((ZMod.unitOfCoprime b hb)⁻¹ * c)⁻¹ : (ZMod m)ˣ).val.val = b * v % m := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val
      ((c⁻¹ : (ZMod m)ˣ) : ZMod m), ← hv, mul_comm, ← Nat.cast_mul, ZMod.val_natCast]
  rw [sub_mul, coeff_sub, Finsupp.sub_apply, coeff_natCast_mul, coeff_single_mul_apply,
    coeff_stickelberger, coeff_stickelberger, hval, coeff_mapRingHom, coeff_smoothedStickelberger,
    ← hv, one_mul, eq_comm, mul_div_assoc', div_sub_div_same, div_eq_iff hm, eq_intCast,
    Int.cast_natCast, sub_eq_iff_eq_add]
  exact_mod_cast (Nat.div_add_mod' (b * v) m).symm

/-- For `b` prime to `m`, the smoothing `s_{m,b}` lies in the integral Stickelberger ideal: it is
`x θ_m` for `x = b - [b]`. -/
theorem smoothedStickelberger_mem_stickelbergerIdeal {b : ℕ} (hb : b.Coprime m) :
    smoothedStickelberger m b ∈ stickelbergerIdeal m :=
  mem_stickelbergerIdeal.2 ⟨(b : MonoidAlgebra ℤ (ZMod m)ˣ) - single (ZMod.unitOfCoprime b hb) 1,
    by simp [mapRingHom_smoothedStickelberger hb]⟩

/-- **Product relation for smoothings.** For `b` and `d` prime to `m`,
`s_{m,bd} = b s_{m,d} + [d] s_{m,b}`. -/
theorem smoothedStickelberger_mul {b d : ℕ} (hb : b.Coprime m) (hd : d.Coprime m) :
    smoothedStickelberger m (b * d) =
      (b : MonoidAlgebra ℤ (ZMod m)ˣ) * smoothedStickelberger m d +
        single (ZMod.unitOfCoprime d hd) 1 * smoothedStickelberger m b := by
  apply map_injective (Int.castRingHom ℚ : ℤ →+ ℚ) Int.cast_injective
  rw [← coe_mapRingHom, map_add, map_mul, map_mul, map_natCast, mapRingHom_single,
    mapRingHom_smoothedStickelberger hb, mapRingHom_smoothedStickelberger hd,
    mapRingHom_smoothedStickelberger (Nat.coprime_mul_iff_left.2 ⟨hb, hd⟩),
    ZMod.unitOfCoprime_mul hb hd, map_one]
  have hsingle : single (ZMod.unitOfCoprime b hb * ZMod.unitOfCoprime d hd) (1 : ℚ) =
      single (ZMod.unitOfCoprime b hb) 1 * single (ZMod.unitOfCoprime d hd) 1 := by
    rw [single_mul_single, mul_one]
  rw [hsingle]
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
