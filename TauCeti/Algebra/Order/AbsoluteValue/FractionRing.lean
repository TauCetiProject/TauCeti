/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Extending an absolute value to a fraction field

An absolute value on a domain, taking values in an ordered field, extends uniquely to any
fraction field, with value `v a / v b` on `a / b`. Nonarchimedean absolute values remain
nonarchimedean. In particular,
this constructs normed fraction fields from multiplicative ring norms without completing them.

The multiplicative extension uses Mathlib's `Submonoid.LocalizationMap.lift₀`.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [IsDomain R]
    [Field S] [LinearOrder S]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The multiplicative extension underlying the fraction-field absolute value. -/
private noncomputable def fractionRingAbsHom (v : AbsoluteValue R S) : F →*₀ S :=
  (IsLocalization.toLocalizationMap R⁰ F).lift₀ v.toMonoidWithZeroHom
    (fun s ↦ isUnit_iff_ne_zero.mpr (v.ne_zero (nonZeroDivisors.ne_zero s.2)))

private theorem fractionRingAbsHom_algebraMap (v : AbsoluteValue R S) (a : R) :
    fractionRingAbsHom F v (algebraMap R F a) = v a := by
  exact Submonoid.LocalizationMap.lift_eq _ _ a

variable [IsStrictOrderedRing S]

private theorem fractionRingAbsHom_nonneg (v : AbsoluteValue R S) (x : F) :
    0 ≤ fractionRingAbsHom F v x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  simp only [map_div₀, fractionRingAbsHom_algebraMap]
  exact div_nonneg (v.nonneg a) (v.nonneg b)

/-- The unique extension of an absolute value to a fraction field. -/
noncomputable def fractionRingAbsoluteValue (v : AbsoluteValue R S) : AbsoluteValue F S where
  toFun := fractionRingAbsHom F v
  map_mul' := map_mul _
  nonneg' := fractionRingAbsHom_nonneg F v
  eq_zero' _ := map_eq_zero _
  add_le' x y := by
    obtain ⟨a, b, d, hx, hy⟩ := IsLocalization.surj₂ R⁰ F x y
    have hd : 0 < v d := v.pos (nonZeroDivisors.ne_zero d.2)
    apply (mul_le_mul_iff_left₀ hd).mp
    simpa only [mul_add, ← fractionRingAbsHom_algebraMap F v, ← map_mul, hx, hy,
      add_mul, ← map_add] using v.add_le a b

/-- The extension agrees with the absolute value on the original domain. -/
@[simp]
theorem fractionRingAbsoluteValue_algebraMap (v : AbsoluteValue R S) (a : R) :
    fractionRingAbsoluteValue F v (algebraMap R F a) = v a :=
  fractionRingAbsHom_algebraMap F v a

/-- An absolute value on a fraction field is determined by its restriction to the domain. -/
theorem fractionRingAbsoluteValue_unique (v : AbsoluteValue R S) (w : AbsoluteValue F S)
    (hw : ∀ a, w (algebraMap R F a) = v a) : w = fractionRingAbsoluteValue F v := by
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  simp [hw]

/-- Extending a nonarchimedean absolute value preserves the ultrametric inequality. -/
theorem isNonarchimedean_fractionRingAbsoluteValue (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) : IsNonarchimedean (fractionRingAbsoluteValue F v) := by
  intro x y
  obtain ⟨a, b, d, hx, hy⟩ := IsLocalization.surj₂ R⁰ F x y
  have hd : 0 < v d := v.pos (nonZeroDivisors.ne_zero d.2)
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [max_mul_of_nonneg _ _ hd.le]
  simpa only [← fractionRingAbsoluteValue_algebraMap F v, ← map_mul, add_mul, hx, hy,
    ← map_add] using hv a b

end TauCeti
