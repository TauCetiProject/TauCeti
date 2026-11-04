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

Use `TauCeti.fractionRingAbsoluteValue F v` to extend `v` to `F`;
`TauCeti.fractionRingAbsoluteValue_algebraMap` characterizes its restriction to the domain.

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

private theorem fractionRingAbsHom_mul_denominator (v : AbsoluteValue R S)
    {x : F} {a d : R} (h : x * algebraMap R F d = algebraMap R F a) :
    fractionRingAbsHom F v x * v d = v a := by
  calc
    _ = fractionRingAbsHom F v (x * algebraMap R F d) := by
      rw [map_mul, fractionRingAbsHom_algebraMap]
    _ = v a := by rw [h, fractionRingAbsHom_algebraMap]

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
    have hxy : (x + y) * algebraMap R F d = algebraMap R F (a + b) := by
      rw [add_mul, hx, hy, map_add]
    apply (mul_le_mul_iff_left₀ hd).mp
    rw [fractionRingAbsHom_mul_denominator F v hxy, add_mul,
      fractionRingAbsHom_mul_denominator F v hx, fractionRingAbsHom_mul_denominator F v hy]
    exact v.add_le a b

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
  have hxy : (x + y) * algebraMap R F d = algebraMap R F (a + b) := by
    rw [add_mul, hx, hy, map_add]
  -- Unwrap the absolute value to reuse the common-denominator lemmas for its underlying
  -- multiplicative homomorphism; those lemmas cannot rewrite through the wrapper directly.
  change fractionRingAbsHom F v (x + y) ≤
    max (fractionRingAbsHom F v x) (fractionRingAbsHom F v y)
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [fractionRingAbsHom_mul_denominator F v hxy, max_mul_of_nonneg _ _ hd.le,
    fractionRingAbsHom_mul_denominator F v hx, fractionRingAbsHom_mul_denominator F v hy]
  exact hv a b

end TauCeti
