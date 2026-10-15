/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Proper ideals of primitive binary quadratic forms

The fractional ideal of a primitive integral form of nonsquare discriminant is proper and
invertible over the associated quadratic number-field order. Its multiplier ring is the
order itself. These invertible ideals define ideal classes in the form-ideal correspondence.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra
open scoped nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- The ideal of a primitive form is proper in the actual quadratic number-field order. -/
theorem IsPrimitive.fractionalIdeal_isProper {f : BinaryQuadraticForm ℤ}
    (hprim : f.IsPrimitive) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).IsProperFractionalIdeal
      (f.fractionalIdeal D hf) := by
  let hD := hf ▸ f.discrim_emod_four_eq_zero_or_one
  apply (GlobalNumberFields.NumberFieldOrder.isProperFractionalIdeal_iff _ _).mpr
  intro x hx
  have ha : f.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)
  have hx₁ := hx _ (a_mem_fractionalIdeal f D hf)
  have hx₂ := hx _ (idealGenerator_mem_fractionalIdeal f D hf)
  obtain ⟨m, n, hm⟩ := (mem_fractionalIdeal_iff f D hf _).mp hx₁
  obtain ⟨r, s, hr⟩ := (mem_fractionalIdeal_iff f D hf _).mp hx₂
  have hmre := congrArg QuadraticAlgebra.re hm
  have hmim := congrArg QuadraticAlgebra.im hm
  have hrre := congrArg QuadraticAlgebra.re hr
  have hrim := congrArg QuadraticAlgebra.im hr
  simp only [zsmul_eq_mul, re_add, re_mul, re_intCast, im_intCast, mul_zero, add_zero,
    idealGenerator_re, idealGenerator_im, one_div, zero_mul, im_add, im_mul, zero_add]
    at hmre hmim hrre hrim
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  have hnb : n * f.b = (m - s) * f.a := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linear_combination -hmre + (f.b : ℚ) * hmim + 2 * (f.a : ℚ) * hrim
  have hnc : n * f.c = -(r * f.a) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linear_combination hrre + (f.b : ℚ) * hrim - x.im / 2 * hd + 2 * (f.c : ℚ) * hmim
  obtain ⟨u, v, w, huvw⟩ := hprim.exists_linearCombination_eq_one
  have hn : n = (u * n + v * (m - s) - w * r) * f.a := by
    linear_combination -n * huvw + v * hnb + w * hnc
  let t := u * n + v * (m - s) - w * r
  have hxform : x = m • 1 + t • f.idealGenerator D := by
    have haK : (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by exact_mod_cast ha
    apply mul_right_cancel₀ haK
    rw [← hm, hn]
    ext <;> simp [t] <;> ring
  apply (congrArg (fun O ↦ x ∈ O) (QuadraticOrder.numberFieldOrder_toSubalgebra D hD)).mpr
  rw [hxform]
  exact (QuadraticOrder.toSubalgebra D hD).add_mem
    ((QuadraticOrder.toSubalgebra D hD).toSubmodule.smul_mem m
      (QuadraticOrder.toSubalgebra D hD).one_mem)
    ((QuadraticOrder.toSubalgebra D hD).toSubmodule.smul_mem t (idealGenerator_mem_order f D hf))

/-- The proper fractional ideal associated with a primitive form. -/
noncomputable def properFractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (hprim : f.IsPrimitive) : (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).properFractionalIdeals :=
  ⟨f.fractionalIdeal D hf, hprim.fractionalIdeal_isProper D hf⟩

/-- The raw proper form ideal has the original fractional ideal as its value. -/
@[simp] theorem coe_properFractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (hprim : f.IsPrimitive) : (f.properFractionalIdeal D hf hprim).val =
      f.fractionalIdeal D hf := (rfl)

/-- The fractional ideal of a primitive form is invertible. -/
theorem IsPrimitive.fractionalIdeal_isUnit {f : BinaryQuadraticForm ℤ}
    (hprim : f.IsPrimitive) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] : IsUnit (f.fractionalIdeal D hf) :=
by
  let O := QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one)
  exact (O.isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two
    (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0) _).mp (hprim.fractionalIdeal_isProper D hf)

/-- The invertible fractional ideal associated with a primitive form. -/
noncomputable def invertibleFractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (hprim : f.IsPrimitive) :
    (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).invertibleProperFractionalIdeals :=
  (hprim.fractionalIdeal_isUnit D hf).unit

/-- The invertible form ideal has the original fractional ideal as its value. -/
@[simp] theorem coe_invertibleFractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (hprim : f.IsPrimitive) : (f.invertibleFractionalIdeal D hf hprim).val =
      f.fractionalIdeal D hf := (hprim.fractionalIdeal_isUnit D hf).unit_spec

end TauCeti.BinaryQuadraticForm
