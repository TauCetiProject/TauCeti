/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.NarrowClass
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The orientation witness at discriminant twelve

The forms `x² - 3y²` and `-x² + 3y²` have the same raw ideal in `ℤ[√3]`, while the
orientation correction separates their narrow classes. The obstruction is elementary:
`m² - 3n²` cannot equal `-1` modulo three, so every order unit has norm one.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
-/

public section
noncomputable section

open QuadraticAlgebra FractionalIdeal TauCeti.GlobalNumberFields
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

private theorem not_isSquare_twelve : ¬ IsSquare (12 : ℤ) := by
  rintro ⟨n, hn⟩
  have hn2 : n ^ 2 = 12 := by nlinarith
  have hlo : -3 ≤ n := by
    by_contra h
    have : n ≤ -4 := by omega
    nlinarith
  have hhi : n ≤ 3 := by
    by_contra h
    have : 4 ≤ n := by omega
    nlinarith
  interval_cases n <;> norm_num at hn2

local instance : Fact (¬ IsSquare (12 : ℤ)) := ⟨not_isSquare_twelve⟩

private abbrev K12 := QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0
private abbrev o12 := QuadraticOrder.numberFieldOrder (12 : ℤ) (Or.inl rfl)

private theorem norm_discrimTwelve_order (z : (o12).toSubalgebra) :
    ∃ m n : ℤ, Algebra.norm ℚ (z : K12) = ((m ^ 2 - 3 * n ^ 2 : ℤ) : ℚ) := by
  have hz : (z : K12) ∈ QuadraticOrder.toSubalgebra (12 : ℤ) (by norm_num) := by
    exact (congrArg (fun O ↦ (z : K12) ∈ O)
      (QuadraticOrder.numberFieldOrder_toSubalgebra (12 : ℤ) (by norm_num))).mp z.property
  obtain ⟨m, n, hmn⟩ := (QuadraticOrder.mem_toSubalgebra_iff (12 : ℤ) (by norm_num) _).mp hz
  refine ⟨m + 6 * n, n, ?_⟩
  rw [hmn]
  norm_num [Algebra.norm_quadraticAlgebra_apply, QuadraticAlgebra.norm_def,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/-- Every unit of the discriminant-twelve order has norm one. -/
theorem norm_discrimTwelve_order_unit
    (u : (QuadraticOrder.numberFieldOrder (12 : ℤ) (Or.inl rfl)).toSubalgebraˣ) :
    Algebra.norm ℚ (u.val.val : QuadraticAlgebra ℚ ((12 : ℤ) : ℚ) 0) = 1 := by
  obtain ⟨m, n, hnorm⟩ := norm_discrimTwelve_order (u : (o12).toSubalgebra)
  obtain ⟨p, q, hinv⟩ := norm_discrimTwelve_order ((u⁻¹ : (o12).toSubalgebraˣ) : (o12).toSubalgebra)
  have hprod : Algebra.norm ℚ ((u : (o12).toSubalgebra) : K12) *
      Algebra.norm ℚ (((u⁻¹ : (o12).toSubalgebraˣ) : (o12).toSubalgebra) : K12) = 1 := by
    rw [← map_mul]
    have hu : ((u : (o12).toSubalgebra) : K12) *
        (((u⁻¹ : (o12).toSubalgebraˣ) : (o12).toSubalgebra) : K12) = 1 := by
      simpa only [map_mul, map_one, Subalgebra.algebraMap_apply, Units.inv_eq_val_inv] using
        congrArg (algebraMap (o12).toSubalgebra K12) u.val_inv
    rw [hu, map_one]
  rw [hnorm, hinv] at hprod
  have hprodZ : (m ^ 2 - 3 * n ^ 2) * (p ^ 2 - 3 * q ^ 2) = 1 := by
    exact_mod_cast hprod
  have hunit : IsUnit (m ^ 2 - 3 * n ^ 2) :=
    isUnit_iff_dvd_one.mpr ⟨p ^ 2 - 3 * q ^ 2, hprodZ.symm⟩
  rcases Int.isUnit_iff.mp hunit with h | h
  · rw [hnorm, h, Int.cast_one]
  · have hmod := congrArg (fun z : ℤ ↦ z % 3) h
    have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm with hm | hm | hm <;>
      norm_num [Int.sub_emod, Int.mul_emod, pow_two, hm] at hmod

/-- The primitive form `x² - 3y²`, of discriminant twelve. -/
def discrimTwelvePositiveLeading : primitiveForms 12 :=
  ⟨⟨1, 0, -3⟩, (mem_primitiveForms 12 _).mpr
    ⟨by norm_num [discrim_def, discrim], by norm_num [isPrimitive_iff, content_def]⟩⟩

/-- The primitive form `-x² + 3y²`, of discriminant twelve. -/
def discrimTwelveNegativeLeading : primitiveForms 12 :=
  ⟨⟨-1, 0, 3⟩, (mem_primitiveForms 12 _).mpr
    ⟨by norm_num [discrim_def, discrim], by norm_num [isPrimitive_iff, content_def]⟩⟩

/-- The positive discriminant-twelve form has coefficients `(1,0,-3)`. -/
@[simp] theorem coe_discrimTwelvePositiveLeading :
    discrimTwelvePositiveLeading.val = (⟨1, 0, -3⟩ : BinaryQuadraticForm ℤ) := by
  rfl

/-- The negative discriminant-twelve form has coefficients `(-1,0,3)`. -/
@[simp] theorem coe_discrimTwelveNegativeLeading :
    discrimTwelveNegativeLeading.val = (⟨-1, 0, 3⟩ : BinaryQuadraticForm ℤ) := by
  rfl

private theorem invertibleFractionalIdeal_eq_one_of_discrimTwelve (f : primitiveForms 12)
    (ha : f.val.a = 1 ∨ f.val.a = -1) :
    f.val.invertibleFractionalIdeal 12 ((mem_primitiveForms 12 f.val).mp f.property).1
      ((mem_primitiveForms 12 f.val).mp f.property).2 = 1 := by
  apply Units.ext
  rw [coe_invertibleFractionalIdeal, Units.val_one]
  refine le_antisymm (fractionalIdeal_le_one _ _ _) (FractionalIdeal.one_le.mpr ?_)
  apply (mem_fractionalIdeal_iff _ _ _ _).mpr
  rcases ha with ha | ha
  · exact ⟨1, 0, by simp [ha]⟩
  · exact ⟨-1, 0, by simp [ha]⟩

/-- The raw ideal of `x² - 3y²` is the unit ideal of the discriminant-twelve order. -/
theorem invertibleFractionalIdeal_discrimTwelvePositiveLeading_eq_one :
    discrimTwelvePositiveLeading.val.invertibleFractionalIdeal 12
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).2 = 1 :=
  invertibleFractionalIdeal_eq_one_of_discrimTwelve _ (by simp)

/-- The raw ideal of `-x² + 3y²` is the same unit ideal. -/
theorem invertibleFractionalIdeal_discrimTwelveNegativeLeading_eq_one :
    discrimTwelveNegativeLeading.val.invertibleFractionalIdeal 12
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).2 = 1 :=
  invertibleFractionalIdeal_eq_one_of_discrimTwelve _ (by simp)

/-- The oriented narrow class of `x² - 3y²` is trivial. -/
theorem narrowPicClass_discrimTwelvePositiveLeading :
    discrimTwelvePositiveLeading.val.narrowPicClass 12
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).2 = 1 := by
  rw [narrowPicClass_def, orientedInvertibleFractionalIdeal_of_a_pos _ _ _ _ (by simp),
    invertibleFractionalIdeal_discrimTwelvePositiveLeading_eq_one, map_one]

/-- The sign correction makes the narrow class of `-x² + 3y²` nontrivial. -/
theorem narrowPicClass_discrimTwelveNegativeLeading_ne_one :
    discrimTwelveNegativeLeading.val.narrowPicClass 12
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).2 ≠ 1 := by
  rw [narrowPicClass_def, orientedInvertibleFractionalIdeal_def,
    invertibleFractionalIdeal_discrimTwelveNegativeLeading_eq_one, mul_one,
    ← NarrowPic.mkPrincipal_apply]
  refine NarrowPic.mkPrincipal_ne_one_of_norm_neg o12 (fun u ↦ ?_) ?_
  · rw [norm_discrimTwelve_order_unit]
    norm_num
  · rw [norm_idealSignFactor]
    norm_num

/-- The two discriminant-twelve forms have distinct oriented narrow classes. -/
theorem narrowPicClass_discrimTwelvePositiveLeading_ne_negative :
    discrimTwelvePositiveLeading.val.narrowPicClass 12
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelvePositiveLeading.property).2 ≠
    discrimTwelveNegativeLeading.val.narrowPicClass 12
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).1
      ((mem_primitiveForms 12 _).mp discrimTwelveNegativeLeading.property).2 := by
  rw [narrowPicClass_discrimTwelvePositiveLeading]
  exact Ne.symm narrowPicClass_discrimTwelveNegativeLeading_ne_one

/-- The two discriminant-twelve forms are in distinct proper classes. -/
theorem properClass_discrimTwelvePositiveLeading_ne_negative :
    (Quotient.mk'' discrimTwelvePositiveLeading :
      MulAction.orbitRel.Quotient SL(2, ℤ) (primitiveForms 12)) ≠
        Quotient.mk'' discrimTwelveNegativeLeading := by
  intro h
  have hc := congrArg (properClassToNarrowPic 12 (by norm_num) (by norm_num)) h
  rw [properClassToNarrowPic_mk, properClassToNarrowPic_mk] at hc
  exact narrowPicClass_discrimTwelvePositiveLeading_ne_negative hc

end TauCeti.BinaryQuadraticForm
