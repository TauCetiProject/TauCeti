/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
public import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Tactic.LinearCombination

/-!
# Nonsquare quadratic orders

For a nonsquare integer `D ≡ 0, 1 mod 4`, the rational quadratic algebra is a number field.
The subalgebra `ℤ[(D + √D)/2]` constructed in `QuadraticOrder/Basic` is therefore an actual
`GlobalNumberFields.NumberFieldOrder`, of discriminant `D`.

This order is maximal exactly when `D` is a fundamental discriminant. The proof transports
Mathlib's criterion `QuadraticAlgebra.Int.isIntegralClosure_iff` for the integral model
`QuadraticAlgebra ℤ ((D - D²)/4) D` along the rational change of generator `ω ↦ (D + √D)/2`.
That criterion needs no nonsquare hypothesis, so neither does the integral-closure form.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open QuadraticAlgebra

namespace TauCeti.QuadraticOrder

/-- The integral quadratic order in the nonsquare number field. -/
noncomputable def numberFieldOrder (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] :
    GlobalNumberFields.NumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) where
  toSubalgebra := toSubalgebra D hD
  finite := inferInstance
  spans := span_toSubalgebra_eq_top D hD

/-- The field order has the subalgebra constructed in the rational quadratic algebra. -/
@[simp] theorem numberFieldOrder_toSubalgebra (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] : (numberFieldOrder D hD).toSubalgebra = toSubalgebra D hD := (rfl)

/-- The discriminant of the field order is its defining integer. -/
@[simp] theorem numberFieldOrder_discr (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] : (numberFieldOrder D hD).discr = D := by
  rw [← (numberFieldOrder D hD).discr_eq_discr (basis D hD)]
  exact discr_basis D hD

/-- The rational algebra of the integral model is identified with `ℚ(√D)` by sending its
generator to `(D + √D)/2`. -/
private def ratEquiv (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    QuadraticAlgebra ℚ (((D - D ^ 2) / 4 : ℤ) : ℚ) (D : ℚ) ≃ₐ[ℚ]
      QuadraticAlgebra ℚ (D : ℚ) 0 :=
  changeGeneratorEquiv (D : ℚ) 0 (Units.mk0 (1 / 2) (by norm_num)) ((D : ℚ) / 2)
    (by
      have hd := parameter_discr D hD
      rw [QuadraticAlgebra.discr_def] at hd
      have hdQ : (D : ℚ) ^ 2 + 4 * (((D - D ^ 2) / 4 : ℤ) : ℚ) = D := by exact_mod_cast hd
      rw [Units.val_mk0]
      linear_combination hdQ / 4)
    (by rw [Units.val_mk0]; ring)

/-- The rational identification restricts to the integral-model embedding. -/
private theorem ratEquiv_algebraMap (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    ratEquiv D hD (algebraMap _ (QuadraticAlgebra ℚ (((D - D ^ 2) / 4 : ℤ) : ℚ) (D : ℚ)) z) =
      lift D hD z := by
  rw [lift_apply]
  ext <;> simp [ratEquiv]

/-- **The order `ℤ[(D + √D)/2]` is the ring of integers exactly when `D` is fundamental.** The
subalgebra `TauCeti.QuadraticOrder.toSubalgebra D` of the model `ℚ(√D)` is the integral closure
of `ℤ` if and only if `D` is a fundamental discriminant. -/
theorem toSubalgebra_eq_integralClosure_iff (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    toSubalgebra D hD = integralClosure ℤ (QuadraticAlgebra ℚ (D : ℚ) 0) ↔
      Int.IsFundamentalDiscr D := by
  have h := QuadraticAlgebra.Int.isIntegralClosure_iff (a := (D - D ^ 2) / 4) (b := D)
  rw [parameter_discr D hD, isIntegralClosure_iff] at h
  rw [← h, SetLike.ext_iff, ← (ratEquiv D hD).toEquiv.forall_congr_right]
  refine forall_congr' fun x ↦ ?_
  have hx : IsIntegral ℤ (ratEquiv D hD x) ↔ IsIntegral ℤ x :=
    isIntegral_algEquiv ((ratEquiv D hD).restrictScalars ℤ)
  change (ratEquiv D hD x ∈ _ ↔ ratEquiv D hD x ∈ _) ↔ _
  rw [mem_integralClosure_iff, hx, mem_toSubalgebra_iff]
  refine Iff.comm.trans <| iff_congr Iff.rfl
    ⟨fun ⟨m, n, h⟩ ↦ ⟨⟨m, n⟩, (ratEquiv D hD).injective ?_⟩,
    fun ⟨w, h⟩ ↦ ⟨w.re, w.im, ?_⟩⟩
  · rw [ratEquiv_algebraMap, lift_apply, h]
  · rw [← h, ratEquiv_algebraMap, lift_apply]

/-- The quadratic field order is maximal exactly when its discriminant is fundamental. -/
@[simp] theorem numberFieldOrder_eq_maximal_iff (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] :
    numberFieldOrder D hD =
      GlobalNumberFields.maximalNumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) ↔
        Int.IsFundamentalDiscr D := by
  rw [← toSubalgebra_eq_integralClosure_iff D hD, ← numberFieldOrder_toSubalgebra,
    ← GlobalNumberFields.maximalNumberFieldOrder_toSubalgebra]
  exact ⟨congrArg _, GlobalNumberFields.NumberFieldOrder.ext⟩

end TauCeti.QuadraticOrder


