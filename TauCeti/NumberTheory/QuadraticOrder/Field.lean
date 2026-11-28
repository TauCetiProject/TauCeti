/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger

/-!
# Nonsquare quadratic orders

For a nonsquare integer `D ≡ 0, 1 mod 4`, the rational quadratic algebra is a number field.
The subalgebra `ℤ[(D + √D)/2]` constructed in `QuadraticOrder/Basic` is therefore an actual
`GlobalNumberFields.NumberFieldOrder`, of discriminant `D`.

The theorem `numberFieldOrder_eq_maximal_iff` deduces maximality exactly for fundamental
discriminants from `toSubalgebra_eq_integralClosure_iff`.
The theorem `QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr` then characterizes when the
field discriminant is `D`.

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

/-- The quadratic field order is maximal exactly when its discriminant is fundamental. -/
@[simp] theorem numberFieldOrder_eq_maximal_iff (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] :
    numberFieldOrder D hD =
      GlobalNumberFields.maximalNumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) ↔
        Int.IsFundamentalDiscr D := by
  rw [← toSubalgebra_eq_integralClosure_iff hD, ← numberFieldOrder_toSubalgebra,
    ← GlobalNumberFields.maximalNumberFieldOrder_toSubalgebra]
  exact ⟨congrArg _, GlobalNumberFields.NumberFieldOrder.ext⟩

/-- For a nonsquare integer `D`, the field discriminant of `QuadraticAlgebra ℚ D 0` equals `D` if
and only if `D` is a fundamental discriminant. -/
theorem _root_.QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr {D : ℤ} [Fact (¬ IsSquare D)] :
    NumberField.discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D ↔ Int.IsFundamentalDiscr D := by
  constructor
  · intro h
    have hD : D % 4 = 0 ∨ D % 4 = 1 :=
      h ▸ TauCeti.NumberField.discr_emod_four_eq_zero_or_one (QuadraticAlgebra ℚ (D : ℚ) 0)
    exact (numberFieldOrder_eq_maximal_iff D hD).mp <|
      (numberFieldOrder D hD).discr_eq_discr_iff.mp ((numberFieldOrder_discr D hD).trans h.symm)
  · intro hfund
    have hD := hfund.emod_four_eq_zero_or_one
    exact ((numberFieldOrder D hD).discr_eq_discr_iff.mpr
      ((numberFieldOrder_eq_maximal_iff D hD).mpr hfund)).symm.trans (numberFieldOrder_discr D hD)

end TauCeti.QuadraticOrder
