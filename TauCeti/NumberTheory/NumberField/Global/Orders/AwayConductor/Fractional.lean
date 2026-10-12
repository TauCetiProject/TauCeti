/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.AwayConductor.Basic

/-!
# Fractional ideals of an order away from its conductor

For an order `O`, the invertible fractional ideals prime to its conductor are the quotients
`A / B` of integral ideals of `O` coprime to the conductor. Extension to the maximal order gives
an isomorphism from this subgroup to `idealsPrimeTo O.conductorModulus`. Its inverse contracts
an integral numerator and denominator separately and then takes their quotient. In particular,
it is not unrestricted set-theoretic contraction of a fractional ideal.

The integral extension/contraction comparison supplies the isomorphism of integral monoids.
Mathlib's universal property of monoid localization extends it to the fractional groups, so the
result is independent of the numerator and denominator chosen. Invertibility and the prime-to
condition are built into both carriers; no assertion about noninvertible ideals is made.

## Main results

* `NumberFieldOrder.fractionalIdealsAwayConductorEquiv`: the fractional extension/contraction
  comparison away from the conductor.
* `NumberFieldOrder.fractionalIdealsAwayConductorEquiv_integralIdealsAwayConductorHom`:
  compatibility with integral extension.
* `NumberFieldOrder.fractionalIdealsAwayConductorEquiv_symm_integralIdealsAwayHom`:
  compatibility with integral contraction.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12, Proposition 12.10.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- The invertible fractional ideals of `O` prime to its conductor: quotients of integral ideals
coprime to the conductor. -/
def fractionalIdealsAwayConductor : Subgroup O.invertibleProperFractionalIdeals where
  carrier := {I | ∃ A B : O.integralIdealsAwayConductor,
    I = O.integralIdealsAwayConductorToInvertible A /
      O.integralIdealsAwayConductorToInvertible B}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨A, B, rfl⟩ ⟨C, D, rfl⟩
    exact ⟨A * C, B * D, by simp [div_mul_div_comm]⟩
  inv_mem' := by
    rintro x ⟨A, B, rfl⟩
    exact ⟨B, A, by simp⟩

/-- Membership means admitting an integral numerator and denominator both coprime to the
conductor. -/
@[simp]
theorem mem_fractionalIdealsAwayConductor_iff {I : O.invertibleProperFractionalIdeals} :
    I ∈ O.fractionalIdealsAwayConductor ↔ ∃ A B : O.integralIdealsAwayConductor,
      I = O.integralIdealsAwayConductorToInvertible A /
        O.integralIdealsAwayConductorToInvertible B :=
  Iff.rfl

/-- Regard an integral ideal coprime to the conductor as a fractional ideal prime to the
conductor. -/
def integralIdealsAwayConductorHom :
    O.integralIdealsAwayConductor →* O.fractionalIdealsAwayConductor :=
  O.integralIdealsAwayConductorToInvertible.codRestrict _ fun I ↦ ⟨I, 1, by simp⟩

/-- The integral-to-fractional map does not change the underlying invertible ideal. -/
@[simp]
theorem coe_integralIdealsAwayConductorHom (I : O.integralIdealsAwayConductor) :
    (O.integralIdealsAwayConductorHom I : O.invertibleProperFractionalIdeals) =
      O.integralIdealsAwayConductorToInvertible I :=
  (rfl)

/-- An away-from-conductor fractional ideal is a quotient of two integral ideals in the same
carrier. -/
theorem exists_integralIdealsAwayConductor_div (I : O.fractionalIdealsAwayConductor) :
    ∃ A B : O.integralIdealsAwayConductor,
      I = O.integralIdealsAwayConductorHom A / O.integralIdealsAwayConductorHom B := by
  obtain ⟨A, B, h⟩ := I.2
  exact ⟨A, B, Subtype.ext h⟩

/-- Localization of the integral conductor-prime monoid inside the actual invertible fractional
ideals of the order. -/
private def fractionalLocalizationMap :
    Submonoid.LocalizationMap (⊤ : Submonoid O.integralIdealsAwayConductor)
      O.fractionalIdealsAwayConductor where
  toMulHom := O.integralIdealsAwayConductorHom.toMulHom
  isLocalizationMap := Submonoid.isLocalizationMap_of_group
    (fun _ _ h ↦ O.integralIdealsAwayConductorToInvertible_injective
      (congrArg Subtype.val h)) fun I ↦ by
        obtain ⟨A, B, h⟩ := O.exists_integralIdealsAwayConductor_div I
        exact ⟨A, B, Submonoid.mem_top _, h⟩

/-- The localization map is the canonical integral-to-fractional ideal map. -/
@[simp]
private theorem fractionalLocalizationMap_apply (I : O.integralIdealsAwayConductor) :
    O.fractionalLocalizationMap I = O.integralIdealsAwayConductorHom I :=
  (rfl)

/-- **Extension and contraction of invertible fractional ideals away from the conductor.**
On quotients of integral ideals, extension extends numerator and denominator; the inverse
contracts both separately. -/
def fractionalIdealsAwayConductorEquiv :
    O.fractionalIdealsAwayConductor ≃* idealsPrimeTo O.conductorModulus :=
  O.fractionalLocalizationMap.mulEquivOfMulEquiv
    (NumberFieldArithmetic.integralIdealsAwayLocalizationMap O.conductorModulus.support)
    (j := O.integralIdealsAwayConductorEquiv)
    (by simp)

/-- Fractional extension agrees with integral extension on integral ideals coprime to the
conductor. -/
@[simp]
theorem fractionalIdealsAwayConductorEquiv_integralIdealsAwayConductorHom
    (I : O.integralIdealsAwayConductor) :
    O.fractionalIdealsAwayConductorEquiv (O.integralIdealsAwayConductorHom I) =
      NumberFieldArithmetic.integralIdealsAwayHom O.conductorModulus.support
        (O.integralIdealsAwayConductorEquiv I) := by
  rw [fractionalIdealsAwayConductorEquiv]
  simpa only [fractionalLocalizationMap_apply,
    NumberFieldArithmetic.integralIdealsAwayLocalizationMap_apply] using
    O.fractionalLocalizationMap.mulEquivOfMulEquiv_eq
      (k := NumberFieldArithmetic.integralIdealsAwayLocalizationMap O.conductorModulus.support)
      (j := O.integralIdealsAwayConductorEquiv) (by simp) I

/-- Fractional contraction agrees with integral contraction on integral ideals prime to the
conductor. -/
@[simp]
theorem fractionalIdealsAwayConductorEquiv_symm_integralIdealsAwayHom
    (J : integralIdealsPrimeTo O.conductorModulus) :
    O.fractionalIdealsAwayConductorEquiv.symm
        (NumberFieldArithmetic.integralIdealsAwayHom O.conductorModulus.support J) =
      O.integralIdealsAwayConductorHom (O.integralIdealsAwayConductorEquiv.symm J) := by
  apply O.fractionalIdealsAwayConductorEquiv.symm_apply_eq.mpr
  simp

end TauCeti.GlobalNumberFields.NumberFieldOrder
