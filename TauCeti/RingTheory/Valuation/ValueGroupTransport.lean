/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Transporting the value group along an equivalence of valuations

Mathlib's `Valuation.IsEquiv.orderMonoidIso` transports value groups along an equivalence
of valuations. This file records its functoriality, using the corresponding results for
`Valuation.IsEquiv.orderMonoidIso₀` on value groups with zero adjoined.

## Main results

* `Valuation.IsEquiv.orderMonoidIso_symm_eq`,
  `Valuation.IsEquiv.orderMonoidIso_self` and
  `Valuation.IsEquiv.orderMonoidIso_trans_eq` : the transport respects inverses, identities
  and composition.

-/

public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- Transport along the inverse equivalence is the inverse transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_symm`. -/
theorem IsEquiv.orderMonoidIso_symm_eq {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.orderMonoidIso.symm = h'.orderMonoidIso :=
  (rfl)

/-- Transport along a valuation's equivalence with itself is the identity. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_eq_refl`. -/
@[simp]
theorem IsEquiv.orderMonoidIso_self {v : Valuation A Γ₀}
    (h : v.IsEquiv v) : h.orderMonoidIso = .refl _ := by
  ext1 γ
  apply WithZero.coe_injective
  simpa only [Valuation.IsEquiv.orderMonoidIso₀_coe, OrderMonoidIso.coe_refl, id_eq] using
    congrArg (fun e : v.ValueGroup₀ ≃*o v.ValueGroup₀ ↦ e γ) h.orderMonoidIso₀_eq_refl

/-- Transport along a composite equivalence is the composite transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_trans`. -/
@[simp]
theorem IsEquiv.orderMonoidIso_trans_eq {Γ₀'' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀''] {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    {u : Valuation A Γ₀''} (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.orderMonoidIso.trans h'.orderMonoidIso = (h.trans h').orderMonoidIso := by
  ext1 γ
  apply WithZero.coe_injective
  simpa only [OrderMonoidIso.trans_apply, Valuation.IsEquiv.orderMonoidIso₀_coe] using
    congrArg (fun e : v.ValueGroup₀ ≃*o u.ValueGroup₀ ↦ e γ) (h.orderMonoidIso₀_trans h')

end Valuation
