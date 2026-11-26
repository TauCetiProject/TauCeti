/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.GroupWithZero.NegLog
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Monoid.TypeTags

/-!
# Additive valuations attached to multiplicative valuations

A valuation with values in `Mᵐ⁰ = WithZero (Multiplicative M)` carries the same information as an
additive valuation with values in `WithTop M = M ∪ {∞}`, the dictionary between the two being
`WithZero.negLog`, which sends `WithZero.exp m` to `-m` and `0` to `∞`. This file records that
translation, in both directions.

`Valuation.toAddValuation` already exhibits the bijection
`Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ`, but its codomain is a type synonym for `Γ₀`
itself, whereas an additive valuation is usually taken to have values in a type of the shape
`M ∪ {∞}`. Composing it with the order-and-additive isomorphism `WithZero.orderAddIsoWithTop`
lands in `WithTop M`.

Adapted from William Coram's [Mathlib PR #43580](https://github.com/leanprover-community/mathlib4/pull/43580),
revision `d87db7956b7510870d514f10da52a0f22a5e54a6`.

## Main definitions

* `Valuation.addVal`: the additive valuation `R → WithTop M` attached to a valuation
  `v : Valuation R Mᵐ⁰`, sending `x` to `WithZero.negLog (v x)`.
* `Valuation.addValValueGroup`: the additive valuation attached to an arbitrary valuation
  `v : Valuation R Γ₀`, with values in `WithTop` of the value group of `v` written additively.
* `AddValuation.expNeg`: the inverse conversion, sending an additive valuation
  `v : R → WithTop M` to the valuation `x ↦ exp (-v x)` with values in `Mᵐ⁰`, such as the order of
  vanishing of meromorphic functions to a normalized discrete valuation `R → ℤᵐ⁰`.

## Main results

* `Valuation.addVal_apply` and `Valuation.addVal_eq_coe`: the characteristic equations
  of the conversion. In particular, `simp` gives `v.addVal x = ∞ ↔ v x = 0`.
* `Valuation.addVal_map`: `Valuation.addVal` is natural in `M`, in the sense that pushing `v`
  forward along the multiplicative form of `f` pushes `v.addVal` forward along `f`.
* `AddValuation.addVal_expNeg` and `Valuation.expNeg_addVal`: `AddValuation.expNeg` and
  `Valuation.addVal` are inverse to each other.
-/

public section

open scoped WithZero

namespace Valuation

open WithZero

variable {R M N : Type*} [Ring R] [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
  [AddCommGroup N] [LinearOrder N] [IsOrderedAddMonoid N]

/-- The additive valuation with values in `WithTop M = M ∪ {∞}` attached to a valuation `v` with
values in `Mᵐ⁰`: it sends `x` to `WithZero.negLog (v x)`, so that `WithZero.exp m ↦ -m` and
`0 ↦ ∞`. -/
def addVal (v : Valuation R Mᵐ⁰) : AddValuation R (WithTop M) :=
  v.toAddValuation.map (orderAddIsoWithTop M : (Additive Mᵐ⁰)ᵒᵈ →+o WithTop M)
    ((orderAddIsoWithTop_apply _).trans negLog_zero)

/-- The conversion is the existing type-tagged additive valuation, followed by the
order-additive isomorphism to `WithTop M`. -/
lemma addVal_def (v : Valuation R Mᵐ⁰) :
    v.addVal = v.toAddValuation.map (orderAddIsoWithTop M : (Additive Mᵐ⁰)ᵒᵈ →+o WithTop M)
      ((orderAddIsoWithTop_apply _).trans negLog_zero) := (rfl)

@[simp]
lemma addVal_apply (v : Valuation R Mᵐ⁰) (x : R) : v.addVal x = negLog (v x) := by
  unfold addVal
  exact orderAddIsoWithTop_apply _

lemma addVal_eq_coe {v : Valuation R Mᵐ⁰} {x : R} {m : M} :
    v.addVal x = (m : WithTop M) ↔ v x = exp (-m) := by
  rw [addVal_apply, negLog_eq_coe]

/-- Pushing a valuation forward along an order-preserving additive map of value groups
commutes with conversion to an additive valuation. -/
lemma addVal_map (v : Valuation R Mᵐ⁰) {f : M →+ N} (hf : Monotone f) (x : R) :
    (v.map { map' (AddMonoidHom.toMultiplicative f) with
      monotone' := map'_mono (fun _ _ h ↦ hf h) }).addVal x =
    WithTop.map f (v.addVal x) := by
  simpa using negLog_map f (v x)

/-! ### The additive valuation with values in the value group -/

section ValueGroup

open MonoidWithZeroHom

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

/-- The additive valuation attached to an arbitrary valuation `v : Valuation R Γ₀`, with values in
`WithTop` of the value group of `v` written additively. -/
noncomputable def addValValueGroup :
    AddValuation R (WithTop (Additive (valueGroup (v : R →*₀ Γ₀)))) :=
  addVal (M := Additive (valueGroup (v : R →*₀ Γ₀))) v.restrict

lemma addValValueGroup_apply (x : R) :
  v.addValValueGroup x = negLog (M := Additive (valueGroup (v : R →*₀ Γ₀))) (v.restrict x) := by
  unfold addValValueGroup
  exact addVal_apply (M := Additive (valueGroup (v : R →*₀ Γ₀))) v.restrict x

/-- The additive value is infinite exactly on the support of the original valuation. -/
@[simp]
lemma addValValueGroup_eq_top {x : R} : v.addValValueGroup x = ⊤ ↔ v x = 0 := by
  rw [addValValueGroup_apply]
  exact (negLog_eq_top (M := Additive (valueGroup (v : R →*₀ Γ₀)))) |>.trans
    v.restrict_eq_zero_iff

end ValueGroup

end Valuation

/-! ### The valuation attached to an additive valuation -/

namespace AddValuation

open WithZero

variable {R M : Type*} [Ring R] [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- The valuation with values in `Mᵐ⁰` attached to an additive valuation `v` with values in
`WithTop M = M ∪ {∞}`: it sends `x` to `exp (-v x)`, and to `0` when `v x = ∞`. This is the
inverse of `Valuation.addVal`, defined through the inverse of `WithZero.orderAddIsoWithTop`. -/
def expNeg (v : AddValuation R (WithTop M)) : Valuation R Mᵐ⁰ :=
  Valuation.ofAddValuation
    (v.map ((orderAddIsoWithTop M).symm : WithTop M →+o (Additive Mᵐ⁰)ᵒᵈ)
      ((orderAddIsoWithTop M).symm.toOrderIso.map_top))

variable {v : AddValuation R (WithTop M)} {x : R}

@[simp]
lemma negLog_expNeg (v : AddValuation R (WithTop M)) (x : R) : negLog (v.expNeg x) = v x :=
  (orderAddIsoWithTop_apply _).symm.trans ((orderAddIsoWithTop M).apply_symm_apply (v x))

lemma expNeg_eq_exp_iff {m : M} : v.expNeg x = exp (-m) ↔ v x = m := by
  rw [← negLog_eq_coe, negLog_expNeg]

@[simp]
lemma expNeg_eq_zero_iff : v.expNeg x = 0 ↔ v x = ⊤ := by
  rw [← negLog_eq_top, negLog_expNeg]

@[simp]
lemma expNeg_eq_one_iff : v.expNeg x = 1 ↔ v x = 0 := by
  simpa using expNeg_eq_exp_iff (v := v) (x := x) (m := 0)

/-- `AddValuation.expNeg` is a left inverse of `Valuation.addVal`. -/
@[simp]
lemma addVal_expNeg (v : AddValuation R (WithTop M)) : v.expNeg.addVal = v :=
  AddValuation.ext fun x ↦ by rw [Valuation.addVal_apply, negLog_expNeg]

end AddValuation

/-- `AddValuation.expNeg` is a right inverse of `Valuation.addVal`. -/
@[simp]
lemma Valuation.expNeg_addVal {R M : Type*} [Ring R] [AddCommGroup M] [LinearOrder M]
    [IsOrderedAddMonoid M] (v : Valuation R Mᵐ⁰) : v.addVal.expNeg = v :=
  Valuation.ext fun x ↦ le_antisymm (WithZero.negLog_le_negLog.mp (by simp))
    (WithZero.negLog_le_negLog.mp (by simp))
