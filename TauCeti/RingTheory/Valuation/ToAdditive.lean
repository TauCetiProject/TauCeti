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
translation.

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

## Main results

* `Valuation.addVal_apply` and `Valuation.addVal_eq_coe`: the characteristic equations
  of the conversion. In particular, `simp` gives `v.addVal x = ∞ ↔ v x = 0`.
* `Valuation.addVal_map`: `Valuation.addVal` is natural in `M`, in the sense that pushing `v`
  forward along the multiplicative form of `f` pushes `v.addVal` forward along `f`.
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
