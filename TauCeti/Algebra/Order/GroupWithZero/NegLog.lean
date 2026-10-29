/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# `negLog : Mᵐ⁰ → WithTop M`

This file identifies `Mᵐ⁰ = WithZero (Multiplicative M)` with `WithTop M`, in the form of the
order-and-additive isomorphism `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`.

The underlying map is `WithZero.negLog`, which is `WithZero.log` in its "additive valuation"
reading: instead of the junk value `log 0 = 0` we record `0` as the genuine `⊤`, and we negate,
so that the reversed order on `Mᵐ⁰` becomes the usual order on `WithTop M`.

Adapted from William Coram's [Mathlib PR #43578](https://github.com/leanprover-community/mathlib4/pull/43578),
revision `c2a17f4dd6efb2b77123c31434e9589e91daafdc`.

## Main definitions

* `WithZero.negLog : Mᵐ⁰ → WithTop M`, sending `0 ↦ ⊤` and `exp m ↦ -m`.
* `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`, the order-and-additive
  isomorphism underlying it. `(Additive Mᵐ⁰)ᵒᵈ` is the additive-with-`⊤` rendering of `Mᵐ⁰`
  provided by `Mathlib/Algebra/Order/GroupWithZero/Canonical.lean`; this isomorphism turns it
  into the familiar `WithTop M = M ∪ {∞}`.
* `WithZero.negLog_map`: naturality under additive maps, using `WithZero.map'`
  on their multiplicative type tags.
-/

public section

open scoped WithZero

namespace WithZero

/-! ### `negLog` -/

section NegLog

variable {M : Type*}

section Neg

variable [Neg M]

/-- The map `Mᵐ⁰ → WithTop M` sending `0` to `⊤` and `exp m` to `-m`.

This is `WithZero.log` in its "additive valuation" reading: instead of the junk value `log 0 = 0`
we record `0` as the genuine `⊤`, and we negate, so that the reversed order on `Mᵐ⁰` becomes the
usual order on `WithTop M`. -/
def negLog (x : Mᵐ⁰) : WithTop M := expRecOn x ⊤ fun m ↦ ((-m : M) : WithTop M)

@[simp]
lemma negLog_zero : negLog (0 : Mᵐ⁰) = ⊤ := (rfl)

@[simp]
lemma negLog_exp (m : M) : negLog (exp m) = ((-m : M) : WithTop M) := (rfl)

@[simp]
lemma negLog_eq_top {x : Mᵐ⁰} : negLog x = ⊤ ↔ x = 0 := by
  induction x using expRecOn <;> simp

end Neg

@[simp]
lemma negLog_one [NegZeroClass M] : negLog (1 : Mᵐ⁰) = 0 := by
  simpa only [exp_eq_coe_ofAdd, ofAdd_zero, coe_one, neg_zero,
    WithTop.coe_zero] using negLog_exp (0 : M)

lemma negLog_eq_coe [InvolutiveNeg M] {x : Mᵐ⁰} {m : M} :
    negLog x = (m : WithTop M) ↔ x = exp (-m) := by
  induction x using expRecOn <;> simp [Ne.symm exp_ne_zero, neg_eq_iff_eq_neg]

@[simp]
lemma negLog_mul [SubtractionCommMonoid M] (x y : Mᵐ⁰) : negLog (x * y) = negLog x + negLog y := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => simp only [← exp_add, negLog_exp, neg_add, WithTop.coe_add]

@[simp]
lemma negLog_le_negLog [AddGroup M] [Preorder M] [AddLeftMono M] [AddRightMono M]
    {x y : Mᵐ⁰} : negLog x ≤ negLog y ↔ y ≤ x := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => simp [neg_le_neg_iff]

variable [AddCommGroup M] [Preorder M] [AddLeftMono M]

variable (M) in
/-- The order-and-additive isomorphism `(Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M` underlying `negLog`.

`(Additive Mᵐ⁰)ᵒᵈ` is the additive-with-`⊤` rendering of `Mᵐ⁰`; this isomorphism turns it into
the familiar `WithTop M = M ∪ {∞}`. -/
def orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M where
  toFun x := negLog x
  invFun y := y.recTopCoe (0 : Mᵐ⁰) fun m ↦ exp (-m)
  left_inv x := by
    induction x using expRecOn with
    | zero => rfl
    | exp a => exact congrArg exp (neg_neg a)
  right_inv y := by
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe m => exact (negLog_exp (-m)).trans (congrArg (fun a : M ↦ (a : WithTop M)) (neg_neg m))
  map_add' := negLog_mul
  map_le_map_iff' := negLog_le_negLog

-- Keep evaluation named: rewriting the bundled map prevents generic inverse laws from matching.
lemma orderAddIsoWithTop_apply (x : (Additive Mᵐ⁰)ᵒᵈ) : orderAddIsoWithTop M x = negLog x := (rfl)

lemma orderAddIsoWithTop_symm_coe (m : M) :
    (orderAddIsoWithTop M).symm (m : WithTop M) = exp (-m) := (rfl)

end NegLog

/-! ### Naturality -/

variable {M N : Type*} [AddGroup M] [SubtractionMonoid N]

/-- The negative logarithm commutes with additive homomorphisms. -/
lemma negLog_map (f : M →+ N) (x : Mᵐ⁰) :
    negLog (map' (AddMonoidHom.toMultiplicative f) x) = WithTop.map f (negLog x) := by
  induction x using expRecOn with
  | zero => rfl
  | exp a =>
    rw [negLog_exp, WithTop.map_coe, map_neg]
    exact negLog_exp (f a)

end WithZero
