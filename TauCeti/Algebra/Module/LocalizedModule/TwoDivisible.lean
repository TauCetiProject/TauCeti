/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Uniquely two-divisible abelian groups

An abelian group is uniquely two-divisible when multiplication by two is a bijection. Such a group
carries a module structure over `ℤ[1/2]`, and its tensor product with `ZMod 2` vanishes.

These are the algebraic consequences of mod-two acyclicity used in the Whitehead-tower proof of
the mod-two Hurewicz theorem.

## Main definitions

* `TauCeti.IsUniquelyTwoDivisible`: multiplication by two is bijective.
* `TauCeti.IsUniquelyTwoDivisible.localizationAwayTwoModule`: the induced `ℤ[1/2]`-module.

## Main results

* `Function.Surjective.subsingleton_zmod_two_tensorProduct`: tensoring with `ZMod 2` kills any
  abelian group on which multiplication by two is surjective; it only needs two-divisibility.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_zmod_two_tensorProduct`: tensoring a uniquely
  two-divisible group with `ZMod 2` gives the zero group.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_tensorProduct_zmod_two`: the same conclusion with
  the tensor factors in the opposite order.
* `TauCeti.odd_addOrderOf_of_smul_eq_zero`: in a `ℤ[1/2]`-module, an element killed by a nonzero
  scalar has odd additive order.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

noncomputable section

namespace Function.Surjective

variable {G : Type*} [AddCommGroup G]

/-- Tensoring an abelian group on which multiplication by two is surjective with `ZMod 2` over `ℤ`
gives the zero group. -/
theorem subsingleton_zmod_two_tensorProduct
    (h : Function.Surjective fun x : G ↦ (2 : ℤ) • x) :
    Subsingleton (TensorProduct ℤ (ZMod 2) G) := by
  rw [subsingleton_iff_forall_eq 0]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨y, rfl⟩ := h y
      rw [← TensorProduct.smul_tmul, CharTwo.two_zsmul, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [hx, hy, add_zero]

/-- Tensoring an abelian group on which multiplication by two is surjective with `ZMod 2` over `ℤ`
gives the zero group, with that group as the left tensor factor. -/
theorem subsingleton_tensorProduct_zmod_two
    (h : Function.Surjective fun x : G ↦ (2 : ℤ) • x) :
    Subsingleton (TensorProduct ℤ G (ZMod 2)) := by
  let _ := h.subsingleton_zmod_two_tensorProduct
  exact (TensorProduct.comm ℤ G (ZMod 2)).toEquiv.injective.subsingleton

end Function.Surjective

namespace TauCeti

/-- An additive commutative group is **uniquely two-divisible** when multiplication by two is a
bijection. -/
def IsUniquelyTwoDivisible (G : Type*) [AddCommGroup G] : Prop :=
  Function.Bijective fun x : G ↦ (2 : ℤ) • x

/-- Unique two-divisibility is bijectivity of multiplication by two. This characterizes the
predicate without requiring its defining body to be exposed to importing modules. -/
theorem isUniquelyTwoDivisible_iff (G : Type*) [AddCommGroup G] :
    IsUniquelyTwoDivisible G ↔ Function.Bijective (fun x : G ↦ (2 : ℤ) • x) :=
  Iff.rfl

namespace IsUniquelyTwoDivisible

variable {G : Type*} [AddCommGroup G]

/-- Unique two-divisibility is preserved by additive equivalences. -/
theorem of_addEquiv (h : IsUniquelyTwoDivisible G) {H : Type*} [AddCommGroup H]
    (e : G ≃+ H) : IsUniquelyTwoDivisible H := by
  rw [isUniquelyTwoDivisible_iff] at h ⊢
  have he : (fun y : H ↦ (2 : ℤ) • y) = e ∘ (fun x : G ↦ (2 : ℤ) • x) ∘ e.symm := by
    ext y
    simp
  rw [he]
  exact e.bijective.comp (h.comp e.symm.bijective)

/-- A uniquely two-divisible abelian group is a module over `ℤ[1/2]`. Its compatibility with the
canonical integer action, `IsScalarTower ℤ (Localization.Away 2) G`, is automatic from Mathlib's
instance `AddCommGroup.intIsScalarTower`. -/
@[instance_reducible]
def localizationAwayTwoModule (h : IsUniquelyTwoDivisible G) :
    Module (Localization.Away (2 : ℤ)) G :=
  Function.Bijective.localizationAwayModule h

/-- Tensoring a uniquely two-divisible abelian group with `ZMod 2` over `ℤ` gives the zero
group. -/
theorem subsingleton_zmod_two_tensorProduct (h : IsUniquelyTwoDivisible G) :
    Subsingleton (TensorProduct ℤ (ZMod 2) G) :=
  Function.Surjective.subsingleton_zmod_two_tensorProduct h.2

/-- Tensoring a uniquely two-divisible abelian group with `ZMod 2` over `ℤ` gives the zero group,
with the uniquely two-divisible group as the left tensor factor. -/
theorem subsingleton_tensorProduct_zmod_two (h : IsUniquelyTwoDivisible G) :
    Subsingleton (TensorProduct ℤ G (ZMod 2)) :=
  Function.Surjective.subsingleton_tensorProduct_zmod_two h.2

end IsUniquelyTwoDivisible

/-- In a `ℤ[1/2]`-module, an element killed by a nonzero scalar has odd additive order: writing the
scalar as `z / 2ʲ` it is killed by the nonzero integer `z`, and two acts invertibly. -/
theorem odd_addOrderOf_of_smul_eq_zero {M : Type*} [AddCommGroup M]
    [Module (Localization.Away (2 : ℤ)) M] {a : Localization.Away (2 : ℤ)} (ha : a ≠ 0) {x : M}
    (hx : a • x = 0) : Odd (addOrderOf x) := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) a
  have hz : z ≠ 0 := by
    rintro rfl
    exact ha (IsLocalization.mk'_zero _)
  have hzx : z • x = 0 := by
    simpa [mul_smul, hx, Int.cast_smul_eq_zsmul] using
      congr($(IsLocalization.mk'_spec' (Localization.Away (2 : ℤ)) z s) • x).symm
  have hpos : 0 < addOrderOf x :=
    (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨z, hz, hzx⟩).addOrderOf_pos
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  rintro ⟨m, hm⟩
  -- If the order were `2 m`, then `m • x` would be killed by the unit `2`, so `m • x = 0`.
  have h2 : IsUnit (2 : Localization.Away (2 : ℤ)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (2 : ℤ)) (2 : ℤ)
  have hmx : m • x = 0 := by
    apply h2.smul_left_cancel.1
    simp [ofNat_smul_eq_nsmul, ← mul_nsmul', ← hm]
  have := Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero hmx)
  omega

end TauCeti

end
