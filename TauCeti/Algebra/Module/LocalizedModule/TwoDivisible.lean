/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Away.Basic
public import TauCeti.Algebra.Module.ZMod.TensorProduct
import TauCeti.Algebra.Group.PowMonoidHom

/-!
# Uniquely two-divisible abelian groups

An abelian group is uniquely two-divisible when multiplication by two is a bijection. Such a group
carries a module structure over `ℤ[1/2]`, and its tensor product with `ZMod 2` vanishes; the
latter needs only two-divisibility (`TauCeti.subsingleton_zmod_tensorProduct_iff`).

These are the algebraic consequences of mod-two acyclicity used in the Whitehead-tower proof of
the mod-two Hurewicz theorem.

## Main definitions

* `TauCeti.IsUniquelyTwoDivisible`: multiplication by two is bijective.
* `TauCeti.IsUniquelyTwoDivisible.localizationAwayTwoModule`: the induced `ℤ[1/2]`-module.

## Main results

* `TauCeti.IsUniquelyTwoDivisible.subsingleton_zmod_two_tensorProduct`: tensoring a uniquely
  two-divisible group with `ZMod 2` gives the zero group.
* `TauCeti.IsUniquelyTwoDivisible.subsingleton_tensorProduct_zmod_two`: the same conclusion with
  the tensor factors in the opposite order.
* `TauCeti.isUniquelyTwoDivisible_iff_isUnit`: a ring is uniquely two-divisible exactly when `2`
  is a unit; so `ℤ` is not (`TauCeti.not_isUniquelyTwoDivisible_int`), and `ℤ/n` is exactly for
  odd `n` (`TauCeti.isUniquelyTwoDivisible_zmod_iff`).
* `TauCeti.isUniquelyTwoDivisible_iff_odd_natCard`: a finite abelian group is uniquely
  two-divisible exactly when its order is odd.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

noncomputable section

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
    Subsingleton (TensorProduct ℤ (ZMod 2) G) := by
  rw [subsingleton_zmod_tensorProduct_iff, Nat.cast_ofNat]
  exact h.2

/-- Tensoring a uniquely two-divisible abelian group with `ZMod 2` over `ℤ` gives the zero group,
with the uniquely two-divisible group as the left tensor factor. -/
theorem subsingleton_tensorProduct_zmod_two (h : IsUniquelyTwoDivisible G) :
    Subsingleton (TensorProduct ℤ G (ZMod 2)) := by
  rw [subsingleton_tensorProduct_zmod_iff, Nat.cast_ofNat]
  exact h.2

end IsUniquelyTwoDivisible

/-! ### Examples -/

/-- A ring is uniquely two-divisible, as an additive group, exactly when `2` is a unit. -/
theorem isUniquelyTwoDivisible_iff_isUnit (R : Type*) [Ring R] :
    IsUniquelyTwoDivisible R ↔ IsUnit (2 : R) := by
  have h : (fun x : R ↦ (2 : ℤ) • x) = ((2 : R) * ·) := funext fun x ↦ by
    rw [zsmul_eq_mul, Int.cast_ofNat]
  rw [isUniquelyTwoDivisible_iff, h, IsUnit.isUnit_iff_mulLeft_bijective]

/-- The integers are not uniquely two-divisible: `1` is not twice an integer. -/
@[simp]
theorem not_isUniquelyTwoDivisible_int : ¬ IsUniquelyTwoDivisible ℤ := by
  rw [isUniquelyTwoDivisible_iff_isUnit, Int.isUnit_iff]
  decide

/-- The cyclic group `ℤ/n` is uniquely two-divisible exactly when `n` is odd. For `n = 0`, where
`ZMod 0 = ℤ`, both sides fail. -/
@[simp]
theorem isUniquelyTwoDivisible_zmod_iff (n : ℕ) : IsUniquelyTwoDivisible (ZMod n) ↔ Odd n := by
  rw [isUniquelyTwoDivisible_iff_isUnit, ← Nat.cast_ofNat, ZMod.isUnit_iff_coprime,
    Nat.coprime_two_left]

/-- A finite abelian group is uniquely two-divisible exactly when its order is odd: multiplication
by two is onto, hence bijective, exactly when two is prime to the order
(`TauCeti.nsmulAddMonoidHom_range_eq_top_iff_coprime`). -/
theorem isUniquelyTwoDivisible_iff_odd_natCard (G : Type*) [AddCommGroup G] [Finite G] :
    IsUniquelyTwoDivisible G ↔ Odd (Nat.card G) := by
  have h : (fun x : G ↦ (2 : ℤ) • x) = nsmulAddMonoidHom 2 := funext fun x ↦ by
    rw [nsmulAddMonoidHom_apply, ← natCast_zsmul, Nat.cast_ofNat]
  rw [isUniquelyTwoDivisible_iff, h, ← Finite.surjective_iff_bijective,
    ← AddMonoidHom.range_eq_top, nsmulAddMonoidHom_range_eq_top_iff_coprime, Nat.coprime_two_right]

end TauCeti

end
