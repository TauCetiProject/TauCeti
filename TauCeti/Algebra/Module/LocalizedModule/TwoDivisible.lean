/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Away.Basic
public import TauCeti.Algebra.Module.ZMod.TensorProduct

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

end TauCeti

end
