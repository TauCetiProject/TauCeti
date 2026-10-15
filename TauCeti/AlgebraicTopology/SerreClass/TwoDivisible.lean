/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Localization.Away
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic

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

namespace IsUniquelyTwoDivisible

variable {G : Type*} [AddCommGroup G]

/-- A uniquely two-divisible abelian group is a module over `ℤ[1/2]`. -/
@[instance_reducible]
def localizationAwayTwoModule (h : IsUniquelyTwoDivisible G) :
    Module (Localization.Away (2 : ℤ)) G :=
  localizationAwayModuleOfBijective h

/-- Tensoring a uniquely two-divisible abelian group with `ZMod 2` over `ℤ` gives the zero group. -/
theorem subsingleton_zmod_two_tensorProduct (h : IsUniquelyTwoDivisible G) :
    Subsingleton (TensorProduct ℤ (ZMod 2) G) := by
  rw [subsingleton_iff_forall_eq 0]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨y, rfl⟩ := h.2 y
      change x ⊗ₜ[ℤ] ((2 : ℤ) • y) = 0
      rw [two_zsmul, TensorProduct.tmul_add, ← TensorProduct.add_tmul,
        CharTwo.add_self_eq_zero, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [hx, hy, add_zero]

/-- Tensoring a uniquely two-divisible abelian group with `ZMod 2` over `ℤ` gives the zero group,
with the uniquely two-divisible group as the left tensor factor. -/
theorem subsingleton_tensorProduct_zmod_two (h : IsUniquelyTwoDivisible G) :
    Subsingleton (TensorProduct ℤ G (ZMod 2)) := by
  let _ := h.subsingleton_zmod_two_tensorProduct
  exact (TensorProduct.comm ℤ G (ZMod 2)).toEquiv.injective.subsingleton

end IsUniquelyTwoDivisible

end TauCeti

end
