/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions

/-!
# Transporting continuous monoid homomorphisms between additive and multiplicative type tags

This file upgrades `AddMonoidHom.toMultiplicative` and `MonoidHom.toAdditive` to equivalences
between bundled continuous homomorphisms:

* `ContinuousAddMonoidHom.toMultiplicative : (α →ₜ+ β) ≃ (Multiplicative α →ₜ* Multiplicative β)`
* `ContinuousMonoidHom.toAdditive : (α →ₜ* β) ≃ (Additive α →ₜ+ Additive β)`
-/

public section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

variable {α β γ : Type*}

namespace ContinuousAddMonoidHom

variable [AddMonoid α] [TopologicalSpace α] [AddMonoid β] [TopologicalSpace β]
  [AddMonoid γ] [TopologicalSpace γ]

/-- Reinterpret `α →ₜ+ β` as `Multiplicative α →ₜ* Multiplicative β`. -/
def toMultiplicative : (α →ₜ+ β) ≃ (Multiplicative α →ₜ* Multiplicative β) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative,
    continuous_ofAdd.comp (f.continuous.comp continuous_toAdd)⟩
  invFun f := ⟨AddMonoidHom.toMultiplicative.symm f.toMonoidHom,
    continuous_toAdd.comp (f.continuous.comp continuous_ofAdd)⟩
  left_inv _ := rfl; right_inv _ := rfl

@[simp] theorem toMultiplicative_toMonoidHom (f : α →ₜ+ β) :
    (f.toMultiplicative : Multiplicative α →* Multiplicative β) =
      (f : α →+ β).toMultiplicative := (rfl)
@[simp] theorem toMultiplicative_symm_toAddMonoidHom (f : Multiplicative α →ₜ* Multiplicative β) :
    (toMultiplicative.symm f : α →+ β) =
      AddMonoidHom.toMultiplicative.symm (f : Multiplicative α →* Multiplicative β) := (rfl)

@[simp] theorem coe_toMultiplicative (f : α →ₜ+ β) :
    ⇑f.toMultiplicative = ofAdd ∘ f ∘ toAdd := (rfl)
@[simp] theorem coe_toMultiplicative_symm (f : Multiplicative α →ₜ* Multiplicative β) :
    ⇑(toMultiplicative.symm f) = toAdd ∘ f ∘ ofAdd := (rfl)

@[simp] theorem toMultiplicative_apply_apply (f : α →ₜ+ β) (a : Multiplicative α) :
    f.toMultiplicative a = ofAdd (f a.toAdd) := (rfl)
@[simp] theorem toMultiplicative_symm_apply_apply
    (f : Multiplicative α →ₜ* Multiplicative β) (a : α) :
    (toMultiplicative.symm f) a = (f (ofAdd a)).toAdd := (rfl)

@[simp] theorem toMultiplicative_id :
    (id α).toMultiplicative = ContinuousMonoidHom.id (Multiplicative α) := (rfl)
@[simp] theorem toMultiplicative_symm_id :
    toMultiplicative.symm (ContinuousMonoidHom.id (Multiplicative α)) = id α := (rfl)

/-- `ContinuousAddMonoidHom.toMultiplicative` commutes with composition. -/
theorem toMultiplicative_comp (g : β →ₜ+ γ) (f : α →ₜ+ β) :
    (g.comp f).toMultiplicative = g.toMultiplicative.comp f.toMultiplicative := (rfl)
/-- `ContinuousAddMonoidHom.toMultiplicative.symm` commutes with composition. -/
@[simp] theorem toMultiplicative_symm_comp
    (g : Multiplicative β →ₜ* Multiplicative γ) (f : Multiplicative α →ₜ* Multiplicative β) :
    toMultiplicative.symm (g.comp f) =
      (toMultiplicative.symm g).comp (toMultiplicative.symm f) := (rfl)

end ContinuousAddMonoidHom

namespace ContinuousMonoidHom

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]
  [Monoid γ] [TopologicalSpace γ]

/-- Reinterpret `α →ₜ* β` as `Additive α →ₜ+ Additive β`. -/
def toAdditive : (α →ₜ* β) ≃ (Additive α →ₜ+ Additive β) where
  toFun f := ⟨f.toMonoidHom.toAdditive, continuous_ofMul.comp (f.continuous.comp continuous_toMul)⟩
  invFun f := ⟨MonoidHom.toAdditive.symm f.toAddMonoidHom,
    continuous_toMul.comp (f.continuous.comp continuous_ofMul)⟩
  left_inv _ := rfl; right_inv _ := rfl

@[simp] theorem toAdditive_toAddMonoidHom (f : α →ₜ* β) :
    (f.toAdditive : Additive α →+ Additive β) = (f : α →* β).toAdditive := (rfl)
@[simp] theorem toAdditive_symm_toMonoidHom (f : Additive α →ₜ+ Additive β) :
    (toAdditive.symm f : α →* β) =
      MonoidHom.toAdditive.symm (f : Additive α →+ Additive β) := (rfl)

@[simp] theorem coe_toAdditive (f : α →ₜ* β) : ⇑f.toAdditive = ofMul ∘ f ∘ toMul := (rfl)
@[simp] theorem coe_toAdditive_symm (f : Additive α →ₜ+ Additive β) :
    ⇑(toAdditive.symm f) = toMul ∘ f ∘ ofMul := (rfl)

@[simp] theorem toAdditive_apply_apply (f : α →ₜ* β) (a : Additive α) :
    f.toAdditive a = ofMul (f a.toMul) := (rfl)
@[simp] theorem toAdditive_symm_apply_apply (f : Additive α →ₜ+ Additive β) (a : α) :
    (toAdditive.symm f) a = (f (ofMul a)).toMul := (rfl)

@[simp] theorem toAdditive_id :
    (id α).toAdditive = ContinuousAddMonoidHom.id (Additive α) := (rfl)
@[simp] theorem toAdditive_symm_id :
    toAdditive.symm (ContinuousAddMonoidHom.id (Additive α)) = id α := (rfl)

/-- `ContinuousMonoidHom.toAdditive` commutes with composition. -/
theorem toAdditive_comp (g : β →ₜ* γ) (f : α →ₜ* β) :
    (g.comp f).toAdditive = g.toAdditive.comp f.toAdditive := (rfl)
/-- `ContinuousMonoidHom.toAdditive.symm` commutes with composition. -/
@[simp] theorem toAdditive_symm_comp
    (g : Additive β →ₜ+ Additive γ) (f : Additive α →ₜ+ Additive β) :
    toAdditive.symm (g.comp f) = (toAdditive.symm g).comp (toAdditive.symm f) := (rfl)

end ContinuousMonoidHom
