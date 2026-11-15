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

section ToMultiplicative

variable [AddMonoid α] [TopologicalSpace α] [AddMonoid β] [TopologicalSpace β]
  [AddMonoid γ] [TopologicalSpace γ]

/-- Reinterpret `α →ₜ+ β` as `Multiplicative α →ₜ* Multiplicative β`. -/
def ContinuousAddMonoidHom.toMultiplicative :
    (α →ₜ+ β) ≃ (Multiplicative α →ₜ* Multiplicative β) where
  toFun f :=
    { toMonoidHom := f.toAddMonoidHom.toMultiplicative
      continuous_toFun := continuous_ofAdd.comp (f.continuous.comp continuous_toAdd) }
  invFun f :=
    { toAddMonoidHom := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
      continuous_toFun := continuous_toAdd.comp (f.continuous.comp continuous_ofAdd) }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem ContinuousAddMonoidHom.toMultiplicative_toMonoidHom (f : α →ₜ+ β) :
    (f.toMultiplicative : Multiplicative α →* Multiplicative β) =
      f.toAddMonoidHom.toMultiplicative :=
  (rfl)

@[simp]
theorem ContinuousAddMonoidHom.coe_toMultiplicative (f : α →ₜ+ β) :
    ⇑f.toMultiplicative = ofAdd ∘ f ∘ toAdd :=
  (rfl)

@[simp]
theorem ContinuousAddMonoidHom.toMultiplicative_apply_apply (f : α →ₜ+ β) (a : Multiplicative α) :
    f.toMultiplicative a = ofAdd (f a.toAdd) :=
  (rfl)

@[simp]
theorem ContinuousAddMonoidHom.toMultiplicative_symm_apply_apply
    (f : Multiplicative α →ₜ* Multiplicative β) (a : α) :
    (ContinuousAddMonoidHom.toMultiplicative.symm f) a = (f (ofAdd a)).toAdd :=
  (rfl)

@[simp]
theorem ContinuousAddMonoidHom.toMultiplicative_id :
    (ContinuousAddMonoidHom.id α).toMultiplicative = ContinuousMonoidHom.id (Multiplicative α) :=
  (rfl)

/-- `ContinuousAddMonoidHom.toMultiplicative` commutes with composition. -/
theorem ContinuousAddMonoidHom.toMultiplicative_comp (g : β →ₜ+ γ) (f : α →ₜ+ β) :
    (g.comp f).toMultiplicative = g.toMultiplicative.comp f.toMultiplicative :=
  (rfl)

end ToMultiplicative

section ToAdditive

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]
  [Monoid γ] [TopologicalSpace γ]

/-- Reinterpret `α →ₜ* β` as `Additive α →ₜ+ Additive β`. -/
def ContinuousMonoidHom.toAdditive :
    (α →ₜ* β) ≃ (Additive α →ₜ+ Additive β) where
  toFun f :=
    { toAddMonoidHom := f.toMonoidHom.toAdditive
      continuous_toFun := continuous_ofMul.comp (f.continuous.comp continuous_toMul) }
  invFun f :=
    { toMonoidHom := MonoidHom.toAdditive.symm f.toAddMonoidHom
      continuous_toFun := continuous_toMul.comp (f.continuous.comp continuous_ofMul) }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem ContinuousMonoidHom.toAdditive_toAddMonoidHom (f : α →ₜ* β) :
    (f.toAdditive : Additive α →+ Additive β) = f.toMonoidHom.toAdditive :=
  (rfl)

@[simp]
theorem ContinuousMonoidHom.coe_toAdditive (f : α →ₜ* β) :
    ⇑f.toAdditive = ofMul ∘ f ∘ toMul :=
  (rfl)

@[simp]
theorem ContinuousMonoidHom.toAdditive_apply_apply (f : α →ₜ* β) (a : Additive α) :
    f.toAdditive a = ofMul (f a.toMul) :=
  (rfl)

@[simp]
theorem ContinuousMonoidHom.toAdditive_symm_apply_apply
    (f : Additive α →ₜ+ Additive β) (a : α) :
    (ContinuousMonoidHom.toAdditive.symm f) a = (f (ofMul a)).toMul :=
  (rfl)

@[simp]
theorem ContinuousMonoidHom.toAdditive_id :
    (ContinuousMonoidHom.id α).toAdditive = ContinuousAddMonoidHom.id (Additive α) :=
  (rfl)

/-- `ContinuousMonoidHom.toAdditive` commutes with composition. -/
theorem ContinuousMonoidHom.toAdditive_comp (g : β →ₜ* γ) (f : α →ₜ* β) :
    (g.comp f).toAdditive = g.toAdditive.comp f.toAdditive :=
  (rfl)

end ToAdditive
