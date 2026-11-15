/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Tensoring on the left with a fixed element

For modules `M` and `N` over a commutative ring `k` and an element `z ∈ M`, the morphism
`TauCeti.ModuleCat.tensorMk z : N ⟶ M ⊗ N` sends `v` to `z ⊗ₜ v`; it is Mathlib's
`TensorProduct.mk k M N z` as a morphism of `ModuleCat k`. This file records how it interacts
with the whiskerings of the monoidal structure and that it is additive and `k`-linear in `z`, so
that a calculation with morphisms out of a tensor product evaluated at a fixed first factor stays
in the category.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace TauCeti.ModuleCat

variable {k : Type u} [CommRing k]

/-- Tensoring on the left with a fixed element `z ∈ M`, as a morphism `N ⟶ M ⊗ N`: Mathlib's
`TensorProduct.mk k M N z` in `ModuleCat k`. -/
noncomputable def tensorMk {M N : ModuleCat.{u} k} (z : M) : N ⟶ M ⊗ N :=
  ModuleCat.ofHom (TensorProduct.mk k M N z)

/-- `TauCeti.ModuleCat.tensorMk z` sends `v` to the pure tensor `z ⊗ₜ v`. -/
@[simp]
lemma tensorMk_apply {M N : ModuleCat.{u} k} (z : M) (v : N) : tensorMk z v = z ⊗ₜ[k] v :=
  (rfl)

/-- Precomposing `TauCeti.ModuleCat.tensorMk z` with `g` is whiskering `g` on the left. -/
@[reassoc]
lemma comp_tensorMk {M N N' : ModuleCat.{u} k} (z : M) (g : N' ⟶ N) :
    g ≫ tensorMk (N := N) z = tensorMk z ≫ (M ◁ g) := by
  ext v
  rfl

/-- Whiskering `g` on the right after `TauCeti.ModuleCat.tensorMk z` is tensoring with `g z`. -/
@[reassoc (attr := simp)]
lemma tensorMk_whiskerRight {M M' N : ModuleCat.{u} k} (z : M) (g : M ⟶ M') :
    tensorMk (N := N) z ≫ (g ▷ N) = tensorMk (g z) := by
  ext v
  rfl

/-- `TauCeti.ModuleCat.tensorMk` is additive in the fixed element. -/
lemma tensorMk_add {M N : ModuleCat.{u} k} (z z' : M) :
    tensorMk (N := N) (z + z') = tensorMk z + tensorMk z' := by
  ext v
  exact TensorProduct.add_tmul z z' v

/-- `TauCeti.ModuleCat.tensorMk` is `k`-linear in the fixed element. -/
lemma tensorMk_smul {M N : ModuleCat.{u} k} (r : k) (z : M) :
    tensorMk (N := N) (r • z) = r • tensorMk z := by
  ext v
  exact TensorProduct.smul_tmul' r z v

end TauCeti.ModuleCat
