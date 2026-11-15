/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of products

A family of exact pairs `Xᵢ → Yᵢ → Zᵢ` gives an exact pair `∏ᵢ Xᵢ → ∏ᵢ Yᵢ → ∏ᵢ Zᵢ` of
componentwise maps. This is the exactness of arbitrary products of abelian groups or modules,
used for instance to pass from a levelwise exact sequence of towers to the exact sequence of the
products of their terms.
-/

public section

/-- Products of exact pairs are exact: if `Xᵢ → Yᵢ → Zᵢ` is exact for every `i`, then so is the
componentwise pair `∏ᵢ Xᵢ → ∏ᵢ Yᵢ → ∏ᵢ Zᵢ`. -/
theorem Function.Exact.piMap {ι : Type*} {X Y Z : ι → Type*} [∀ i, Zero (Z i)]
    {f : ∀ i, X i → Y i} {g : ∀ i, Y i → Z i} (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (Pi.map f) (Pi.map g) := by
  intro y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · choose x hx using fun i ↦ (h i (y i)).1 (congrFun hy i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    exact funext fun i ↦ (h i).apply_apply_eq_zero (x i)
