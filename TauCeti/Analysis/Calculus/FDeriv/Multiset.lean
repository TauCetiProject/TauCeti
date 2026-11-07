/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Differentiability of multiset products

Finite products of differentiable functions remain differentiable, including products with
repeated factors. These function-level statements complement Mathlib's multiset derivative
formulas and support differentiation automation for finite products in normed commutative
algebras.
-/

public section

variable {𝕜 E A ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedCommRing A] [NormedAlgebra 𝕜 A]
  {m : Multiset ι} {f : ι → E → A}

/-- A multiset product of differentiable functions is differentiable, allowing repetitions. -/
@[fun_prop]
theorem Differentiable.fun_multisetProd (hf : ∀ i ∈ m, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (fun x ↦ (m.map fun i ↦ f i x).prod) := by
  classical
  exact fun x ↦ (HasFDerivAt.multiset_prod (fun i hi ↦ (hf i hi x).hasFDerivAt)).differentiableAt

/-- The product in the function algebra of a multiset of differentiable functions is
itself differentiable. -/
@[fun_prop]
theorem Differentiable.multisetProd (hf : ∀ i ∈ m, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (m.map f).prod := by
  have he : (fun x ↦ (m.map fun i ↦ f i x).prod) = (m.map f).prod := by
    funext x
    simp only [Pi.multiset_prod_apply, Multiset.map_map, Function.comp_def]
  rw [← he]
  exact Differentiable.fun_multisetProd hf
