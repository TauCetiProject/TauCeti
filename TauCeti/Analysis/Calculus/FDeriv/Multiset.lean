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
algebras. Pointwise, within-set and on-set forms provide the same automation for
local differentiability goals.
-/

public section

variable {𝕜 E A ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedCommRing A] [NormedAlgebra 𝕜 A]
  {m : Multiset ι} {f : ι → E → A} {x : E} {s : Set E}

/-- A multiset product of functions differentiable within a set is differentiable there. -/
@[fun_prop]
theorem DifferentiableWithinAt.fun_multisetProd
    (hf : ∀ i ∈ m, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (m.map fun i ↦ f i y).prod) s x := by
  classical
  exact (HasFDerivWithinAt.multiset_prod
    (fun i hi ↦ (hf i hi).hasFDerivWithinAt)).differentiableWithinAt

/-- A multiset product of functions differentiable at a point is differentiable there. -/
@[fun_prop]
theorem DifferentiableAt.fun_multisetProd (hf : ∀ i ∈ m, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (fun y ↦ (m.map fun i ↦ f i y).prod) x := by
  classical
  exact (HasFDerivAt.multiset_prod (fun i hi ↦ (hf i hi).hasFDerivAt)).differentiableAt

/-- A multiset product of functions differentiable on a set is differentiable on that set. -/
@[fun_prop]
theorem DifferentiableOn.fun_multisetProd (hf : ∀ i ∈ m, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (fun x ↦ (m.map fun i ↦ f i x).prod) s :=
  fun x hx ↦ DifferentiableWithinAt.fun_multisetProd (fun i hi ↦ hf i hi x hx)

/-- A multiset product of differentiable functions is differentiable, allowing repetitions. -/
@[fun_prop]
theorem Differentiable.fun_multisetProd (hf : ∀ i ∈ m, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (fun x ↦ (m.map fun i ↦ f i x).prod) :=
  fun x ↦ DifferentiableAt.fun_multisetProd (fun i hi ↦ hf i hi x)

/-- The product in the function algebra preserves differentiability within a set at a point. -/
@[fun_prop]
theorem DifferentiableWithinAt.multisetProd
    (hf : ∀ i ∈ m, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (m.map f).prod s x := by
  have he : (fun x ↦ (m.map fun i ↦ f i x).prod) = (m.map f).prod := by
    funext x
    simp only [Pi.multiset_prod_apply, Multiset.map_map, Function.comp_def]
  rw [← he]
  exact DifferentiableWithinAt.fun_multisetProd hf

/-- The product in the function algebra preserves differentiability at a point. -/
@[fun_prop]
theorem DifferentiableAt.multisetProd (hf : ∀ i ∈ m, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (m.map f).prod x := by
  have he : (fun x ↦ (m.map fun i ↦ f i x).prod) = (m.map f).prod := by
    funext x
    simp only [Pi.multiset_prod_apply, Multiset.map_map, Function.comp_def]
  rw [← he]
  exact DifferentiableAt.fun_multisetProd hf

/-- The product in the function algebra preserves differentiability on a set. -/
@[fun_prop]
theorem DifferentiableOn.multisetProd (hf : ∀ i ∈ m, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (m.map f).prod s :=
  fun x hx ↦ DifferentiableWithinAt.multisetProd (fun i hi ↦ hf i hi x hx)

/-- The product in the function algebra of differentiable functions is differentiable. -/
@[fun_prop]
theorem Differentiable.multisetProd (hf : ∀ i ∈ m, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (m.map f).prod :=
  fun x ↦ DifferentiableAt.multisetProd (fun i hi ↦ hf i hi x)
