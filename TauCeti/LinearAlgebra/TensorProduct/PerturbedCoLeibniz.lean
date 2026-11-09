/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.LinearCombination

/-!
# The co-Leibniz rule for a perturbed homotopy

Let `D` be a linear map `X → X ⊗ X`, `τ` an involution of `X`, and `h` a map satisfying the
co-Leibniz rule along `D` with respect to the idempotent `i p` and `τ`. Let `δ` satisfy the
co-Leibniz rule with respect to the identity and `τ`. Let `h'`, `i'`, `p'` be obtained from
`h`, `i`, `p` by the perturbation identities `h' (1 + δ h) = h`, `i' + h' δ i = i`,
`p' (1 + δ h) = p`. Assume the side conditions `h' h = 0`, `h' i p = 0`, `h' τ h = 0`,
`p' h = 0` and `p' i p = p`. Then `h'` satisfies the co-Leibniz rule along `D` with respect to
`i' p'` and `τ`, provided `1 + δ h` is surjective.

## Main result

* `TauCeti.comp_perturbed_homotopy_eq`
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- The co-Leibniz rule for a perturbed homotopy `h'`, in terms of a comultiplication `D`,
from the corresponding rules for `h` and `δ`, the perturbation identities
`h' (1 + δ h) = h`, `i' + h' δ i = i`, `p' (1 + δ h) = p`, the side conditions
`h' h = 0`, `h' i p = 0`, `h' τ h = 0`, `p' h = 0`, `p' i p = p` and `τ τ = id`, and the
surjectivity of `1 + δ h`. -/
theorem comp_perturbed_homotopy_eq {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] {D : X →ₗ[R] X ⊗[R] X}
    {h h' δ τ : X →ₗ[R] X}
    {i i' : Y →ₗ[R] X} {p p' : X →ₗ[R] Y}
    (hfix : h' + h' ∘ₗ δ ∘ₗ h = h) (hih : i' + h' ∘ₗ δ ∘ₗ i = i)
    (hpfix : p' + p' ∘ₗ δ ∘ₗ h = p) (hp'h : p' ∘ₗ h = 0) (hp'π : p' ∘ₗ (i ∘ₗ p) = p)
    (hh'h : h' ∘ₗ h = 0) (hh'π : h' ∘ₗ (i ∘ₗ p) = 0) (hh'τh : h' ∘ₗ τ ∘ₗ h = 0)
    (hττ : τ ∘ₗ τ = LinearMap.id)
    (hΔh : D ∘ₗ h = (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D)
    (hΔδ : D ∘ₗ δ = (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ D)
    (hsurj : Function.Surjective (1 + δ * h : Module.End R X)) :
    D ∘ₗ h' = (TensorProduct.map h' (i' ∘ₗ p') + TensorProduct.map τ h') ∘ₗ D := by
  -- Both sides agree after precomposition with the surjective map `1 + δ h`.
  set C := TensorProduct.map h' (i' ∘ₗ p') + TensorProduct.map τ h'
  have hΔδh : D ∘ₗ δ ∘ₗ h = ((TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h)) ∘ₗ D := by
    rw [← LinearMap.comp_assoc, hΔδ, LinearMap.comp_assoc, hΔh, LinearMap.comp_assoc]
  have h1 : D ∘ₗ h' + D ∘ₗ h' ∘ₗ δ ∘ₗ h =
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D := by
    rw [← hΔh, ← LinearMap.comp_add, hfix]
  have h2 : C ∘ₗ D + C ∘ₗ D ∘ₗ δ ∘ₗ h =
      (TensorProduct.map h (i ∘ₗ p) + TensorProduct.map τ h) ∘ₗ D := by
    -- Of the eight tensor terms, four vanish by the side conditions. The remaining terms
    -- combine using the fixed-point equations for `h'`, `p'`, and `i'`.
    rw [hΔδh]
    simp only [C, LinearMap.add_comp, LinearMap.comp_add, ← LinearMap.comp_assoc,
      ← TensorProduct.map_comp, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, hp'π, hp'h, hh'π, hh'h, hh'τh,
      hττ, LinearMap.id_comp, LinearMap.comp_id,
      TensorProduct.map_zero_left, TensorProduct.map_zero_right, LinearMap.zero_comp,
      LinearMap.comp_zero, add_zero, zero_add]
    have hπ : i' ∘ₗ p + h' ∘ₗ δ ∘ₗ (i ∘ₗ p) = i ∘ₗ p := by
      simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using congrArg (· ∘ₗ p) hih
    have e1 := congrArg (fun f ↦ TensorProduct.map h' (i' ∘ₗ f) ∘ₗ D) hpfix
    have e2 := congrArg (fun f ↦ TensorProduct.map f (i' ∘ₗ p) ∘ₗ D) hfix
    have e3 := congrArg (fun f ↦ TensorProduct.map τ f ∘ₗ D) hfix
    have e4 := congrArg (fun f ↦ TensorProduct.map h f ∘ₗ D) hπ
    simp only [LinearMap.comp_add, TensorProduct.map_add_left, TensorProduct.map_add_right,
      LinearMap.add_comp] at e1 e2 e3 e4
    linear_combination (norm := abel) e1 + e2 + e3 + e4
  have key (f : X →ₗ[R] X ⊗[R] X) : f ∘ₗ (1 + δ * h : Module.End R X) = f + f ∘ₗ δ ∘ₗ h := by
    rw [Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id, LinearMap.comp_id]
  refine (LinearMap.cancel_right hsurj).mp ?_
  rw [key, key, LinearMap.comp_assoc, LinearMap.comp_assoc]
  exact h1.trans h2.symm

end TauCeti
