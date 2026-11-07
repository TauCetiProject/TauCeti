/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Affine coordinates with a prescribed first coordinate

A continuous linear equivalence `e : V ≃L[𝕜] 𝕜 × F'` identifies a topological affine space `P`
over `V`, once an origin `z` is chosen, with `𝕜 × F'`. Its first coordinate can be replaced by any
continuous functional `ℓ` taking a unit value on `e.symm (1, 0)`: keeping the second coordinate of
`e`, the map `y ↦ (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)` is still a homeomorphism `P ≃ₜ 𝕜 × F'`.
The scalars form a ring with continuous addition and separately continuous multiplication.

## Main results

* `ContinuousLinearEquiv.exists_homeomorph_apply_eq`: the map `y ↦ (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)`
  is a homeomorphism `P ≃ₜ 𝕜 × F'`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 V P F' : Type*} [Ring 𝕜] [TopologicalSpace 𝕜] [IsSemitopologicalRing 𝕜]
  [AddCommGroup V] [TopologicalSpace V] [Module 𝕜 V] [AddTorsor V P] [TopologicalSpace P]
  [IsTopologicalAddTorsor P] [AddCommGroup F'] [TopologicalSpace F'] [Module 𝕜 F']

/-- A continuous linear equivalence `e : V ≃L[𝕜] 𝕜 × F'` can have its first coordinate replaced by
any continuous functional `ℓ` taking a unit value on `e.symm (1, 0)`. Centred at `z`, the map
`y ↦ (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)` is a homeomorphism `P ≃ₜ 𝕜 × F'`. -/
theorem exists_homeomorph_apply_eq (e : V ≃L[𝕜] 𝕜 × F') (ℓ : V →L[𝕜] 𝕜)
    (hℓ : IsUnit (ℓ (e.symm (1, 0)))) (z : P) :
    ∃ Φ : P ≃ₜ 𝕜 × F', ∀ y, Φ y = (ℓ (y -ᵥ z), (e (y -ᵥ z)).2) := by
  obtain ⟨u, hu⟩ := hℓ
  have key (q : 𝕜 × F') : ℓ (e.symm q) = q.1 * u + ℓ (e.symm (0, q.2)) := by
    conv_lhs => rw [show q = q.1 • ((1 : 𝕜), (0 : F')) + (0, q.2) by ext <;> simp]
    simp only [_root_.map_add, _root_.map_smul, smul_eq_mul, hu]
  refine ⟨{ toFun y := (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)
            invFun q := e.symm ((q.1 - ℓ (e.symm (0, q.2))) * ↑u⁻¹, q.2) +ᵥ z
            left_inv y := ?_
            right_inv q := ?_
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }, fun _ => rfl⟩
  · have hy := key (e (y -ᵥ z))
    rw [e.symm_apply_apply] at hy
    simp [hy]
  · simp only [vadd_vsub, e.apply_symm_apply]
    rw [key]
    simp

end ContinuousLinearEquiv
