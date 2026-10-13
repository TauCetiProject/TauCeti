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
continuous functional `ℓ` not vanishing on `e.symm (1, 0)`: keeping the second coordinate of `e`,
the map `y ↦ (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)` is still a homeomorphism `P ≃ₜ 𝕜 × F'`.
The scalars form a division ring with continuous addition and separately continuous multiplication.

## Main results

* `ContinuousLinearEquiv.exists_homeomorph_fst_eq`: a homeomorphism `P ≃ₜ 𝕜 × F'` with first
  coordinate `y ↦ ℓ (y -ᵥ z)`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 V P F' : Type*} [DivisionRing 𝕜] [TopologicalSpace 𝕜] [IsSemitopologicalRing 𝕜]
  [AddCommGroup V] [TopologicalSpace V] [Module 𝕜 V] [AddTorsor V P] [TopologicalSpace P]
  [IsTopologicalAddTorsor P] [AddCommGroup F'] [TopologicalSpace F'] [Module 𝕜 F']

/-- A continuous linear equivalence `e : V ≃L[𝕜] 𝕜 × F'` can have its first coordinate replaced by
any continuous functional `ℓ` not vanishing on `e.symm (1, 0)`. Centred at `z`, this gives a
homeomorphism `P ≃ₜ 𝕜 × F'` whose first coordinate is `y ↦ ℓ (y -ᵥ z)`. -/
theorem exists_homeomorph_fst_eq (e : V ≃L[𝕜] 𝕜 × F') (ℓ : V →L[𝕜] 𝕜)
    (hℓ : ℓ (e.symm (1, 0)) ≠ 0) (z : P) : ∃ Φ : P ≃ₜ 𝕜 × F', ∀ y, (Φ y).1 = ℓ (y -ᵥ z) := by
  set a := ℓ (e.symm (1, 0))
  have key (q : 𝕜 × F') : ℓ (e.symm q) = q.1 * a + ℓ (e.symm (0, q.2)) := by
    have hq : q = q.1 • ((1 : 𝕜), (0 : F')) + (0, q.2) := by ext <;> simp
    calc ℓ (e.symm q) = ℓ (e.symm (q.1 • ((1 : 𝕜), (0 : F')) + (0, q.2))) := by rw [← hq]
      _ = q.1 * a + ℓ (e.symm (0, q.2)) := by
        simp only [_root_.map_add, _root_.map_smul, smul_eq_mul, a]
  refine ⟨{ toFun := fun y => (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)
            invFun := fun q => e.symm ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2) +ᵥ z
            left_inv := fun y => ?_
            right_inv := fun q => ?_
            continuous_toFun := by fun_prop
            continuous_invFun := by simp only [div_eq_mul_inv]; fun_prop }, fun y => rfl⟩
  · have hy := key (e (y -ᵥ z))
    rw [e.symm_apply_apply] at hy
    have h1 : (ℓ (y -ᵥ z) - ℓ (e.symm (0, (e (y -ᵥ z)).2))) / a = (e (y -ᵥ z)).1 := by
      rw [hy, add_sub_cancel_right, mul_div_cancel_right₀ _ hℓ]
    dsimp only
    rw [h1, Prod.mk.eta, e.symm_apply_apply, vsub_vadd]
  · have hq := key ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2)
    simp only [vadd_vsub, e.apply_symm_apply]
    refine Prod.ext ?_ rfl
    rw [hq, div_mul_cancel₀ _ hℓ, sub_add_cancel]

end ContinuousLinearEquiv
