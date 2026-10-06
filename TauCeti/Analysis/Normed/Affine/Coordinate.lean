/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Affine coordinates with a prescribed first coordinate

A continuous linear equivalence `e : V ≃L[ℝ] ℝ × F'` identifies a real normed affine space `P`
over `V`, once an origin `z` is chosen, with `ℝ × F'`. Its first coordinate can be replaced by any
continuous functional `ℓ` not vanishing on `e.symm (1, 0)`: keeping the second coordinate of `e`,
the map `y ↦ (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)` is still a homeomorphism `P ≃ₜ ℝ × F'`.

## Main results

* `TauCeti.exists_homeomorph_fst_eq`: a homeomorphism `P ≃ₜ ℝ × F'` with first coordinate
  `y ↦ ℓ (y -ᵥ z)`.
-/

public section

namespace TauCeti

variable {V P F' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- A continuous linear equivalence `e : V ≃L[ℝ] ℝ × F'` can have its first coordinate replaced by
any continuous functional `ℓ` not vanishing on `e.symm (1, 0)`. Centred at `z`, this gives a
homeomorphism `P ≃ₜ ℝ × F'` whose first coordinate is `y ↦ ℓ (y -ᵥ z)`. -/
theorem exists_homeomorph_fst_eq (e : V ≃L[ℝ] ℝ × F') (ℓ : StrongDual ℝ V)
    (hℓ : ℓ (e.symm (1, 0)) ≠ 0) (z : P) : ∃ Φ : P ≃ₜ ℝ × F', ∀ y, (Φ y).1 = ℓ (y -ᵥ z) := by
  set a := ℓ (e.symm (1, 0))
  have key (q : ℝ × F') : ℓ (e.symm q) = q.1 * a + ℓ (e.symm (0, q.2)) := by
    have hq : q = q.1 • ((1 : ℝ), (0 : F')) + (0, q.2) := by ext <;> simp
    calc ℓ (e.symm q) = ℓ (e.symm (q.1 • ((1 : ℝ), (0 : F')) + (0, q.2))) := by rw [← hq]
      _ = q.1 * a + ℓ (e.symm (0, q.2)) := by rw [map_add, map_add, map_smul, map_smul, smul_eq_mul]
  refine ⟨{ toFun := fun y => (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)
            invFun := fun q => e.symm ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2) +ᵥ z
            left_inv := fun y => ?_
            right_inv := fun q => ?_
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }, fun y => rfl⟩
  · have hy := key (e (y -ᵥ z))
    rw [e.symm_apply_apply] at hy
    have h1 : (ℓ (y -ᵥ z) - ℓ (e.symm (0, (e (y -ᵥ z)).2))) / a = (e (y -ᵥ z)).1 := by
      rw [div_eq_iff hℓ]
      linarith
    dsimp only
    rw [h1, Prod.mk.eta, e.symm_apply_apply, vsub_vadd]
  · have hq := key ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2)
    simp only [vadd_vsub, e.apply_symm_apply]
    refine Prod.ext ?_ rfl
    rw [hq, div_mul_cancel₀ _ hℓ]
    ring

end TauCeti
