/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# The Lie derivative commutes with the exterior derivative

For a smooth form `φ` and a smooth vector field `V` on a manifold,

`d (L_V φ) = L_V (d φ)` (`TauCeti.SmoothForm.mextDeriv_mlieDerivForm`).

This follows from Cartan's formula `L_V = ι_V d + d ι_V`
(`TauCeti.SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add`) and `d ∘ d = 0`
(`TauCeti.SmoothForm.mextDeriv_mextDeriv`): both sides equal `d ι_V d φ`. In particular the Lie
derivative of a closed smooth form along a smooth vector field is closed.

## Main results

* `TauCeti.SmoothForm.mextDeriv_mlieDerivForm`: `d (L_V φ) = L_V (d φ)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 14.35
  (Cartan's formula) and Corollary 14.36 (the Lie derivative commutes with `d`).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The exterior derivative commutes with the Lie derivative**, `d (L_V φ) = L_V (d φ)`, for a
smooth form `φ` and a smooth vector field `V`. -/
theorem mextDeriv_mlieDerivForm (φ : SmoothForm I M F (k + 1)) {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (fun y ↦ (V y : TangentBundle I M))) :
    mextDeriv (mlieDerivForm V φ.val) = mlieDerivForm V (mextDeriv φ.val) := by
  -- The two terms `ι_V dφ` and `ι_V φ` of Cartan's formula, as smooth forms.
  set dφ := mextDerivₗ I (k + 1) φ
  have ha : IsSmoothForm I ∞ (RoughForm.interior V dφ.val) := dφ.isSmoothForm.interior hV
  have hb : IsSmoothForm I ∞ (RoughForm.interior V (φ.val : RoughForm I M F (k + 1))) :=
    φ.isSmoothForm.interior hV
  set a : SmoothForm I M F (k + 1) := ⟨_, ha.mem_smoothBundleForms⟩
  set b : SmoothForm I M F k := ⟨_, hb.mem_smoothBundleForms⟩
  -- `L_V φ = ι_V dφ + d ι_V φ`, whose exterior derivative is `d ι_V dφ`.
  have hL : mlieDerivForm V φ.val = (a + mextDerivₗ I k b).val := by
    rw [SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add (hV.mdifferentiable (by simp)),
      Submodule.coe_add, mextDerivₗ_apply]
    simp only [a, b, dφ, mextDerivₗ_apply]
  -- `L_V dφ = ι_V ddφ + d ι_V dφ = d ι_V dφ`.
  have hR : mlieDerivForm V (mextDeriv φ.val) = (mextDerivₗ I (k + 1) a).val := by
    rw [mextDerivₗ_apply, ← mextDerivₗ_apply I (k + 1) φ,
      TauCeti.mlieDerivForm_eq_interior_mextDeriv_add dφ.mdifferentiable
        (hV.mdifferentiable (by simp)), mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv]
    simp [a, dφ]
  rw [hL, hR, ← mextDerivₗ_apply, map_add, Submodule.coe_add]
  simp only [mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv, add_zero]

end SmoothForm

end TauCeti
