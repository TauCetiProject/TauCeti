/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Restriction of scalars of vector fields

The native self-model tangent comparison takes differentiable vector fields to differentiable
vector fields over the smaller field. It preserves their manifold Lie bracket. This lets bracket
comparisons for complex Lie groups use the general vector-field statement.

## Main results

* `MDifferentiableAt.restrictScalars_vectorField`: differentiability of a restricted vector field.
* `VectorField.mlieBracket_restrictScalars`: scalar restriction preserves manifold Lie brackets.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1 and §15.2, Exercise 15.2.3, for the complex-to-real
  specialization.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

variable (R : Type*) {A : Type*}
  [NontriviallyNormedField R] [NontriviallyNormedField A] [NormedAlgebra R A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace A E] [NormedSpace R E]
  [IsScalarTower R A E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(A, E) 1 M] [IsManifold 𝓘(R, E) 1 M]

/-- A differentiable vector field remains differentiable under the native self-model
scalar comparison. -/
theorem MDifferentiableAt.restrictScalars_vectorField
    {V : ∀ y : M, TangentSpace 𝓘(A, E) y} {x : M}
    (hV : MDifferentiableAt 𝓘(A, E) 𝓘(A, E).tangent
      (fun y ↦ (V y : TangentBundle 𝓘(A, E) M)) x) :
    MDifferentiableAt 𝓘(R, E) 𝓘(R, E).tangent
      (fun y ↦ (⟨y, TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (E := E) y
        ((RestrictScalars.addEquiv R A _).symm (V y))⟩ : TangentBundle 𝓘(R, E) M)) x := by
  have hVR : MDifferentiableAt 𝓘(R, E) 𝓘(R, E).tangent
      (fun y ↦ (V y : TangentBundle 𝓘(A, E) M)) x := by
    -- Tangent charts use the tagged ModelProd E E, not the native self-model on E × E.
    simp only [mdifferentiableAt_iff, mfld_simps] at hV ⊢
    exact ⟨hV.1, hV.2.restrictScalars R⟩
  have h := ((TangentBundle.contMDiff_restrictScalarsHomeomorph R
    (𝕜' := A) M 1).mdifferentiable (by norm_num)).mdifferentiableAt.comp x hVR
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  simp only [Function.comp_apply, TangentBundle.restrictScalarsHomeomorph_apply,
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv_apply, AddEquiv.apply_symm_apply]

namespace VectorField

variable [CompleteSpace E]
  [IsManifold 𝓘(A, E) (minSmoothness A 2) M]
  [IsManifold 𝓘(R, E) (minSmoothness R 2) M]

/-- The native scalar comparison preserves the bracket of vector fields differentiable at
one point. Both fields may vary arbitrarily away from that point. -/
theorem mlieBracket_restrictScalars
    {V W : ∀ y : M, TangentSpace 𝓘(A, E) y} {x : M}
    (hV : MDifferentiableAt 𝓘(A, E) 𝓘(A, E).tangent
      (fun y ↦ (V y : TangentBundle 𝓘(A, E) M)) x)
    (hW : MDifferentiableAt 𝓘(A, E) 𝓘(A, E).tangent
      (fun y ↦ (W y : TangentBundle 𝓘(A, E) M)) x) :
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R x
        ((RestrictScalars.addEquiv R A _).symm (mlieBracket 𝓘(A, E) V W x)) =
      mlieBracket 𝓘(R, E)
        (fun y ↦ TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R y
          ((RestrictScalars.addEquiv R A _).symm (V y)))
        (fun y ↦ TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R y
          ((RestrictScalars.addEquiv R A _).symm (W y))) x := by
  apply TauCeti.eq_mlieBracket_of_mvfderiv_extChartAt
    (hV.restrictScalars_vectorField R) (hW.restrictScalars_vectorField R)
  have hchart : extChartAt 𝓘(R, E) x = extChartAt 𝓘(A, E) x := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      (ModelWithCorners.extChartAt_restrictScalars R 𝓘(A, E) x)
  rw [hchart]
  have hf : ContMDiffAt 𝓘(A, E) 𝓘(A, E) (minSmoothness A 2)
      (extChartAt 𝓘(A, E) x) x := contMDiffAt_extChartAt
  have hnear (U : ∀ y : M, TangentSpace 𝓘(A, E) y) :
      (fun y ↦ mvfderiv 𝓘(R, E) (extChartAt 𝓘(A, E) x) y
        (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R y
          ((RestrictScalars.addEquiv R A _).symm (U y)))) =ᶠ[𝓝 x]
      (fun y ↦ mvfderiv 𝓘(A, E) (extChartAt 𝓘(A, E) x) y (U y)) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(A, E)) x] with y hy
    simpa only [AddEquiv.apply_symm_apply] using
      (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)
        |>.mvfderiv_restrictScalarsSelf_apply R
          ((RestrictScalars.addEquiv R A _).symm (U y)))
  have hf' := hf.mdifferentiableAt
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) le_minSmoothness))
  simp only [MDifferentiableAt.mvfderiv_restrictScalarsSelf_apply R hf',
    (hnear W).mvfderiv_eq, (hnear V).mvfderiv_eq,
    MDifferentiableAt.mvfderiv_restrictScalarsSelf_apply R
      (TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hW),
    MDifferentiableAt.mvfderiv_restrictScalarsSelf_apply R
      (TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hV)]
  simpa only [AddEquiv.apply_symm_apply] using mvfderiv_mlieBracket hf le_rfl hV hW

end VectorField
