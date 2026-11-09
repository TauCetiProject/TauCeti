/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The unit gradient

On a Riemannian manifold, the gradient of a function `f : M → ℝ` scaled to unit length,
`NormedSpace.normalize (mgradient I f x)`, is the unit normal at a regular point `x` to the level
set of `f` through `x`, pointing towards increasing `f`. Its inner product with a tangent vector
`v` is `df_x v / ‖grad f x‖`, so it is orthogonal to the kernel of `df_x` and `df_x` takes the
value `‖grad f x‖` on it. For a `C^{n+1}` function and a `C^n` metric it is a `C^n` vector field
near every point where the gradient does not vanish.

## Main results

* `TauCeti.Manifold.inner_normalize_mgradient`: `⟪grad f x / ‖grad f x‖, v⟫ = df_x v / ‖grad f x‖`.
* `TauCeti.Manifold.mvfderiv_normalize_mgradient`: `df_x (grad f x / ‖grad f x‖) = ‖grad f x‖`.
* `TauCeti.Manifold.contMDiffAt_normalize_mgradient`: the unit gradient of a function that is
  `C^{n+1}` at a point with nonzero gradient is `C^n` at that point, for a `C^n` metric.
* `TauCeti.Manifold.contMDiff_normalize_mgradient`: the unit gradient of a `C^{n+1}` function with
  nowhere vanishing gradient is a `C^n` vector field.
-/

public section

open Bundle
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {f : M → ℝ} {x : M}

/-- The inner product of the unit gradient with a tangent vector `v` is `df_x v / ‖grad f x‖`. -/
theorem inner_normalize_mgradient (v : TangentSpace I x) :
    ⟪NormedSpace.normalize (mgradient I f x), v⟫_ℝ = ‖mgradient I f x‖⁻¹ * mvfderiv I f x v := by
  rw [NormedSpace.normalize, real_inner_smul_left, inner_mgradient]

/-- The differential of `f` takes the value `‖grad f x‖` on the unit gradient. -/
theorem mvfderiv_normalize_mgradient :
    mvfderiv I f x (NormedSpace.normalize (mgradient I f x)) = ‖mgradient I f x‖ := by
  rw [← inner_mgradient, real_inner_comm, inner_normalize_mgradient, mvfderiv_apply_mgradient,
    real_inner_self_eq_norm_sq]
  rcases eq_or_ne ‖mgradient I f x‖ 0 with h | h
  · simp [h]
  · field_simp

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- For a `C^n` metric, the unit gradient of a function that is `C^{n+1}` at a point where its
gradient does not vanish is `C^n` at that point. -/
theorem contMDiffAt_normalize_mgradient (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hx : mgradient I f x ≠ 0) :
    ContMDiffAt I I.tangent n
      (fun y ↦ (⟨y, NormedSpace.normalize (mgradient I f y)⟩ : TangentBundle I M)) x := by
  have hgrad := contMDiffAt_mgradient hf
  have hsq : ContMDiffAt I 𝓘(ℝ) n (fun y ↦ ⟪mgradient I f y, mgradient I f y⟫_ℝ) x :=
    ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun y : M ↦ TangentSpace I y) (b := id)
      hgrad hgrad
  have hne : ⟪mgradient I f x, mgradient I f x⟫_ℝ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  have hnorm : ContMDiffAt I 𝓘(ℝ) n (fun y ↦ ‖mgradient I f y‖) x := by
    simpa only [Function.comp_def, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using
      (Real.contDiffAt_sqrt hne).comp_contMDiffAt
        (f := fun y ↦ ⟪mgradient I f y, mgradient I f y⟫_ℝ) hsq
  exact (hnorm.inv₀ (norm_ne_zero_iff.mpr hx)).smul_section hgrad

/-- For a `C^n` metric, the unit gradient of a `C^{n+1}` function with nowhere vanishing gradient
is a `C^n` vector field. -/
theorem contMDiff_normalize_mgradient (hf : ContMDiff I 𝓘(ℝ) (n + 1) f)
    (hx : ∀ x, mgradient I f x ≠ 0) :
    ContMDiff I I.tangent n
      (fun y ↦ (⟨y, NormedSpace.normalize (mgradient I f y)⟩ : TangentBundle I M)) :=
  fun x ↦ contMDiffAt_normalize_mgradient (hf x) (hx x)

end TauCeti.Manifold
