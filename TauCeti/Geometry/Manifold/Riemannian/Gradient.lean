/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The gradient of a function on a Riemannian manifold

On a manifold `M` whose tangent spaces carry a Riemannian metric, the **gradient** of a function
`f : M → ℝ` at `x` is the tangent vector `grad f x` dual to the differential `df_x` through the
metric: `⟪grad f x, v⟫ = df_x v` for every tangent vector `v`. It is the fibrewise Riesz dual
`Riemannian.Tensor.rieszDual` of `df_x`.

For a `C^{n+1}` function and a `C^n` metric, the gradient is a `C^n` vector field: the evaluations
of `df` on a chart-local frame are `C^n`, and so is the Riesz dual of such a field of covectors
(`Riemannian.Tensor.contMDiffAt_rieszDual`).

## Main declarations

* `TauCeti.Manifold.riemannianGradient`: the gradient of a function.
* `TauCeti.Manifold.inner_riemannianGradient_left`: its characteristic property
  `⟪grad f x, v⟫ = df_x v`, and `TauCeti.Manifold.eq_riemannianGradient_iff`, which identifies the
  gradient from it.
* `TauCeti.Manifold.riemannianGradient_eq_zero_iff`: the gradient vanishes exactly where the
  differential does.
* `TauCeti.Manifold.contMDiff_riemannianGradient`: the gradient of a `C^{n+1}` function for a `C^n`
  metric is a `C^n` vector field.
-/

public section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

open Riemannian.Tensor

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The **gradient** of a function `f : M → ℝ` at `x` for the Riemannian metric: the tangent
vector dual to the differential `df_x`, so that `⟪grad f x, v⟫ = df_x v`. -/
noncomputable def riemannianGradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  rieszDual x (mvfderiv I f x)

variable {f : M → ℝ} {x : M}

/-- The characteristic property of the gradient: `⟪grad f x, v⟫ = df_x v`. -/
@[simp]
theorem inner_riemannianGradient_left (v : TangentSpace I x) :
    inner ℝ (riemannianGradient I f x) v = mvfderiv I f x v :=
  inner_rieszDual _ v

/-- The characteristic property of the gradient: `⟪v, grad f x⟫ = df_x v`. -/
@[simp]
theorem inner_riemannianGradient_right (v : TangentSpace I x) :
    inner ℝ v (riemannianGradient I f x) = mvfderiv I f x v := by
  rw [real_inner_comm, inner_riemannianGradient_left]

/-- A tangent vector is the gradient exactly when its inner product with every vector `v` is
`df_x v`. -/
theorem eq_riemannianGradient_iff {w : TangentSpace I x} :
    w = riemannianGradient I f x ↔ ∀ v, inner ℝ w v = mvfderiv I f x v :=
  eq_rieszDual_iff_inner_eq

/-- The differential of `f` in the direction of its gradient is the squared length of the
gradient. -/
theorem mvfderiv_apply_riemannianGradient :
    mvfderiv I f x (riemannianGradient I f x) =
      inner ℝ (riemannianGradient I f x) (riemannianGradient I f x) :=
  (inner_riemannianGradient_left _).symm

/-- The gradient vanishes exactly where the differential does. -/
@[simp]
theorem riemannianGradient_eq_zero_iff : riemannianGradient I f x = 0 ↔ mvfderiv I f x = 0 := by
  rw [riemannianGradient, LinearIsometryEquiv.map_eq_zero_iff]

/-- The gradient of `-f` is the opposite of the gradient of `f`. -/
@[simp]
theorem riemannianGradient_neg : riemannianGradient I (-f) x = -riemannianGradient I f x := by
  rw [riemannianGradient, riemannianGradient, mvfderiv_neg]
  exact (rieszDual (I := I) x).toLinearEquiv.map_neg _

/-- **The gradient is smooth.** For a `C^n` Riemannian metric, the gradient of a `C^{n+1}`
function is a `C^n` vector field. -/
theorem contMDiff_riemannianGradient {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, riemannianGradient I f x⟩ : TangentBundle I M)) :=
  fun x ↦ by
  -- `df` evaluated on the chart-local frame at `x` is `C^n` on the chart source.
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  refine contMDiffAt_rieszDual x (mem_chart_source H x) fun j ↦ ?_
  have hframe := contMDiffOn_chartLocalFrame (I := I) (n := n) x j
  rw [TangentBundle.trivializationAt_baseSet] at hframe
  exact (hf.contMDiffOn.contMDiffOn_mvfderiv_apply hopen hframe le_rfl).contMDiffAt
    (hopen.mem_nhds (mem_chart_source H x))

end TauCeti.Manifold
