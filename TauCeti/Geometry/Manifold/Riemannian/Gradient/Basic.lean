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

The gradient within a subset is similarly the fibrewise Riesz dual of `mvfderivWithin`.
Its characteristic equations, uniqueness, vanishing, and neighbourhood-restriction laws require
only the pointwise Riemannian bundle structure.

For a `C^{n+1}` function and a `C^n` metric, the gradient is a `C^n` vector field: the evaluations
of `df` on a chart-local frame are `C^n`, and so is the Riesz dual of such a field of covectors
(`Riemannian.Tensor.contMDiffAt_rieszDual`).

## Main declarations

* `TauCeti.Manifold.mgradient`: the gradient of a function.
* `TauCeti.Manifold.mgradientWithin`: the gradient within a subset.
* `TauCeti.Manifold.inner_mgradient`: its characteristic property
  `⟪grad f x, v⟫ = df_x v`, and `TauCeti.Manifold.eq_mgradient_iff`, which identifies the
  gradient from it.
* `TauCeti.Manifold.mgradient_eq_zero_iff`: the gradient vanishes exactly where the
  differential does.
* `TauCeti.Manifold.contMDiff_mgradient`: the gradient of a `C^{n+1}` function for a `C^n`
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
noncomputable def mgradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  rieszDual x (mvfderiv I f x)

/-- The gradient is the fibrewise Riesz dual of the manifold derivative. -/
theorem mgradient_def (f : M → ℝ) (x : M) :
    mgradient I f x = rieszDual x (mvfderiv I f x) := by
  rw [mgradient]

variable {f : M → ℝ} {x : M}

/-- The characteristic property of the gradient: `⟪grad f x, v⟫ = df_x v`. -/
@[simp]
theorem inner_mgradient (v : TangentSpace I x) :
    inner ℝ (mgradient I f x) v = mvfderiv I f x v :=
  inner_rieszDual _ v

/-- The characteristic property of the gradient: `⟪v, grad f x⟫ = df_x v`. -/
@[simp]
theorem inner_mgradient_right (v : TangentSpace I x) :
    inner ℝ v (mgradient I f x) = mvfderiv I f x v := by
  rw [real_inner_comm, inner_mgradient]

/-- A tangent vector is the gradient exactly when its inner product with every vector `v` is
`df_x v`. -/
theorem eq_mgradient_iff {w : TangentSpace I x} :
    w = mgradient I f x ↔ ∀ v, inner ℝ w v = mvfderiv I f x v :=
  eq_rieszDual_iff_inner_eq

/-- The differential of `f` in the direction of its gradient is the squared length of the
gradient. -/
theorem mvfderiv_apply_mgradient :
    mvfderiv I f x (mgradient I f x) =
      inner ℝ (mgradient I f x) (mgradient I f x) :=
  (inner_mgradient _).symm

/-- The gradient vanishes exactly where the differential does. -/
@[simp]
theorem mgradient_eq_zero_iff : mgradient I f x = 0 ↔ mvfderiv I f x = 0 := by
  rw [mgradient, LinearIsometryEquiv.map_eq_zero_iff]

/-- The gradient of a constant function is zero. -/
@[simp]
theorem mgradient_const (c : ℝ) : mgradient I (fun _ : M ↦ c) = 0 := by
  funext x
  simp only [mgradient, mvfderiv_const, LinearIsometryEquiv.map_zero, Pi.zero_apply]

/-- The gradient is additive on differentiable functions. -/
theorem mgradient_add {g : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ) f)
    (hg : MDifferentiable I 𝓘(ℝ) g) :
    mgradient I (f + g) = mgradient I f + mgradient I g := by
  funext x
  simp [mgradient, mvfderiv_add (hf x) (hg x)]

/-- The gradient commutes with multiplication by a real constant. -/
theorem mgradient_smul (c : ℝ) (hf : MDifferentiable I 𝓘(ℝ) f) :
    mgradient I (c • f) = c • mgradient I f := by
  funext x
  simpa [mgradient, mvfderiv_const, Pi.smul_def, smul_eq_mul] using
    congrArg (Riemannian.Tensor.rieszDual (I := I) x)
      (mvfderiv_smul (a := fun _ : M ↦ c) mdifferentiableAt_const (hf x))

/-- The gradient of `-f` is the opposite of the gradient of `f`. -/
@[simp]
theorem mgradient_neg : mgradient I (-f) x = -mgradient I f x := by
  rw [mgradient, mgradient, mvfderiv_neg]
  exact (rieszDual (I := I) x).toLinearEquiv.map_neg _

variable {s : Set M}

variable (I) in
/-- The Riemannian gradient within a set, obtained by taking the fibrewise Riesz dual of the
manifold derivative within that set. Like the derivative, it is total. -/
noncomputable def mgradientWithin (f : M → ℝ) (s : Set M)
    (x : M) : TangentSpace I x :=
  rieszDual x (mvfderivWithin I f s x)

/-- The gradient within a set is the Riesz dual of the relative differential. -/
theorem mgradientWithin_def (f : M → ℝ) (s : Set M) (x : M) :
    mgradientWithin I f s x = rieszDual x (mvfderivWithin I f s x) := (rfl)

/-- Pairing the relative gradient with a tangent vector evaluates the relative differential. -/
@[simp]
theorem inner_mgradientWithin_left (v : TangentSpace I x) :
    inner ℝ (mgradientWithin I f s x) v = mvfderivWithin I f s x v := by
  rw [mgradientWithin_def, inner_rieszDual]

/-- The symmetric form of the relative gradient's characteristic equation. -/
@[simp]
theorem inner_mgradientWithin_right (v : TangentSpace I x) :
    inner ℝ v (mgradientWithin I f s x) = mvfderivWithin I f s x v := by
  rw [real_inner_comm, inner_mgradientWithin_left]

/-- On the whole manifold the relative gradient is the gradient. -/
@[simp]
theorem mgradientWithin_univ (f : M → ℝ) :
    mgradientWithin I f univ = mgradient I f := by
  funext x
  apply ext_inner_right ℝ
  intro v
  simp only [inner_mgradientWithin_left, inner_mgradient,
    mvfderivWithin_univ]

/-- The relative gradient is uniquely characterized by its inner products. -/
theorem eq_mgradientWithin_iff {w : TangentSpace I x} :
    w = mgradientWithin I f s x ↔
      ∀ v, inner ℝ w v = mvfderivWithin I f s x v := by
  rw [mgradientWithin_def]
  exact eq_rieszDual_iff_inner_eq

/-- The relative gradient vanishes exactly where the relative differential vanishes. -/
@[simp]
theorem mgradientWithin_eq_zero_iff :
    mgradientWithin I f s x = 0 ↔ mvfderivWithin I f s x = 0 := by
  rw [mgradientWithin_def, LinearIsometryEquiv.map_eq_zero_iff]

/-- Restriction to a neighbourhood does not change the gradient. -/
theorem mgradientWithin_of_mem_nhds (hs : s ∈ 𝓝 x) :
    mgradientWithin I f s x = mgradient I f x := by
  apply ext_inner_right ℝ
  intro v
  simp only [inner_mgradientWithin_left, inner_mgradient,
    mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hs]

/-- **The gradient is smooth.** For a `C^n` Riemannian metric, the gradient of a `C^{n+1}`
function is a `C^n` vector field. -/
theorem contMDiff_mgradient {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, mgradient I f x⟩ : TangentBundle I M)) :=
  fun x ↦ by
  -- `df` evaluated on the chart-local frame at `x` is `C^n` on the chart source.
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  refine contMDiffAt_rieszDual x (mem_chart_source H x) fun j ↦ ?_
  have hframe := contMDiffOn_chartLocalFrame (I := I) (n := n) x j
  rw [TangentBundle.trivializationAt_baseSet] at hframe
  exact (hf.contMDiffOn.contMDiffOn_mvfderiv_apply hopen hframe le_rfl).contMDiffAt
    (hopen.mem_nhds (mem_chart_source H x))

end TauCeti.Manifold
