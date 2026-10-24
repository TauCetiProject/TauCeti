/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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
  differential does, and `TauCeti.Manifold.norm_mgradient_eq_norm_mvfderiv`: it has the same
  length as the differential.
* `TauCeti.Manifold.contMDiffAt_mgradient`: for a `C^n` metric, a function that is `C^{n+1}`
  at a point has a `C^n` gradient there.
* `TauCeti.Manifold.contMDiff_mgradient`: the gradient of a `C^{n+1}` function for a `C^n`
  metric is a `C^n` vector field.
* `TauCeti.Manifold.mdifferentiable_mgradient`: a `C²` function has a differentiable Riemannian
  gradient section.
* `TauCeti.Manifold.contMDiff_neg_mgradient`: so is the negative gradient, and
  `TauCeti.Manifold.contMDiff_neg_mgradient_one` states its `C¹` case for a `C²` function.
* `TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`: for a
  continuous metric, the differential of `f` read in a chart is locally bounded by a multiple of
  the length of the gradient. This is how coordinate estimates for `df` become metric estimates.
-/

public section

open Bundle Filter Set Topology
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

/-- The gradient has the same length as the differential it represents: the Riesz equivalence is
an isometry. -/
theorem norm_mgradient_eq_norm_mvfderiv (f : M → ℝ) (x : M) :
    ‖mgradient I f x‖ = ‖mvfderiv I f x‖ :=
  (rieszDual x).norm_map _

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

/-- The gradient satisfies the scalar product rule for differentiable functions. -/
theorem mgradient_mul {g : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ) f)
    (hg : MDifferentiable I 𝓘(ℝ) g) :
    mgradient I (f * g) = fun x ↦ f x • mgradient I g x + g x • mgradient I f x := by
  funext x
  apply ext_inner_right ℝ
  intro v
  rw [inner_mgradient, mvfderiv_mul (hf x) (hg x)]
  simp only [inner_add_left, real_inner_smul_left, inner_mgradient]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- The gradient commutes with multiplication by a real constant. -/
theorem mgradient_smul (c : ℝ) (hf : MDifferentiable I 𝓘(ℝ) f) :
    mgradient I (c • f) = c • mgradient I f := by
  funext x
  simpa [mgradient, mvfderiv_const, Pi.smul_def, smul_eq_mul] using
    congrArg (Riemannian.Tensor.rieszDual (I := I) x)
      (mvfderiv_fun_smul (a := fun _ : M ↦ c) mdifferentiableAt_const (hf x))

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

/-- For a `C^n` metric, a function which is `C^{n+1}` at a point has a `C^n` gradient there. -/
theorem contMDiffAt_mgradient {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x) :
    ContMDiffAt I I.tangent n (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x := by
  refine contMDiffAt_rieszDual x (mem_chart_source H x) fun j ↦ ?_
  have hframe := contMDiffOn_chartLocalFrame (I := I) (n := n) x j
  rw [TangentBundle.trivializationAt_baseSet] at hframe
  exact (hf.contMDiffAt_mvfderiv_apply le_rfl).comp x
    (hframe.contMDiffAt ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)))

/-- **The gradient is smooth.** For a `C^n` Riemannian metric, the gradient of a `C^{n+1}`
function is a `C^n` vector field. -/
theorem contMDiff_mgradient {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, mgradient I f x⟩ : TangentBundle I M)) :=
  fun x ↦ contMDiffAt_mgradient (hf x)

/-- A `C²` function has a differentiable Riemannian gradient section. -/
theorem mdifferentiable_mgradient {f : M → ℝ} [IsManifold I 2 M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    MDifferentiable I I.tangent
      (fun x ↦ (⟨x, mgradient I f x⟩ : TangentBundle I M)) := by
  let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  exact (contMDiff_mgradient (I := I) (n := 1)
    (by simpa only [one_add_one_eq_two] using hf)).mdifferentiable (by simp)

/-- **The negative gradient is smooth.** For a `C^n` Riemannian metric, the negative gradient of a
`C^{n+1}` function is a `C^n` vector field. -/
theorem contMDiff_neg_mgradient {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, -mgradient I f x⟩ : TangentBundle I M)) := by
  simpa only [mgradient_neg] using contMDiff_mgradient (f := -f) hf.neg

/-- `TauCeti.Manifold.contMDiff_neg_mgradient` at `n = 1`, with the smoothness order `1 + 1`
written as `2`, in the form taken by the integral-curve API. -/
theorem contMDiff_neg_mgradient_one [IsManifold I 2 M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ContMDiff I I.tangent 1 (fun y ↦ (⟨y, (-mgradient I f) y⟩ : TangentBundle I M)) :=
  have : IsManifold I (1 + 1) M := by rwa [one_add_one_eq_two]
  contMDiff_neg_mgradient (n := 1) (by rwa [one_add_one_eq_two])

/-! ### Comparison with the differential in a chart -/

/-- **The differential in a chart is controlled by the gradient.** Near `p`, the Fréchet
derivative of the coordinate expression of `f` in the extended chart at `p` is bounded by a fixed
multiple of the Riemannian length of the gradient of `f`. The constant bounds the operator norm of
the inverse of the tangent chart, measured with the metric on its target, which is locally bounded
for a continuous metric. -/
theorem eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (f : M → ℝ) (p : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 p,
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ≤ C * ‖mgradient I f y‖ := by
  obtain ⟨C, hC, hsymm⟩ :=
    eventually_norm_symmL_trivializationAt_lt E (fun x : M ↦ TangentSpace I x) p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsymm, chart_source_mem_nhds H p] with y hy hys
  by_cases hd : DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)
  swap
  · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
    positivity
  set e := trivializationAt E (TangentSpace I) p
  -- The tangent chart at `y` is `e` read at `y`, and `e.symmL ℝ y` is its inverse.
  have hmf := TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt
    (by rwa [extChartAt_source]) hd
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hys] at hmf
  have hw : ∀ w : E, fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y) w =
      mvfderiv I f y (e.symmL ℝ y w) := by
    intro w
    have h2 : e.continuousLinearMapAt ℝ y (e.symmL ℝ y w) = w :=
      e.continuousLinearMapAt_symmL (by simpa [e] using hys) w
    calc fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y) w
        = fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)
            (e.continuousLinearMapAt ℝ y (e.symmL ℝ y w)) := by rw [h2]
      _ = mvfderiv I f y (e.symmL ℝ y w) := by
        rw [mvfderiv_apply_eq_mfderiv_apply]
        exact (DFunLike.congr_fun hmf (e.symmL ℝ y w)).symm
  rw [norm_mgradient_eq_norm_mvfderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [hw]
  calc ‖mvfderiv I f y (e.symmL ℝ y w)‖ ≤ ‖mvfderiv I f y‖ * ‖e.symmL ℝ y w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖mvfderiv I f y‖ * (C * ‖w‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    _ = C * ‖mvfderiv I f y‖ * ‖w‖ := by ring

end TauCeti.Manifold
