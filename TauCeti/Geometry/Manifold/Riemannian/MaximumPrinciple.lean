/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The maximum principle for the Laplace–Beltrami operator

On a boundaryless Riemannian manifold, this file proves the pointwise second-derivative test for
the Riemannian Hessian and the Laplace–Beltrami operator `Δ = div ∘ grad`, and the resulting
comparison principle for semilinear elliptic equations on a compact manifold.

At a critical point of a `C²` function the Levi-Civita correction term of the Hessian vanishes,
so the Riemannian Hessian is the ordinary second derivative of the function read in the
preferred chart. Consequently the Hessian is negative semidefinite at a local maximum and
positive semidefinite at a local minimum, and the same holds for its trace `Δ`.

On a compact boundaryless manifold, evaluating at a maximum of `u - v` gives the comparison
principle: if `h(x, ·)` is strictly increasing for every `x`, a subsolution
`h(x, u) ≤ Δ u` lies below a supersolution `Δ v ≤ h(x, v)`. In particular a semilinear equation
`Δ u = h(x, u)` with strictly increasing nonlinearity has at most one `C²` solution. This is the
uniqueness mechanism for the curvature equation of conformal metrics on closed surfaces.

## Main results

* `TauCeti.Manifold.hessian_eq_criticalHessian`: at a critical point, the Hessian is the critical
  Hessian, the second derivative of the coordinate expression in the preferred chart.
* `TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin`: the second-derivative test.
* `TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.laplaceBeltrami_nonneg_of_isLocalMin`: the sign of `Δ` at local extrema.
* `TauCeti.Manifold.le_of_le_laplaceBeltrami_of_laplaceBeltrami_le`: the comparison principle.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Chapter 3 (the classical maximum principle).
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47 (comparison of sub- and supersolutions on a compact manifold).
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- On the source of the preferred chart at `x`, the derivative of `extChartAt I x` sends the
extension `FiberBundle.extend E w` of a tangent vector `w` at `x` back to `w`. -/
private theorem mfderiv_extChartAt_extend {y : M} (w : TangentSpace I x)
    (hy : y ∈ (chartAt H x).source) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (FiberBundle.extend E w y) = w := by
  set t := trivializationAt E (TangentSpace I) x
  have hyt : y ∈ t.baseSet := by simpa [t] using hy
  -- `FiberBundle.extend E w` is the inverse trivialization at `x` applied to the coordinate of `w`.
  have hext : FiberBundle.extend E w y = t.symmL ℝ y (t ⟨x, w⟩).2 := by
    rw [Trivialization.symmL_apply (R := ℝ) t hyt]
    rfl
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy, hext]
  exact (t.continuousLinearMapAt_symmL hyt _).trans
    ((t.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (FiberBundle.mem_baseSet_trivializationAt' x) w).symm.trans
      (continuousLinearMapAt_trivializationAt_self x w))

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Near `x`, the derivative of a `C¹` function `f` along the extension of a tangent vector `w`
at `x` is the derivative of the coordinate expression of `f` along `w`, read through the
preferred chart. -/
private theorem mvfderiv_extend_eventuallyEq (hf : ContMDiffAt I 𝓘(ℝ) 1 f x)
    (w : TangentSpace I x) :
    (fun y ↦ mvfderiv I f y (FiberBundle.extend E w y)) =ᶠ[𝓝 x]
      (fun z ↦ fderiv ℝ (f ∘ (extChartAt I x).symm) z w) ∘ extChartAt I x := by
  have hdF : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y) :=
    (continuousAt_extChartAt x).eventually
      ((hf.contDiffAt_comp_extChartAt_symm.eventually (by simp)).mono
        fun z hz ↦ hz.differentiableAt (by simp))
  filter_upwards [chart_source_mem_nhds H x, hdF] with y hy hdy
  rw [Function.comp_apply, mvfderiv_apply_eq_mfderiv_apply,
    mfderiv_eq_fderiv_comp_mfderiv_extChartAt (by simpa using hy) hdy]
  exact congrArg _ (mfderiv_extChartAt_extend w hy)

/-- At a critical point `x` of a `C²` function `f` on a boundaryless Riemannian manifold, the
Riemannian Hessian of `f` is the critical Hessian `TauCeti.criticalHessian`, the second Fréchet
derivative of the coordinate expression `f ∘ (extChartAt I x).symm` at the chart image of `x`. -/
theorem hessian_eq_criticalHessian (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    hessian I f x v w = criticalHessian I f x v w := by
  -- At a critical point, the Hessian is the derivative of `df` along an extension of `w`.
  have h := hessian_apply_eq_mvfderiv_sub x hf (FiberBundle.extend E v) (FiberBundle.extend E w)
    (FiberBundle.mdifferentiableAt_extend I E w)
  simp only [FiberBundle.extend_apply_self, hcrit, zero_apply, sub_zero] at h
  rw [h, criticalHessian_def]
  set φ := extChartAt I x
  set F := f ∘ φ.symm
  -- Regard `w` as a vector of the model space `E`, so the chart computations typecheck in `E`.
  obtain ⟨e, rfl⟩ : ∃ e : E, e = w := ⟨w, rfl⟩
  -- Read through the chart, that derivative is the derivative of `z ↦ dF(z) w` at `φ x`.
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (φ x) :=
    (hf.contDiffAt_comp_extChartAt_symm.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hH : DifferentiableAt ℝ (fun z ↦ fderiv ℝ F z e) (φ x) :=
    hdF.clm_apply (differentiableAt_const e)
  have hφ : HasMFDerivAt I 𝓘(ℝ, E) φ x (mfderiv I 𝓘(ℝ, E) φ x) :=
    (mdifferentiableAt_extChartAt (mem_chart_source H x)).hasMFDerivAt
  have hcomp := (hH.hasFDerivAt.hasMFDerivAt.comp x hφ).congr_of_eventuallyEq
    (mvfderiv_extend_eventuallyEq (hf.of_le (by norm_num)) e)
  rw [mvfderiv_apply_eq_mfderiv_apply, hcomp.mfderiv, mfderiv_extChartAt_self]
  -- The remaining tangent-space casts of the chain rule are identities.
  change fderiv ℝ (fun z ↦ fderiv ℝ F z e) (φ x) v = _
  rw [fderiv_clm_apply hdF (differentiableAt_const e)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact ContinuousLinearMap.flip_apply _ _ _

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) (v : TangentSpace I x) : hessian I f x v v ≤ 0 := by
  have hmax' : IsLocalMax (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMax f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmax
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))),
    criticalHessian_def]
  exact fderiv_fderiv_self_nonpos_of_isLocalMax hf.contDiffAt_comp_extChartAt_symm hmax' v

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the
Laplace–Beltrami operator `Δ = div ∘ grad` is nonpositive. -/
theorem laplaceBeltrami_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) : laplaceBeltrami I f x ≤ 0 := by
  rw [laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Finset.sum_nonpos fun i _ ↦ hessian_self_nonpos_of_isLocalMax hf hmax _

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
positive semidefinite. -/
theorem hessian_self_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) (v : TangentSpace I x) : 0 ≤ hessian I f x v v := by
  have hmin' : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmin
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmin.mem_criticalPoints (I := I))),
    criticalHessian_def]
  exact fderiv_fderiv_self_nonneg_of_isLocalMin hf.contDiffAt_comp_extChartAt_symm hmin' v

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the
Laplace–Beltrami operator `Δ = div ∘ grad` is nonnegative. -/
theorem laplaceBeltrami_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) : 0 ≤ laplaceBeltrami I f x := by
  rw [laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Finset.sum_nonneg fun i _ ↦ hessian_self_nonneg_of_isLocalMin hf hmin _

/-- **The comparison principle** for semilinear equations `Δ u = h(x, u)` on a compact
boundaryless Riemannian manifold, with `h(x, ·)` strictly increasing for every `x`: a `C²`
subsolution `h(x, u) ≤ Δ u` lies below a `C²` supersolution `Δ v ≤ h(x, v)`. -/
theorem le_of_le_laplaceBeltrami_of_laplaceBeltrami_le [CompactSpace M] {h : M → ℝ → ℝ}
    (hh : ∀ x, StrictMono (h x)) {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hsub : ∀ x, h x (u x) ≤ laplaceBeltrami I u x)
    (hsuper : ∀ x, laplaceBeltrami I v x ≤ h x (v x)) : u ≤ v := by
  intro y
  -- At a maximum `x₀` of `u - v`, the Laplacian of `u - v` is nonpositive.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (hu.continuous.sub hv.continuous).continuousOn
  have hmax : laplaceBeltrami I (u - v) x₀ ≤ 0 :=
    laplaceBeltrami_nonpos_of_isLocalMax (hu.sub hv).contMDiffAt (hx₀.isLocalMax Filter.univ_mem)
  rw [laplaceBeltrami_sub I hu hv] at hmax
  -- Hence `h x₀ (u x₀) ≤ h x₀ (v x₀)`, so `u x₀ ≤ v x₀` by strict monotonicity.
  have hle : u x₀ ≤ v x₀ :=
    (hh x₀).le_iff_le.1 (by linarith [hsub x₀, hsuper x₀])
  have hy : u y - v y ≤ u x₀ - v x₀ := hx₀ (Set.mem_univ y)
  linarith

end TauCeti.Manifold
