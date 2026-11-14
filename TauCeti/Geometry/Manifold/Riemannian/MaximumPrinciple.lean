/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

import TauCeti.Analysis.Calculus.ContDiff.Differentiable

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

* `TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin`: the second-derivative test.
* `TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.laplaceBeltrami_nonneg_of_isLocalMin`: the sign of `Δ` at local extrema.
* `TauCeti.Manifold.exists_forall_ge_and_laplaceBeltrami_nonpos`,
  `TauCeti.Manifold.exists_forall_le_and_laplaceBeltrami_nonneg`: on a compact manifold a `C²`
  function attains its maximum at a point where `Δ` is nonpositive, and its minimum at a point
  where `Δ` is nonnegative.
* `TauCeti.Manifold.le_of_le_laplaceBeltrami_of_laplaceBeltrami_le`: the comparison principle.
* `TauCeti.Manifold.le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami`: the bound
  `u ≤ max (b / a) 0` for a subsolution of `a u² - b u ≤ Δu` with `a > 0`.

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

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) (v : TangentSpace I x) : hessian I f x v v ≤ 0 := by
  have hmax' : IsLocalMax (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMax f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmax
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))),
    criticalHessian_def]
  exact fderiv_fderiv_self_nonpos_of_isLocalMax
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmax' v

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
  exact fderiv_fderiv_self_nonneg_of_isLocalMin
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmin' v

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the
Laplace–Beltrami operator `Δ = div ∘ grad` is nonnegative. -/
theorem laplaceBeltrami_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) : 0 ≤ laplaceBeltrami I f x := by
  rw [laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Finset.sum_nonneg fun i _ ↦ hessian_self_nonneg_of_isLocalMin hf hmin _

/-- On a compact boundaryless Riemannian manifold, a `C²` function attains its maximum at a point
where its Laplace–Beltrami operator `Δ = div ∘ grad` is nonpositive. -/
theorem exists_forall_ge_and_laplaceBeltrami_nonpos [CompactSpace M] [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ∃ x₀, (∀ y, f y ≤ f x₀) ∧ laplaceBeltrami I f x₀ ≤ 0 := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuous.continuousOn
  exact ⟨x₀, fun y ↦ hx₀ (Set.mem_univ y),
    laplaceBeltrami_nonpos_of_isLocalMax hf.contMDiffAt (hx₀.isLocalMax Filter.univ_mem)⟩

/-- On a compact boundaryless Riemannian manifold, a `C²` function attains its minimum at a point
where its Laplace–Beltrami operator `Δ = div ∘ grad` is nonnegative. -/
theorem exists_forall_le_and_laplaceBeltrami_nonneg [CompactSpace M] [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ∃ x₀, (∀ y, f x₀ ≤ f y) ∧ 0 ≤ laplaceBeltrami I f x₀ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  exact ⟨x₀, fun y ↦ hx₀ (Set.mem_univ y),
    laplaceBeltrami_nonneg_of_isLocalMin hf.contMDiffAt (hx₀.isLocalMin Filter.univ_mem)⟩

/-- **The comparison principle** for semilinear equations `Δ u = h(x, u)` on a compact
boundaryless Riemannian manifold, with `h(x, ·)` strictly increasing for every `x`: a `C²`
subsolution `h(x, u) ≤ Δ u` lies below a `C²` supersolution `Δ v ≤ h(x, v)`. -/
theorem le_of_le_laplaceBeltrami_of_laplaceBeltrami_le [CompactSpace M] {h : M → ℝ → ℝ}
    (hh : ∀ x, StrictMono (h x)) {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hsub : ∀ x, h x (u x) ≤ laplaceBeltrami I u x)
    (hsuper : ∀ x, laplaceBeltrami I v x ≤ h x (v x)) : u ≤ v := by
  intro y
  have : Nonempty M := ⟨y⟩
  -- At a maximum `x₀` of `u - v`, the Laplacian of `u - v` is nonpositive.
  obtain ⟨x₀, hx₀, hmax⟩ := exists_forall_ge_and_laplaceBeltrami_nonpos (f := u - v) (hu.sub hv)
  rw [laplaceBeltrami_sub I hu hv] at hmax
  -- Hence `h x₀ (u x₀) ≤ h x₀ (v x₀)`, so `u x₀ ≤ v x₀` by strict monotonicity.
  have hle : u x₀ ≤ v x₀ :=
    (hh x₀).le_iff_le.1 (by linarith [hsub x₀, hsuper x₀])
  have hy : u y - v y ≤ u x₀ - v x₀ := hx₀ y
  linarith

/-- **The maximum principle bound for a quadratic subsolution.** On a compact boundaryless
Riemannian manifold, a `C²` function `u` with `a u² - b u ≤ Δu` and `a > 0` satisfies
`u ≤ max (b / a) 0`. For instance a subsolution of `-Δu / 2 + (r / 4) (u - 1) u ≤ k u` with
`r > 0` and `k ≥ 0` is at most `1 + 4 k / r`. -/
theorem le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami [CompactSpace M] {u : M → ℝ}
    {a b : ℝ} (ha : 0 < a) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (h : ∀ x, a * u x ^ 2 - b * u x ≤ laplaceBeltrami I u x) (x : M) :
    u x ≤ max (b / a) 0 := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨x₀, hx₀, hΔ⟩ := exists_forall_ge_and_laplaceBeltrami_nonpos hu
  refine (hx₀ x).trans ?_
  rcases le_or_gt (u x₀) 0 with hu₀ | hu₀
  · exact hu₀.trans (le_max_right _ _)
  -- At the maximum `Δu ≤ 0`, so `(a u) u ≤ b u`, and `u > 0` there.
  have hle : u x₀ * a * u x₀ ≤ b * u x₀ := by linarith [h x₀]
  exact le_max_of_le_left ((le_div_iff₀ ha).2 (le_of_mul_le_mul_right hle hu₀))

end TauCeti.Manifold
