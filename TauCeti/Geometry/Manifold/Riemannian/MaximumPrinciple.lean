/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

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
* `TauCeti.Manifold.exists_forall_le_and_laplaceBeltrami_nonpos`: on a compact manifold a `C²`
  function attains its maximum at a point where `Δ` is nonpositive.
* `TauCeti.Manifold.le_of_le_laplaceBeltrami_of_laplaceBeltrami_le`: the comparison principle.
* `TauCeti.Manifold.le_one_add_mul_div_of_laplaceBeltrami_le`: the bound `u ≤ 1 + 4 k / r` for a
  subsolution of `-Δu / 2 + (r / 4) (u - 1) u ≤ k u`.

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

/-- On a compact boundaryless Riemannian manifold, a `C²` function attains its maximum at a point
where its Laplace–Beltrami operator `Δ = div ∘ grad` is nonpositive. -/
theorem exists_forall_le_and_laplaceBeltrami_nonpos [CompactSpace M] [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ∃ x₀, (∀ y, f y ≤ f x₀) ∧ laplaceBeltrami I f x₀ ≤ 0 := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuous.continuousOn
  exact ⟨x₀, fun y ↦ hx₀ (Set.mem_univ y),
    laplaceBeltrami_nonpos_of_isLocalMax hf.contMDiffAt (hx₀.isLocalMax Filter.univ_mem)⟩

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
  obtain ⟨x₀, hx₀, hmax⟩ := exists_forall_le_and_laplaceBeltrami_nonpos (f := u - v) (hu.sub hv)
  rw [laplaceBeltrami_sub I hu hv] at hmax
  -- Hence `h x₀ (u x₀) ≤ h x₀ (v x₀)`, so `u x₀ ≤ v x₀` by strict monotonicity.
  have hle : u x₀ ≤ v x₀ :=
    (hh x₀).le_iff_le.1 (by linarith [hsub x₀, hsuper x₀])
  have hy : u y - v y ≤ u x₀ - v x₀ := hx₀ y
  linarith

/-- **The maximum principle bound for a logistic subsolution.** On a compact boundaryless
Riemannian manifold, a `C²` function `u` with `-Δu / 2 + (r / 4) (u - 1) u ≤ k u` satisfies
`u ≤ 1 + 4 k / r`. For `u = |α|² + |β|²` this is Taubes's bound `|Ψ|² ≤ r (1 + C / r)` on a
Seiberg–Witten spinor. -/
theorem le_one_add_mul_div_of_laplaceBeltrami_le [CompactSpace M] {u : M → ℝ} {r k : ℝ}
    (hr : 0 < r) (hk : 0 ≤ k) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (h : ∀ x, -laplaceBeltrami I u x / 2 + r / 4 * (u x - 1) * u x ≤ k * u x) (x : M) :
    u x ≤ 1 + 4 * k / r := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨x₀, hx₀, hΔ⟩ := exists_forall_le_and_laplaceBeltrami_nonpos hu
  refine (hx₀ x).trans ?_
  have h₀ := h x₀
  rcases le_or_gt (u x₀) 0 with hu₀ | hu₀
  · exact hu₀.trans (by positivity)
  -- At the maximum `Δu ≤ 0`, so `(r / 4) (u - 1) u ≤ k u`, and `u > 0` there.
  have hle : r / 4 * (u x₀ - 1) ≤ k := le_of_mul_le_mul_right (by linarith) hu₀
  rw [← sub_le_iff_le_add', le_div_iff₀ hr]
  linarith

end TauCeti.Manifold
