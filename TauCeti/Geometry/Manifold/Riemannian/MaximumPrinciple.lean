/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Giada Franz
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# The maximum principle for the Laplace–Beltrami operator

On a boundaryless Riemannian manifold, this file proves the pointwise second-derivative test for
the Riemannian Hessian and the Laplace–Beltrami operator `Δ = div ∘ grad`, and the resulting
comparison principle for semilinear elliptic equations on a compact manifold. It also proves
the weak maximum principle on compact subsets in the presence of a strictly subharmonic barrier.

At a critical point of a `C²` function the Levi-Civita correction term of the Hessian vanishes,
so the Riemannian Hessian is the ordinary second derivative of the function read in the
preferred chart. Consequently the Hessian is negative semidefinite at a local maximum and
positive semidefinite at a local minimum, and the same holds for its trace `Δ`.

On a compact boundaryless manifold, evaluating at a maximum of `u - v` gives the comparison
principle: if `h(x, ·)` is strictly increasing for every `x`, a subsolution
`h(x, u) ≤ Δ u` lies below a supersolution `Δ v ≤ h(x, v)`. In particular a semilinear equation
`Δ u = h(x, u)` with strictly increasing nonlinearity has at most one `C²` solution. This is the
uniqueness mechanism for the curvature equation of conformal metrics on closed surfaces.

Let `K` be a compact subset of a boundaryless Riemannian manifold. Its *boundary part*
`K \ interior K` plays the role of the boundary of a domain. This file proves the classical weak
maximum principle on `K` for the Laplace–Beltrami operator `Δ = div ∘ grad`.

If `Δ w > 0` on the interior of `K`, then `w` attains its maximum over `K` at a point of
`K \ interior K`, because at an interior maximum the Laplacian is nonpositive. If moreover
`Δ u ≥ 0` on the interior of `K`, then the same holds for `u + ε w` for every `ε > 0`, and letting
`ε → 0` shows that `u` is bounded on `K` by its bounds on `K \ interior K`. In Euclidean space
`w = |x|²` is such a strict subsolution; on a general manifold one has to be supplied.

## Main results

* `TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin`: the second-derivative test.
* `TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.laplaceBeltrami_nonneg_of_isLocalMin`: the sign of `Δ` at local extrema.
* `TauCeti.Manifold.le_of_le_laplaceBeltrami_of_laplaceBeltrami_le`: the comparison principle.
* `TauCeti.Manifold.exists_mem_sdiff_interior_isMaxOn_of_laplaceBeltrami_pos`: a function with
  positive Laplacian on the interior of a nonempty compact set `K` attains its maximum over `K`
  on `K \ interior K`.
* `TauCeti.Manifold.le_of_laplaceBeltrami_nonneg_of_forall_mem_sdiff_interior_le`:
  the weak maximum principle for subharmonic functions, in the presence of a strict subsolution.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Chapter 3, especially Theorem 3.1 (the classical weak maximum principle).
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47 (comparison of sub- and supersolutions on a compact manifold).

The compact-set results adapt Giada Franz's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/MaximumPrinciple/Compact.lean`,
revision `dce3b2954b2845d2a9609395ece4cf0910cd1694` (Apache 2.0).
-/

public section

open Bundle Filter Set
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

variable {K : Set M}

/-- **Strict weak maximum principle.** A function that is continuous on a nonempty compact set
`K`, and `C²` with positive Laplacian on the interior of `K`, attains its maximum over `K` at a
point of `K \ interior K`. -/
theorem exists_mem_sdiff_interior_isMaxOn_of_laplaceBeltrami_pos (hK : IsCompact K)
    (hne : K.Nonempty) {w : M → ℝ} (hcont : ContinuousOn w K)
    (hw : ∀ x ∈ interior K, ContMDiffAt I 𝓘(ℝ) 2 w x)
    (hpos : ∀ x ∈ interior K, 0 < laplaceBeltrami I w x) :
    ∃ x ∈ K \ interior K, IsMaxOn w K x := by
  obtain ⟨x, hxK, hmax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨x, ⟨hxK, fun hx ↦ ?_⟩, hmax⟩
  exact (hpos x hx).not_ge (laplaceBeltrami_nonpos_of_isLocalMax (hw x hx)
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.1 hx)))

/-- **Weak maximum principle.** Let `K` be compact and let `u` and `w` be continuous on
`K` and `C²` on its interior. If `Δ u ≥ 0` and `Δ w > 0` on the interior of `K`, then every
upper bound of `u` on `K \ interior K` is an upper bound of `u` on `K`. -/
theorem le_of_laplaceBeltrami_nonneg_of_forall_mem_sdiff_interior_le (hK : IsCompact K)
    {u w : M → ℝ} (hcu : ContinuousOn u K) (hcw : ContinuousOn w K)
    (hu : ∀ x ∈ interior K, ContMDiffAt I 𝓘(ℝ) 2 u x)
    (hw : ∀ x ∈ interior K, ContMDiffAt I 𝓘(ℝ) 2 w x)
    (hΔu : ∀ x ∈ interior K, 0 ≤ laplaceBeltrami I u x)
    (hΔw : ∀ x ∈ interior K, 0 < laplaceBeltrami I w x) {c : ℝ}
    (hc : ∀ x ∈ K \ interior K, u x ≤ c) {x : M} (hx : x ∈ K) : u x ≤ c := by
  refine (hK.bddAbove_image hcw).le_of_forall_pos_exists_add_mul_le fun ε hε ↦ ?_
  have hεw (y : M) (hy : y ∈ interior K) : ContMDiffAt I 𝓘(ℝ) 2 (ε • w) y :=
    (contMDiffAt_const (c := ε)).mul (hw y hy)
  have hv (y : M) (hy : y ∈ interior K) : ContMDiffAt I 𝓘(ℝ) 2 (u + ε • w) y :=
    (hu y hy).add (hεw y hy)
  obtain ⟨z, hz, hmax⟩ := exists_mem_sdiff_interior_isMaxOn_of_laplaceBeltrami_pos hK
    ⟨x, hx⟩ (hcu.add (hcw.const_smul ε)) hv fun y hy ↦ by
      rw [laplaceBeltrami_add_of_contMDiffAt I (hu y hy) (hεw y hy),
        laplaceBeltrami_smul_of_contMDiffAt I ε (hw y hy)]
      exact add_pos_of_nonneg_of_pos (hΔu y hy) (mul_pos hε (hΔw y hy))
  exact ⟨z, hz.1, isMaxOn_iff.1 hmax x hx, hc z hz⟩

end TauCeti.Manifold
