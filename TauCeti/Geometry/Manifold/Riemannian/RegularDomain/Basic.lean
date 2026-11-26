/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# Regular sublevels as Riemannian manifolds with boundary

Let `(N, g)` be a boundaryless smooth manifold modelled on a real space `E` of dimension `n + 1`,
with a smooth Riemannian metric, and let `a` be a regular value of a smooth function `f : N → ℝ`.
The sublevel `D = {f ≤ a}` is a smooth manifold with boundary for Tau Ceti's atlas
`TauCeti.scalarRegularSublevelChartedSpace`, and its inclusion `j : D → N` is smooth with
invertible differential at every point, boundary points included. This file equips `D` with the
metric `g_D = j^* g` pulled back along `j` (`TauCeti.scalarRegularSublevelMetric`) and proves:

* `j` is a local Riemannian isometry `(D, g_D) → (N, g)`
  (`TauCeti.isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel`); Tau Ceti's naturality
  theorems for local isometries, which assume no boundaryless source, then apply to `j`;
* `dj` carries gradients of restrictions to gradients: `dj(grad^D (u ∘ j)) = grad^N u` for every
  `u : N → ℝ` differentiable at the point
  (`TauCeti.mfderiv_mgradient_comp_subtypeVal_scalarRegularSublevel`).

The metric-free facts about `D` live with the topology of regular sublevels: `a - f` is a global
boundary defining function of `D` (`TauCeti.isBoundaryDefiningFunctionOn_scalarRegularSublevel`),
and a tangent vector `v` at a point of the level `f⁻¹(a)` points outward exactly when
`df(dj v) > 0` (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mfderiv`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer, 2018, Chapter 2 (pullback metrics, local isometries and Riemannian manifolds with
  boundary).
* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)]
  {f : N → ℝ} {a : ℝ}

variable (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
  (hn : finrank ℝ E = n + 1)

/-- The **metric of a regular sublevel**: the pullback `j^* g` of the metric of `N` along the
inclusion `j` of the sublevel `{f ≤ a}` at a regular value `a` of a smooth function `f`, for the
atlas `TauCeti.scalarRegularSublevelChartedSpace`. It is a smooth Riemannian metric because `j` is
smooth with invertible differential at every point, boundary points included. -/
def scalarRegularSublevelMetric :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    ContMDiffRiemannianMetric (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun y : N ↦ TangentSpace I y)).pullback Subtype.val
    (by simpa using contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf)
    fun x ↦ (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel
      (hf.of_le ENat.LEInfty.out) hreg hn x).injective

/-- The metric of a regular sublevel is the metric of `N` applied to the differentials of the
inclusion. -/
@[simp]
theorem scalarRegularSublevelMetric_inner (x : {x | f x ≤ a})
    (v w : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      TangentSpace (𝓡∂ (n + 1)) x) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    (scalarRegularSublevelMetric hf hreg hn).inner x v w =
      inner ℝ (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x v)
        (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x w) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  ContMDiffRiemannianMetric.pullback_ofIsContMDiffRiemannianBundle_inner _ _ _ x v w

/-- **The inclusion of a regular sublevel is a local Riemannian isometry** for the pulled-back
metric `TauCeti.scalarRegularSublevelMetric`: it is smooth, its differential is invertible at
every point, boundary points included, and it preserves inner products. -/
theorem isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    IsLocalRiemannianIsometry (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  { contMDiff := contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    isInvertible_mfderiv :=
      isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (hf.of_le ENat.LEInfty.out) hreg hn
    inner_mfderiv x v w := (scalarRegularSublevelMetric_inner hf hreg hn x v w).symm }

/-- **Gradients of restrictions to a regular sublevel.** For `u : N → ℝ` differentiable at a point
`j x` of the regular sublevel `D = {f ≤ a}`, with the pulled-back metric on `D`, the differential
of the inclusion `j` carries the gradient of `u ∘ j` at `x` to the gradient of `u` at `j x`,
boundary points included. -/
theorem mfderiv_mgradient_comp_subtypeVal_scalarRegularSublevel {u : N → ℝ} (x : {x | f x ≤ a})
    (hu : MDifferentiableAt I 𝓘(ℝ) u x) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x
        (Manifold.mgradient (𝓡∂ (n + 1)) (u ∘ Subtype.val) x) =
      Manifold.mgradient I u x :=
  letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel hf hreg hn).mfderiv_mgradient_comp hu

end TauCeti
