/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic

/-!
# Local Riemannian isometries carry geodesics and exponential maps

A local Riemannian isometry `f : M → N` carries a geodesic from `p` with initial velocity `v` to a
geodesic from `f p` with initial velocity `df_p v`: the geodesic equation is preserved, and the
velocity lift of `f ∘ γ` is the tangent map of the velocity lift of `γ`. Consequently, if the
geodesic from `p` with velocity `v` is defined on an open interval containing `1`, then `df_p v`
lies in the domain of the exponential map at `f p` and `exp_{f p}(df_p v) = f (exp_p v)`. No
injectivity of `f` is used; for a covering map this computes the exponential map of the quotient.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {γ : ℝ → M} {p : M} {v : TangentSpace I p}

/-- A local Riemannian isometry carries a geodesic with initial data `(p, v)` to a geodesic with
initial data `(f p, df_p v)`. -/
theorem isGeodesicCurveOnFrom_comp [IsManifold I 2 M] [IsManifold J 2 N]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
    (hf : IsLocalRiemannianIsometry I J f) {s : Set ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ s p v) :
    IsGeodesicCurveOnFrom J (f ∘ γ) s (f p) (mfderiv I J f p v) := by
  refine ⟨hf.isGeodesicCurveOn_comp hγ.isGeodesicCurveOn, hγ.zero_mem, ?_⟩
  have hlift := tangentMap_curveVelocityLiftWithin (hf.mdifferentiableAt (γ 0))
    (hγ.isGeodesicCurveOn.mdifferentiableOn 0 hγ.zero_mem)
    (hγ.isGeodesicCurveOn.uniqueDiffOn 0 hγ.zero_mem).uniqueMDiffWithinAt
  rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply, hγ.initial_eq] at hlift
  rw [← hlift]
  rfl

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- If the geodesic from `p` with velocity `v` is defined on an open interval containing `1`, then
`df_p v` lies in the domain of the exponential map at `f p`. -/
theorem mfderiv_mem_expDomain (hf : IsLocalRiemannianIsometry I J f) {a b : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (h1 : (1 : ℝ) ∈ Ioo a b) :
    mfderiv I J f p v ∈ expDomain J N (f p) :=
  mem_expDomain_iff.2 (mem_geodesicInterval_iff.2
    ⟨f ∘ γ, a, b, hf.isGeodesicCurveOnFrom_comp hγ, h1⟩)

/-- **The exponential map through a local isometry.** If the geodesic `γ` from `p` with velocity
`v` is defined on an open interval containing `1`, then `exp_{f p}(df_p v) = f (γ 1)`. -/
theorem riemannianExp_mfderiv_eq [J.Boundaryless] [T2Space N]
    (hf : IsLocalRiemannianIsometry I J f) {a b : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (h1 : (1 : ℝ) ∈ Ioo a b) :
    riemannianExp J N (f p) (mfderiv I J f p v) = f (γ 1) := by
  rw [riemannianExp_def, (hf.isGeodesicCurveOnFrom_comp hγ).eqOn_maximalGeodesic h1,
    Function.comp_apply]

end TauCeti.IsLocalRiemannianIsometry
