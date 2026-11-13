/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential

/-!
# Maximal geodesics and the exponential map under Riemannian isometries

A smooth Riemannian isometry `Φ : M → N` carries geodesics with initial data `(p, v)` to
geodesics with initial data `(Φ p, dΦ_p v)`. Consequently it preserves the maximal geodesic
interval, intertwines the maximal geodesics, `Φ ∘ γ_{p, v} = γ_{Φ p, dΦ_p v}`, carries the natural
domain of the exponential map at `p` onto the one at `Φ p`, and intertwines the exponential maps,
`Φ ∘ exp_p = exp_{Φ p} ∘ dΦ_p`. The identities for the maximal geodesic and the exponential map
hold for every time and every tangent vector, since both sides take the same junk value off the
natural domains.

This is the naturality of the exponential map under isometries; see J. Lee, *Introduction to
Riemannian Manifolds*, 2nd ed., Chapter 5 (naturality of the exponential map), and do Carmo,
*Riemannian Geometry*, Chapter 3, Section 2, for the exponential map itself.

## Main results

* `RiemannianIsometry.geodesicInterval_mfderiv`: an isometry preserves maximal geodesic
  intervals.
* `RiemannianIsometry.maximalGeodesic_mfderiv`: an isometry intertwines maximal geodesics.
* `RiemannianIsometry.mfderiv_image_expDomain`: the differential of an isometry maps the domain of
  the exponential map onto the domain at the image point.
* `RiemannianIsometry.riemannianExp_mfderiv`: an isometry intertwines the exponential maps.
* `RiemannianIsometry.mfderiv_apply_mfderiv_riemannianExp`: on the natural domain, it also
  intertwines their differentials.
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ F]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-! ### Maximal intervals -/

/-- A smooth Riemannian isometry preserves the maximal geodesic interval: the maximal interval of
the geodesic with initial data `(Φ p, dΦ_p v)` is that of the geodesic with initial data
`(p, v)`. -/
@[simp]
theorem geodesicInterval_mfderiv (Φ : RiemannianIsometry I J M N) (p : M)
    (v : TangentSpace I p) :
    geodesicInterval J N (Φ p) (mfderiv I J Φ p v) = geodesicInterval I M p v := by
  ext t
  simp only [mem_geodesicInterval_iff]
  constructor
  · rintro ⟨γ, a, b, hγ, ht⟩
    refine ⟨Φ.symm ∘ γ, a, b, ?_, ht⟩
    have hcomp : Φ ∘ (Φ.symm ∘ γ) = γ := funext fun r ↦ Φ.apply_symm_apply (γ r)
    rw [← hcomp] at hγ
    exact Φ.isGeodesicCurveOnFrom_comp_iff.mp hγ
  · rintro ⟨γ, a, b, hγ, ht⟩
    exact ⟨Φ ∘ γ, a, b, Φ.isGeodesicCurveOnFrom_comp_iff.mpr hγ, ht⟩

/-- A smooth Riemannian isometry intertwines the maximal geodesics with corresponding initial
data, at every time `t`: the identity holds on the common maximal interval, and off it both sides
take the junk value `Φ p`. -/
@[simp]
theorem maximalGeodesic_mfderiv [I.Boundaryless] [J.Boundaryless] [T2Space M]
    (Φ : RiemannianIsometry I J M N) (p : M) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic J N (Φ p) (mfderiv I J Φ p v) t = Φ (maximalGeodesic I M p v t) := by
  have : T2Space N := Φ.toDiffeomorph.toHomeomorph.t2Space
  by_cases ht : t ∈ geodesicInterval I M p v
  · obtain ⟨γ, a, b, hγ, ht'⟩ := (mem_geodesicInterval_iff (I := I) (M := M)).1 ht
    rw [hγ.eqOn_maximalGeodesic ht',
      (Φ.isGeodesicCurveOnFrom_comp_iff.mpr hγ).eqOn_maximalGeodesic ht', Function.comp_apply]
  · have ht' : t ∉ geodesicInterval J N (Φ p) (mfderiv I J Φ p v) := by
      rwa [Φ.geodesicInterval_mfderiv]
    rw [maximalGeodesic_eq_of_not_mem ht, maximalGeodesic_eq_of_not_mem ht']

/-! ### The exponential map -/

/-- A tangent vector at `Φ p` of the form `dΦ_p v` lies in the domain of the exponential map at
`Φ p` exactly when `v` lies in the domain of the exponential map at `p`. -/
theorem mfderiv_mem_expDomain_iff (Φ : RiemannianIsometry I J M N) {p : M}
    {v : TangentSpace I p} :
    mfderiv I J Φ p v ∈ expDomain J N (Φ p) ↔ v ∈ expDomain I M p := by
  simp only [mem_expDomain_iff, Φ.geodesicInterval_mfderiv]

/-- The differential of a smooth Riemannian isometry maps the domain of the exponential map at
`p` onto the domain of the exponential map at `Φ p`. -/
theorem mfderiv_image_expDomain (Φ : RiemannianIsometry I J M N) (p : M) :
    mfderiv I J Φ p '' expDomain I M p = expDomain J N (Φ p) := by
  ext w
  obtain ⟨v, rfl⟩ := Φ.mfderiv_surjective p w
  rw [(Φ.mfderiv_injective p).mem_set_image, Φ.mfderiv_mem_expDomain_iff]

/-- A smooth Riemannian isometry intertwines the exponential maps, `Φ ∘ exp_p = exp_{Φ p} ∘ dΦ_p`,
on every tangent vector: the identity holds on the natural domain, and off it both sides take the
junk value `Φ p`. -/
@[simp]
theorem riemannianExp_mfderiv [I.Boundaryless] [J.Boundaryless] [T2Space M]
    (Φ : RiemannianIsometry I J M N) (p : M) (v : TangentSpace I p) :
    riemannianExp J N (Φ p) (mfderiv I J Φ p v) = Φ (riemannianExp I M p v) := by
  simp only [riemannianExp_def, Φ.maximalGeodesic_mfderiv]

/-- **Naturality of the differential of the exponential map.** At a vector `v` of the natural
domain of `exp_p`, a smooth Riemannian isometry intertwines the differentials of the exponential
maps: `dΦ_(exp_p v) (d(exp_p)_v w) = d(exp_(Φ p))_(dΦ_p v) (dΦ_p w)`. -/
theorem mfderiv_apply_mfderiv_riemannianExp [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [T2Space N] (Φ : RiemannianIsometry I J M N) {p : M} {v : TangentSpace I p}
    (hv : v ∈ expDomain I M p) (w : TangentSpace I p) :
    mfderiv I J Φ (riemannianExp I M p v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      mfderiv 𝓘(ℝ, TangentSpace J (Φ p)) J (riemannianExp J N (Φ p)) (mfderiv I J Φ p v)
        (mfderiv I J Φ p w) := by
  -- Both sides are derivatives at `v` of the same map `Φ ∘ exp_p = exp_(Φ p) ∘ dΦ_p`.
  have hfun : Φ ∘ riemannianExp I M p = riemannianExp J N (Φ p) ∘ mfderiv I J Φ p :=
    funext fun u ↦ (Φ.riemannianExp_mfderiv p u).symm
  have hleft := (Φ.mdifferentiableAt _).hasMFDerivAt.comp v
    ((contMDiffAt_riemannianExp hv).mdifferentiableAt (by simp)).hasMFDerivAt
  have hright := ((contMDiffAt_riemannianExp (Φ.mfderiv_mem_expDomain_iff.2 hv)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp v (mfderiv I J Φ p).hasMFDerivAt
  rw [hfun] at hleft
  exact congrArg (fun L ↦ L w) (hasMFDerivAt_unique hleft hright)

end TauCeti.RiemannianIsometry

end
