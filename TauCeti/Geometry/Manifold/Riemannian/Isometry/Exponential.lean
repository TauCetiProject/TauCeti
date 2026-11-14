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

A local Riemannian isometry `f : M → N` still carries a geodesic with initial data `(p, v)` to a
geodesic with initial data `(f p, df_p v)`, so it maps the maximal geodesic interval at `(p, v)`
into the one at `(f p, df_p v)` and intertwines the exponential maps on the natural domain at `p`.
No injectivity of `f` is used; for a Riemannian covering this computes the exponential map of the
base. When every geodesic leaving `p` is defined for all time, `f` intertwines the maximal
geodesics and the exponential maps at every time and every tangent vector. Without completeness
this fails: the inclusion of an open subset is a local isometry along which a geodesic of the
ambient manifold can outlive its lifts.

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
* `IsLocalRiemannianIsometry.geodesicInterval_subset_geodesicInterval_mfderiv`: a local isometry
  maps maximal geodesic intervals into maximal geodesic intervals.
* `IsLocalRiemannianIsometry.maximalGeodesic_mfderiv_of_mem`,
  `IsLocalRiemannianIsometry.riemannianExp_mfderiv_of_mem`: a local isometry intertwines the
  maximal geodesics and the exponential maps on their natural domains.
* `IsLocalRiemannianIsometry.maximalGeodesic_mfderiv`,
  `IsLocalRiemannianIsometry.riemannianExp_mfderiv`: with completeness at `p`, a local isometry
  intertwines the maximal geodesics and the exponential maps.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5
  (naturality of geodesics and of the exponential map) and Chapter 6 (Riemannian coverings).
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

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
  {f : M → N} {γ : ℝ → M} {p : M} {v : TangentSpace I p}

namespace IsLocalRiemannianIsometry

/-- A local Riemannian isometry maps the maximal geodesic interval at `(p, v)` into the maximal
geodesic interval at `(f p, df_p v)`. -/
theorem geodesicInterval_subset_geodesicInterval_mfderiv (hf : IsLocalRiemannianIsometry I J f)
    (p : M) (v : TangentSpace I p) :
    geodesicInterval I M p v ⊆ geodesicInterval J N (f p) (mfderiv I J f p v) := by
  intro t ht
  obtain ⟨γ, a, b, hγ, ht'⟩ := (mem_geodesicInterval_iff (I := I) (M := M)).1 ht
  exact (mem_geodesicInterval_iff (I := J) (M := N)).2
    ⟨f ∘ γ, a, b, hf.isGeodesicCurveOnFrom_comp hγ, ht'⟩

/-- The differential of a local Riemannian isometry maps the natural domain of the exponential
map at `p` into the natural domain at `f p`. -/
theorem mfderiv_mem_expDomain (hf : IsLocalRiemannianIsometry I J f)
    (hv : v ∈ expDomain I M p) :
    mfderiv I J f p v ∈ expDomain J N (f p) :=
  mem_expDomain_iff.2
    (hf.geodesicInterval_subset_geodesicInterval_mfderiv p v (mem_expDomain_iff.1 hv))

/-- A local Riemannian isometry carries any geodesic with initial data `(p, v)` to the
maximal geodesic with initial data `(f p, df_p v)` on its interval of definition. -/
theorem maximalGeodesic_mfderiv_eq [J.Boundaryless] [T2Space N]
    (hf : IsLocalRiemannianIsometry I J f) {a b t : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (ht : t ∈ Ioo a b) :
    maximalGeodesic J N (f p) (mfderiv I J f p v) t = f (γ t) := by
  rw [(hf.isGeodesicCurveOnFrom_comp hγ).eqOn_maximalGeodesic ht, Function.comp_apply]

/-- **The exponential map through a local isometry.** If the geodesic `γ` from `p` with velocity
`v` is defined on an open interval containing `1`, then `exp_{f p}(df_p v) = f (γ 1)`. -/
theorem riemannianExp_mfderiv_eq [J.Boundaryless] [T2Space N]
    (hf : IsLocalRiemannianIsometry I J f) {a b : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (h1 : (1 : ℝ) ∈ Ioo a b) :
    riemannianExp J N (f p) (mfderiv I J f p v) = f (γ 1) := by
  rw [riemannianExp_def]
  exact hf.maximalGeodesic_mfderiv_eq hγ h1

/-- A local Riemannian isometry intertwines maximal geodesics at every time in the source
maximal geodesic interval. -/
theorem maximalGeodesic_mfderiv_of_mem [I.Boundaryless] [J.Boundaryless]
    [T2Space N] (hf : IsLocalRiemannianIsometry I J f) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    maximalGeodesic J N (f p) (mfderiv I J f p v) t = f (maximalGeodesic I M p v t) := by
  rw [← maximalIntegralCurveInterval_geodesicSpray] at ht
  obtain ⟨z, a, b, hz, hz0, h0, ht', heq⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  rw [maximalGeodesic_def (I := I), heq]
  exact hf.maximalGeodesic_mfderiv_eq
    (hz.isGeodesicCurveOnFrom_proj (uniqueDiffOn_Ioo a b) h0 hz0) ht'

/-- If every geodesic leaving `p` is defined for all time, a local Riemannian isometry `f`
intertwines the maximal geodesics leaving `p` and `f p`. -/
theorem maximalGeodesic_mfderiv [I.Boundaryless] [J.Boundaryless] [T2Space N]
    (hf : IsLocalRiemannianIsometry I J f) (hp : IsGeodesicallyCompleteAt I M p)
    (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic J N (f p) (mfderiv I J f p v) t = f (maximalGeodesic I M p v t) :=
  hf.maximalGeodesic_mfderiv_of_mem (hp.geodesicInterval_eq_univ v ▸ mem_univ t)

/-- A local Riemannian isometry intertwines the exponential maps on the natural domain of the
source exponential map. -/
theorem riemannianExp_mfderiv_of_mem [I.Boundaryless] [J.Boundaryless]
    [T2Space N] (hf : IsLocalRiemannianIsometry I J f)
    (hv : v ∈ expDomain I M p) :
    riemannianExp J N (f p) (mfderiv I J f p v) = f (riemannianExp I M p v) := by
  simpa only [riemannianExp_def] using
    hf.maximalGeodesic_mfderiv_of_mem (mem_expDomain_iff.1 hv)

/-- **Naturality of the exponential map under a local isometry.** If every geodesic leaving `p`
is defined for all time, a local Riemannian isometry `f` satisfies
`exp_{f p} (df_p v) = f (exp_p v)` for every tangent vector `v` at `p`. -/
theorem riemannianExp_mfderiv [I.Boundaryless] [J.Boundaryless] [T2Space N]
    (hf : IsLocalRiemannianIsometry I J f) (hp : IsGeodesicallyCompleteAt I M p)
    (v : TangentSpace I p) :
    riemannianExp J N (f p) (mfderiv I J f p v) = f (riemannianExp I M p v) :=
  hf.riemannianExp_mfderiv_of_mem
    (mem_expDomain_iff.2 (hp.geodesicInterval_eq_univ v ▸ mem_univ 1))

end IsLocalRiemannianIsometry

namespace RiemannianIsometry

/-! ### Maximal intervals -/

/-- A smooth Riemannian isometry preserves the maximal geodesic interval: the maximal interval of
the geodesic with initial data `(Φ p, dΦ_p v)` is that of the geodesic with initial data
`(p, v)`. -/
@[simp]
theorem geodesicInterval_mfderiv (Φ : RiemannianIsometry I J M N) (p : M)
    (v : TangentSpace I p) :
    geodesicInterval J N (Φ p) (mfderiv I J Φ p v) = geodesicInterval I M p v := by
  apply Subset.antisymm
  · have h := Φ.symm.isLocalRiemannianIsometry.geodesicInterval_subset_geodesicInterval_mfderiv
      (Φ p) (mfderiv I J Φ p v)
    rw [coe_symm, ← coe_toDiffeomorph,
      Φ.toDiffeomorph.mfderiv_symm_apply_mfderiv_apply (by simp),
      Φ.toDiffeomorph.symm_apply_apply] at h
    exact h
  · exact Φ.isLocalRiemannianIsometry.geodesicInterval_subset_geodesicInterval_mfderiv p v

/-- A smooth Riemannian isometry intertwines the maximal geodesics with corresponding initial
data, at every time `t`: the identity holds on the common maximal interval, and off it both sides
take the junk value `Φ p`. -/
@[simp]
theorem maximalGeodesic_mfderiv [I.Boundaryless] [J.Boundaryless] [T2Space M]
    (Φ : RiemannianIsometry I J M N) (p : M) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic J N (Φ p) (mfderiv I J Φ p v) t = Φ (maximalGeodesic I M p v t) := by
  have : T2Space N := Φ.toDiffeomorph.toHomeomorph.t2Space
  by_cases ht : t ∈ geodesicInterval I M p v
  · exact Φ.isLocalRiemannianIsometry.maximalGeodesic_mfderiv_of_mem ht
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

end RiemannianIsometry

end TauCeti

end
