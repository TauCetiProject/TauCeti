/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization

/-!
# The exponential map under local Riemannian isometries

A local Riemannian isometry `f : M → N` carries a geodesic with initial data `(p, v)` to a
geodesic with initial data `(f p, df_p v)`. When every geodesic leaving `p` is defined for all
time, the image of the maximal geodesic `γ_{p, v}` is therefore a geodesic of `N` on the whole
real line, so it is the maximal geodesic `γ_{f p, df_p v}`, and the latter is also defined for all
time. Since `df_p` is surjective, `N` is geodesically complete at `f p`, and `f` intertwines the
exponential maps: `f ∘ exp_p = exp_{f p} ∘ df_p`.

For a Riemannian isometry these statements hold without any completeness assumption
(`TauCeti.RiemannianIsometry.riemannianExp_mfderiv`). For a local isometry, completeness at `p`
is what rules out a geodesic of `N` that is defined longer than its lifts: the inclusion of an
open subset is a local isometry which does not intertwine the exponential maps.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.isGeodesicCurveOnFrom_comp`: a local isometry carries the
  initial point and velocity of a geodesic through its differential.
* `TauCeti.IsLocalRiemannianIsometry.maximalGeodesic_mfderiv`: with completeness at `p`, `f`
  intertwines the maximal geodesics leaving `p` and `f p`.
* `TauCeti.IsLocalRiemannianIsometry.isGeodesicallyCompleteAt`: with completeness at `p`, the
  target is geodesically complete at `f p`.
* `TauCeti.IsLocalRiemannianIsometry.riemannianExp_mfderiv`: with completeness at `p`,
  `exp_{f p} (df_p v) = f (exp_p v)`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5
  (naturality of geodesics and of the exponential map) and Chapter 6 (Riemannian coverings).
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti

namespace IsLocalRiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

variable [I.Boundaryless] [J.Boundaryless] [T2Space M] [T2Space N]

omit [J.Boundaryless] [T2Space M] [T2Space N] in
/-- At a point where the manifold is geodesically complete, every maximal geodesic interval is
the whole real line. -/
private theorem geodesicInterval_eq_univ {p : M} (hp : IsGeodesicallyCompleteAt I M p)
    (v : TangentSpace I p) : geodesicInterval I M p v = univ := by
  have h := expDomain_eq_univ_iff.2 hp
  exact eq_univ_of_forall fun t ↦
    mem_geodesicInterval_iff_smul_mem_expDomain.2 (h ▸ mem_univ _)

/-- If every geodesic leaving `p` is defined for all time, a local Riemannian isometry `f` carries
the maximal geodesic with initial data `(p, v)` to the maximal geodesic with initial data
`(f p, df_p v)`, and the latter is defined for all time. -/
theorem geodesicInterval_mfderiv_eq_univ_and_maximalGeodesic_mfderiv
    (hf : IsLocalRiemannianIsometry I J f) {p : M} (hp : IsGeodesicallyCompleteAt I M p)
    (v : TangentSpace I p) :
    geodesicInterval J N (f p) (mfderiv I J f p v) = univ ∧
      ∀ t, maximalGeodesic J N (f p) (mfderiv I J f p v) t = f (maximalGeodesic I M p v t) := by
  have hγ : IsGeodesicCurveOnFrom I (maximalGeodesic I M p v) univ p v := by
    simpa only [geodesicInterval_eq_univ hp v] using
      isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  have hfγ := hf.isGeodesicCurveOnFrom_comp hγ
  have hloc (t : ℝ) : IsGeodesicCurveOnFrom J (f ∘ maximalGeodesic I M p v)
      (Ioo (-(|t| + 1)) (|t| + 1)) (f p) (mfderiv I J f p v) :=
    hfγ.mono (uniqueDiffOn_Ioo _ _) (subset_univ _)
      ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  have hmem (t : ℝ) : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨eq_univ_of_forall fun t ↦ ?_, fun t ↦ ?_⟩
  · exact (mem_geodesicInterval_iff (I := J) (M := N)).2 ⟨_, _, _, hloc t, hmem t⟩
  · exact (hloc t).eqOn_maximalGeodesic (hmem t)

/-- If every geodesic leaving `p` is defined for all time, a local Riemannian isometry `f`
intertwines the maximal geodesics leaving `p` and `f p`. -/
theorem maximalGeodesic_mfderiv (hf : IsLocalRiemannianIsometry I J f) {p : M}
    (hp : IsGeodesicallyCompleteAt I M p) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic J N (f p) (mfderiv I J f p v) t = f (maximalGeodesic I M p v t) :=
  (hf.geodesicInterval_mfderiv_eq_univ_and_maximalGeodesic_mfderiv hp v).2 t

/-- If every geodesic leaving `p` is defined for all time, then so is every geodesic leaving
`f p`, for a local Riemannian isometry `f`. -/
theorem isGeodesicallyCompleteAt (hf : IsLocalRiemannianIsometry I J f) {p : M}
    (hp : IsGeodesicallyCompleteAt I M p) : IsGeodesicallyCompleteAt J N (f p) := by
  refine expDomain_eq_univ_iff.1 (eq_univ_of_forall fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := hf.mfderiv_surjective p w
  rw [mem_expDomain_iff, (hf.geodesicInterval_mfderiv_eq_univ_and_maximalGeodesic_mfderiv hp v).1]
  exact mem_univ _

/-- **Naturality of the exponential map under a local isometry.** If every geodesic leaving `p`
is defined for all time, a local Riemannian isometry `f` satisfies
`exp_{f p} (df_p v) = f (exp_p v)` for every tangent vector `v` at `p`. -/
theorem riemannianExp_mfderiv (hf : IsLocalRiemannianIsometry I J f) {p : M}
    (hp : IsGeodesicallyCompleteAt I M p) (v : TangentSpace I p) :
    riemannianExp J N (f p) (mfderiv I J f p v) = f (riemannianExp I M p v) := by
  simp only [riemannianExp_def, hf.maximalGeodesic_mfderiv hp]

end IsLocalRiemannianIsometry

end TauCeti
