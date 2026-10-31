/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.LocallySymmetric

/-!
# The covariant derivative of curvature under Riemannian isometries

A local Riemannian isometry `f : M → N`, and in particular a smooth Riemannian isometry, carries
the covariant derivative `∇R` of the Riemann curvature tensor of `M` to that of `N`:

`df_x ((∇_v R)(u, w) s) = (∇_{df_x v} R)(df_x u, df_x w) (df_x s)`

for all tangent vectors `v, u, w, s` at `x`, where both sides use the Levi-Civita connections.
Contracting in an orthonormal basis, it also preserves the covariant derivative `∇Ric` of the
Ricci tensor.

Consequently `∇R` vanishes at `x` exactly when it vanishes at `f x`. Since `f` need not be
injective or surjective, having parallel curvature, that is local symmetry in Cartan's
characterization, pulls back along every local Riemannian isometry, in particular to open
submanifolds; it descends along surjective ones, such as Riemannian coverings, and Riemannian
isometric manifolds are locally symmetric together.

The identity follows from the naturality of the Levi-Civita connection
(`TauCeti.IsLocalRiemannianIsometry.mfderiv_leviCivitaConnection_mpullback`) and of the curvature
tensor (`TauCeti.IsLocalRiemannianIsometry.mfderiv_curvatureTensor`), applied to each of the four
terms of `(∇_v R)(Y, Z) W = ∇_v (R(Y, Z) W) - R(∇_v Y, Z) W - R(Y, ∇_v Z) W - R(Y, Z) (∇_v W)`
on pullbacks of smooth vector fields.

## Main results

In the namespace `TauCeti.IsLocalRiemannianIsometry`:

* `mfderiv_derivCurvatureTensor`: **naturality of the covariant derivative of the curvature
  tensor**.
* `derivRicciTensor_mfderiv`: preservation of the covariant derivative of the Ricci tensor.
* `derivCurvatureTensor_eq_zero_iff`: `∇R` vanishes at `f x` exactly when it vanishes at `x`.
* `hasParallelCurvature` and `hasParallelCurvature_iff_of_surjective`: parallel curvature pulls
  back along local Riemannian isometries and descends along surjective ones.

In the namespace `TauCeti.RiemannianIsometry`, `hasParallelCurvature_iff`: Riemannian isometric
manifolds have parallel curvature together.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Proposition 7.6
  (naturality of the curvature tensor) and Chapter 7 (locally symmetric spaces).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience
  (1969), Chapter XI (affine locally symmetric spaces, as connections with parallel curvature).
-/

public section

open Bundle FiberBundle Manifold VectorField CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

namespace IsLocalRiemannianIsometry

variable {f : M → N}

/-- **Naturality of the covariant derivative of the curvature tensor under local Riemannian
isometries:** `df_x ((∇_v R)(u, w) s) = (∇_{df_x v} R)(df_x u, df_x w) (df_x s)`. -/
@[simp]
theorem mfderiv_derivCurvatureTensor (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (v u w s : TangentSpace I x) :
    mfderiv I J f x
        ((leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M) x v u w s) =
      (leviCivitaConnection J N).derivCurvatureTensor (leviCivitaConnection J N) (f x)
        (mfderiv I J f x v) (mfderiv I J f x u) (mfderiv I J f x w) (mfderiv I J f x s) := by
  -- Extend the images of `u`, `w`, `s` to smooth vector fields on `N` and pull them back.
  obtain ⟨Y, hY, hYu, hYf⟩ := hf.exists_contMDiff_mpullback_apply_eq u
  obtain ⟨Z, hZ, hZw, hZf⟩ := hf.exists_contMDiff_mpullback_apply_eq w
  obtain ⟨W, hW, hWs, hWf⟩ := hf.exists_contMDiff_mpullback_apply_eq s
  have hd : ∀ {X : Π y : N, TangentSpace J y}, CMDiff ∞ (T% X) → MDiffAt (T% X) (f x) :=
    fun hX ↦ hX.mdifferentiableAt (by simp)
  have hR := (leviCivitaConnection J N).contMDiff_curvatureOperator hY hZ hW
  rw [← hYf, ← hZf, ← hWf, derivCurvatureTensor_apply _ _ (f x) _ hY hZ hW, ← hYu, ← hZw, ← hWs,
    derivCurvatureTensor_apply _ _ x v (hf.contMDiff_mpullback hY) (hf.contMDiff_mpullback hZ)
      (hf.contMDiff_mpullback hW), hf.curvatureOperator_mpullback hY hZ hW]
  simp only [map_sub, hf.mfderiv_curvatureTensor, hf.mfderiv_apply_mpullback,
    hf.mfderiv_leviCivitaConnection_mpullback (hd hR), hf.mfderiv_leviCivitaConnection_mpullback
      (hd hY), hf.mfderiv_leviCivitaConnection_mpullback (hd hZ),
    hf.mfderiv_leviCivitaConnection_mpullback (hd hW)]

/-- A local Riemannian isometry preserves the covariant derivative of the Ricci tensor:
`(∇_{df_x v} Ric)(df_x u, df_x w) = (∇_v Ric)(u, w)`. -/
@[simp]
theorem derivRicciTensor_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (u w v : TangentSpace I x) :
    (leviCivitaConnection J N).derivRicciTensor (f x) (mfderiv I J f x u) (mfderiv I J f x w)
        (mfderiv I J f x v) =
      (leviCivitaConnection I M).derivRicciTensor x u w v := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [← sum_inner_derivCurvatureTensor_eq_derivRicciTensor _ x b,
    ← sum_inner_derivCurvatureTensor_eq_derivRicciTensor _ (f x) (b.map e)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.map_apply, he, ← hf.mfderiv_derivCurvatureTensor, hf.inner_mfderiv]

/-- The covariant derivative of the curvature tensor vanishes at `f x` exactly when it vanishes
at `x`. -/
theorem derivCurvatureTensor_eq_zero_iff (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (leviCivitaConnection J N).derivCurvatureTensor (leviCivitaConnection J N) (f x) = 0 ↔
      (leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M) x = 0 := by
  have hs := hf.mfderiv_surjective x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext v u w s
    apply hf.mfderiv_injective x
    simp [hf.mfderiv_derivCurvatureTensor, h]
  · ext v' u' w' s'
    obtain ⟨v, rfl⟩ := hs v'
    obtain ⟨u, rfl⟩ := hs u'
    obtain ⟨w, rfl⟩ := hs w'
    obtain ⟨s, rfl⟩ := hs s'
    simp [← hf.mfderiv_derivCurvatureTensor, h]

/-- Parallel curvature pulls back along a local Riemannian isometry: if `N` has parallel
curvature, then so does `M`. -/
theorem hasParallelCurvature (hf : IsLocalRiemannianIsometry I J f)
    (h : (leviCivitaConnection J N).HasParallelCurvature) :
    (leviCivitaConnection I M).HasParallelCurvature := by
  rw [hasParallelCurvature_iff] at h ⊢
  exact fun x ↦ (hf.derivCurvatureTensor_eq_zero_iff x).1 (h (f x))

/-- Along a surjective local Riemannian isometry, such as a Riemannian covering, `N` has parallel
curvature exactly when `M` does. -/
theorem hasParallelCurvature_iff_of_surjective (hf : IsLocalRiemannianIsometry I J f)
    (hs : Function.Surjective f) :
    (leviCivitaConnection J N).HasParallelCurvature ↔
      (leviCivitaConnection I M).HasParallelCurvature := by
  refine ⟨hf.hasParallelCurvature, fun h ↦ ?_⟩
  rw [hasParallelCurvature_iff] at h ⊢
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact (hf.derivCurvatureTensor_eq_zero_iff x).2 (h x)

end IsLocalRiemannianIsometry

/-- Riemannian isometric manifolds have parallel curvature together. -/
theorem RiemannianIsometry.hasParallelCurvature_iff (Φ : RiemannianIsometry I J M N) :
    (leviCivitaConnection J N).HasParallelCurvature ↔
      (leviCivitaConnection I M).HasParallelCurvature :=
  Φ.isLocalRiemannianIsometry.hasParallelCurvature_iff_of_surjective (EquivLike.surjective Φ)

end TauCeti

end
