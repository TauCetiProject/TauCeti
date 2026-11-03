/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongCurve
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic

/-!
# Jacobi fields under Riemannian isometries

A smooth Riemannian isometry `Φ : M → N` carries a Jacobi field `V` along a geodesic `γ` to the
Jacobi field `t ↦ dΦ (V t)` along the geodesic `Φ ∘ γ`, and every Jacobi field along `Φ ∘ γ`
arises in this way. This holds on every parameter set with unique derivatives, including closed
intervals.

The differential of `Φ` commutes with covariant differentiation along curves, takes the velocity
of `γ` to the velocity of `Φ ∘ γ` and takes the curvature tensor of `M` to that of `N`, so it
carries the Jacobi equation `D_t² V + R(V, γ')γ' = 0` along `γ` to the Jacobi equation along
`Φ ∘ γ`. The tangent map of `Φ` is smooth, so it preserves the `C²` regularity of the field.

## Main results

* `TauCeti.RiemannianIsometry.isJacobiFieldOn_comp_iff`: `t ↦ dΦ (V t)` is a Jacobi field along
  `Φ ∘ γ` exactly when `V` is a Jacobi field along `γ`.

The initial data of the transported field are the images of those of `V` under `dΦ`, by
`TauCeti.RiemannianIsometry.mfderiv_alongCurveWithin`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

private theorem isJacobiFieldOn_comp (Φ : RiemannianIsometry I J M N)
    (h : IsJacobiFieldOn I γ V s) :
    IsJacobiFieldOn J (Φ ∘ γ) (fun r ↦ mfderiv I J Φ (γ r) (V r)) s := by
  have hfirst : ∀ r ∈ s, alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
      (fun r ↦ mfderiv I J Φ (γ r) (V r)) s r =
        mfderiv I J Φ (γ r) (alongCurveWithin (leviCivitaConnection I M) γ V s r) :=
    fun r hr ↦ (Φ.mfderiv_alongCurveWithin (h.uniqueDiffOn r hr)
      (h.isGeodesicCurveOn.mdifferentiableOn r hr) (h.differentiableWithinAt_sectionCoord hr)).symm
  refine ⟨Φ.isGeodesicCurveOn_comp_iff.2 h.isGeodesicCurveOn, ?_, fun r hr ↦ ?_⟩
  · exact (Φ.toDiffeomorph.contMDiff.contMDiff_tangentMap (m := 2) (by simp)).comp_contMDiffOn
      h.contMDiffOn
  -- The differential of `Φ` carries the second covariant derivative and the velocity along `γ`
  -- to those along `Φ ∘ γ`.
  have hsecond : alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
      (alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ mfderiv I J Φ (γ r) (V r)) s) s r =
        mfderiv I J Φ (γ r) (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ V s) s r) := by
    rw [alongCurveWithin_congr _ _ _ (mem_of_superset self_mem_nhdsWithin hfirst) (hfirst r hr)]
    exact (Φ.mfderiv_alongCurveWithin (h.uniqueDiffOn r hr)
      (h.isGeodesicCurveOn.mdifferentiableOn r hr)
      (h.differentiableWithinAt_sectionCoord_alongCurveWithin hr)).symm
  have hvel : curveVelocityWithin J (Φ ∘ γ) s r =
      mfderiv I J Φ (γ r) (curveVelocityWithin I γ s r) :=
    curveVelocityWithin_map (Φ.mdifferentiableAt (γ r)) (h.uniqueDiffOn r hr)
      (h.isGeodesicCurveOn.mdifferentiableOn r hr)
  -- Apply `dΦ` to the Jacobi equation along `γ` at `r`.
  have heq := congrArg (mfderiv I J Φ (γ r)) (h.equation r hr)
  rw [map_add, map_zero, Φ.isLocalRiemannianIsometry.mfderiv_curvatureTensor] at heq
  rwa [hsecond, hvel]

/-- **Riemannian isometries preserve Jacobi fields.** For a smooth Riemannian isometry `Φ`, the
field `t ↦ dΦ (V t)` along `Φ ∘ γ` is a Jacobi field exactly when `V` is a Jacobi field
along `γ`. -/
@[simp]
theorem isJacobiFieldOn_comp_iff (Φ : RiemannianIsometry I J M N) :
    IsJacobiFieldOn J (Φ ∘ γ) (fun r ↦ mfderiv I J Φ (γ r) (V r)) s ↔
      IsJacobiFieldOn I γ V s := by
  refine ⟨fun h ↦ ?_, Φ.isJacobiFieldOn_comp⟩
  have h' := Φ.symm.isJacobiFieldOn_comp h
  have hcomp : Φ.symm ∘ (Φ ∘ γ) = γ := funext fun r ↦ Φ.symm_apply_apply (γ r)
  -- Rewriting the curve is type-correct because every tangent space is the model space `E`.
  rw [hcomp] at h'
  refine h'.congr fun r _ ↦ ?_
  rw [coe_symm, Function.comp_apply, ← coe_toDiffeomorph]
  exact (Φ.toDiffeomorph.mfderiv_symm_apply_mfderiv_apply (by simp) (γ r) (V r)).symm

end TauCeti.RiemannianIsometry
