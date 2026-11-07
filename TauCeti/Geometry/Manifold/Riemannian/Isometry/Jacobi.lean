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

A local Riemannian isometry `f : M → N` carries a Jacobi field `V` along a geodesic `γ` to the
Jacobi field `t ↦ df (V t)` along the geodesic `f ∘ γ`. For a global Riemannian isometry,
applying this result to the inverse also gives reflection of the Jacobi condition. This holds on
every parameter set with unique derivatives, including closed intervals. For local isometries,
reflection holds when the original field has a `C²` tangent-bundle lift; this assumption also
ensures regularity of the base curve and rules out jumps between distinct sheets.

The differential of `f` commutes with covariant differentiation along curves, takes the velocity
of `γ` to the velocity of `f ∘ γ` and takes the curvature tensor of `M` to that of `N`, so it
carries the Jacobi equation `D_t² V + R(V, γ')γ' = 0` along `γ` to the Jacobi equation along
`f ∘ γ`. The tangent map of `f` is smooth, so it preserves the `C²` regularity of the field.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.isJacobiFieldOn_comp`: local isometries preserve Jacobi
  fields on the same parameter set.
* `TauCeti.IsLocalRiemannianIsometry.isJacobiFieldOn_comp_iff`: preservation and reflection for
  fields with `C²` tangent-bundle lifts.
* `TauCeti.RiemannianIsometry.isJacobiFieldOn_comp_iff`: `t ↦ dΦ (V t)` is a Jacobi field along
  `Φ ∘ γ` exactly when `V` is a Jacobi field along `γ`.

The initial data of the transported field are the images of those of `V` under the differential of
the isometry, by `TauCeti.IsLocalRiemannianIsometry.mfderiv_alongCurveWithin`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

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

namespace IsLocalRiemannianIsometry

/-- A local Riemannian isometry carries Jacobi fields to Jacobi fields along the image geodesic. -/
theorem isJacobiFieldOn_comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    (h : IsJacobiFieldOn I γ V s) :
    IsJacobiFieldOn J (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) s := by
  refine ⟨hf.isGeodesicCurveOn_comp h.isGeodesicCurveOn, ?_, fun r hr ↦ ?_⟩
  · exact (hf.contMDiff.contMDiff_tangentMap (m := 2) (by simp)).comp_contMDiffOn
      h.contMDiffOn
  have hsecond := hf.mfderiv_alongCurveWithin_alongCurveWithin h.uniqueDiffOn h.contMDiffOn hr
  have hvel : curveVelocityWithin J (f ∘ γ) s r =
      mfderiv I J f (γ r) (curveVelocityWithin I γ s r) :=
    curveVelocityWithin_map (hf.mdifferentiableAt (γ r))
      (h.isGeodesicCurveOn.mdifferentiableOn r hr)
  -- Apply `df` to the Jacobi equation along `γ` at `r`.
  have heq := congrArg (mfderiv I J f (γ r)) (h.equation r hr)
  rw [map_add, map_zero, hf.mfderiv_curvatureTensor] at heq
  rwa [← hsecond, hvel]

/-- A field with `C²` tangent-bundle lift is Jacobi exactly when its image under a local
Riemannian isometry is. The lift regularity also supplies regularity of the base curve. -/
theorem isJacobiFieldOn_comp_iff {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s) :
    IsJacobiFieldOn J (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) s ↔
      IsJacobiFieldOn I γ V s := by
  refine ⟨fun h ↦ ?_, hf.isJacobiFieldOn_comp⟩
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I)
      (n := 2)).comp_contMDiffOn hV
  refine ⟨(hf.isGeodesicCurveOn_comp_iff hγ).1 h.isGeodesicCurveOn, hV, fun r hr ↦ ?_⟩
  apply hf.mfderiv_injective (γ r)
  rw [map_add, map_zero,
    hf.mfderiv_alongCurveWithin_alongCurveWithin h.uniqueDiffOn hV hr,
    hf.mfderiv_curvatureTensor,
    ← curveVelocityWithin_map (hf.mdifferentiableAt _)
      ((hγ.mdifferentiableOn (by norm_num)) r hr)]
  exact h.equation r hr

end IsLocalRiemannianIsometry

namespace RiemannianIsometry

/-- **Riemannian isometries preserve Jacobi fields.** For a smooth Riemannian isometry `Φ`, the
field `t ↦ dΦ (V t)` along `Φ ∘ γ` is a Jacobi field exactly when `V` is a Jacobi field
along `γ`. -/
@[simp]
theorem isJacobiFieldOn_comp_iff (Φ : RiemannianIsometry I J M N) :
    IsJacobiFieldOn J (Φ ∘ γ) (fun r ↦ mfderiv I J Φ (γ r) (V r)) s ↔
      IsJacobiFieldOn I γ V s := by
  refine ⟨fun h ↦ ?_, Φ.isLocalRiemannianIsometry.isJacobiFieldOn_comp⟩
  have h' := Φ.symm.isLocalRiemannianIsometry.isJacobiFieldOn_comp h
  have hcomp : Φ.symm ∘ (Φ ∘ γ) = γ := funext fun r ↦ Φ.symm_apply_apply (γ r)
  -- Rewriting the curve is type-correct because every tangent space is the model space `E`.
  rw [hcomp] at h'
  refine h'.congr fun r _ ↦ ?_
  rw [coe_symm, Function.comp_apply, ← coe_toDiffeomorph]
  exact (Φ.toDiffeomorph.mfderiv_symm_apply_mfderiv_apply (by simp) (γ r) (V r)).symm

end RiemannianIsometry

end TauCeti
