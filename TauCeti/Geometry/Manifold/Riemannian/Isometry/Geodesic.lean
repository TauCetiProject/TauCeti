/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongCurve

/-!
# Geodesics under Riemannian isometries

A smooth Riemannian isometry carries geodesics to geodesics. This holds on an arbitrary
parameter set with unique derivatives, and the tangent map carries the initial velocity to the
initial velocity of the image geodesic. Applying the result to the inverse isometry gives
equivalences for interval-aware geodesics, all-time geodesics, and geodesics with initial data.

This is the geodesic form of naturality of the Levi-Civita connection; see do Carmo,
*Riemannian Geometry*, Chapter 2, Theorem 3.6, and Chapter 3, Section 2. The equivalence for
geodesics with prescribed initial data is the input for showing that an isometry preserves
maximal geodesic intervals and intertwines the exponential maps, `Φ ∘ exp_p = exp_{Φ p} ∘ dΦ_p`.

## Main results

* `RiemannianIsometry.isGeodesicCurveOn_comp_iff`: an isometry preserves the geodesic equation
  on a parameter set.
* `RiemannianIsometry.isGeodesicCurve_comp_iff`: the all-time specialization.
* `RiemannianIsometry.isGeodesicCurveOnFrom_comp_iff`: the initial point and velocity are carried
  by the isometry and its differential.
-/

public section

open Bundle CovariantDerivative Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

private theorem isGeodesicCurveOn_comp (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} (h : IsGeodesicCurveOn I γ s) :
    IsGeodesicCurveOn J (Φ ∘ γ) s where
  uniqueDiffOn := h.uniqueDiffOn
  contMDiffOn :=
    (Φ.toDiffeomorph.contMDiff.of_le (by norm_num)).comp_contMDiffOn h.contMDiffOn
  alongCurveWithin_curveVelocityWithin_eq_zero t ht := by
    have hvelocity (r : ℝ) (hr : r ∈ s) :
        curveVelocityWithin J (Φ ∘ γ) s r =
          mfderiv I J Φ (γ r) (curveVelocityWithin I γ s r) :=
      curveVelocityWithin_map (Φ.mdifferentiableAt (γ r)) (h.uniqueDiffOn r hr)
        (h.mdifferentiableOn r hr)
    have hvelocity_eventually :
        curveVelocityWithin J (Φ ∘ γ) s =ᶠ[𝓝[s] t]
          fun r ↦ mfderiv I J Φ (γ r) (curveVelocityWithin I γ s r) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hvelocity r hr
    have hsourceCoord : DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t)) s t :=
      differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn h.contMDiffOn ht
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    have hnaturality := Φ.mfderiv_alongCurveWithin (h.uniqueDiffOn t ht)
      (h.mdifferentiableOn t ht) hsourceCoord
    have hmappedZero : alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ mfderiv I J Φ (γ r) (curveVelocityWithin I γ s r)) s t = 0 := by
      rw [h.alongCurveWithin_curveVelocityWithin_eq_zero t ht, map_zero] at hnaturality
      exact hnaturality.symm
    rw [alongCurveWithin_congr (leviCivitaConnection J N) (Φ ∘ γ)
      (curveVelocityWithin J (Φ ∘ γ) s) hvelocity_eventually (hvelocity t ht)]
    exact hmappedZero

/-- A smooth Riemannian isometry preserves the geodesic equation on every parameter set with
unique derivatives. -/
@[simp]
theorem isGeodesicCurveOn_comp_iff (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} :
    IsGeodesicCurveOn J (Φ ∘ γ) s ↔ IsGeodesicCurveOn I γ s := by
  constructor
  · intro h
    have h' := isGeodesicCurveOn_comp Φ.symm h
    have hcomp : Φ.symm ∘ (Φ ∘ γ) = γ := by
      funext t
      exact Φ.symm_apply_apply (γ t)
    rw [hcomp] at h'
    exact h'
  · exact isGeodesicCurveOn_comp Φ

/-- A smooth Riemannian isometry preserves all-time geodesics. -/
@[simp]
theorem isGeodesicCurve_comp_iff (Φ : RiemannianIsometry I J M N) {γ : ℝ → M} :
    IsGeodesicCurve J (Φ ∘ γ) ↔ IsGeodesicCurve I γ := by
  rw [← isGeodesicCurveOn_univ, ← isGeodesicCurveOn_univ]
  exact Φ.isGeodesicCurveOn_comp_iff

/-- A smooth Riemannian isometry carries the initial point of a geodesic to its image and the
initial velocity through its differential. -/
@[simp]
theorem isGeodesicCurveOnFrom_comp_iff (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} {p : M} {v : TangentSpace I p} :
    IsGeodesicCurveOnFrom J (Φ ∘ γ) s (Φ p) (mfderiv I J Φ p v) ↔
      IsGeodesicCurveOnFrom I γ s p v := by
  constructor
  · intro h
    have hgeod : IsGeodesicCurveOn I γ s := Φ.isGeodesicCurveOn_comp_iff.mp
      h.isGeodesicCurveOn
    refine ⟨hgeod, h.zero_mem, ?_⟩
    have hinitial := congrArg (tangentMap J I Φ.symm) h.initial_eq
    have hlift := tangentMap_curveVelocityLiftWithin
      (Φ.symm.mdifferentiableAt (Φ (γ 0)))
      (h.isGeodesicCurveOn.mdifferentiableOn 0 h.zero_mem)
      (h.isGeodesicCurveOn.uniqueDiffOn 0 h.zero_mem).uniqueMDiffWithinAt
    have hcomp : Φ.symm ∘ (Φ ∘ γ) = γ := by
      funext t
      exact Φ.symm_apply_apply (γ t)
    rw [hcomp] at hlift
    calc
      TotalSpace.mk' E (γ 0) (curveVelocityWithin I γ s 0) =
          curveVelocityLiftWithin I γ s 0 :=
        (curveVelocityLiftWithin_apply (I := I) γ s 0).symm
      _ = tangentMap J I Φ.symm (curveVelocityLiftWithin J (Φ ∘ γ) s 0) :=
        hlift.symm
      _ = tangentMap J I Φ.symm
          (TotalSpace.mk' F (Φ p) (mfderiv I J Φ p v)) := by
        simpa only [curveVelocityLiftWithin_apply] using hinitial
      _ = tangentMap J I Φ.symm
          (tangentMap I J Φ (TotalSpace.mk' E p v)) :=
        congrArg _ (Eq.symm (TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)))
      _ = TotalSpace.mk' E p v := by
        rw [coe_symm]
        exact Diffeomorph.tangentMap_symm_apply Φ.toDiffeomorph (by simp)
          (TotalSpace.mk' E p v)
  · intro h
    refine ⟨Φ.isGeodesicCurveOn_comp_iff.mpr h.isGeodesicCurveOn, h.zero_mem, ?_⟩
    have hinitial := congrArg (tangentMap I J Φ) h.initial_eq
    calc
      TotalSpace.mk' F ((Φ ∘ γ) 0) (curveVelocityWithin J (Φ ∘ γ) s 0) =
          curveVelocityLiftWithin J (Φ ∘ γ) s 0 :=
        (curveVelocityLiftWithin_apply (I := J) (Φ ∘ γ) s 0).symm
      _ = tangentMap I J Φ (curveVelocityLiftWithin I γ s 0) :=
        (tangentMap_curveVelocityLiftWithin (Φ.mdifferentiableAt (γ 0))
          (h.isGeodesicCurveOn.mdifferentiableOn 0 h.zero_mem)
          (h.isGeodesicCurveOn.uniqueDiffOn 0 h.zero_mem).uniqueMDiffWithinAt).symm
      _ = tangentMap I J Φ (TotalSpace.mk' E p v) := by
        simpa only [curveVelocityLiftWithin_apply] using hinitial
      _ = TotalSpace.mk' F (Φ p) (mfderiv I J Φ p v) :=
        TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)

end TauCeti.RiemannianIsometry

end
