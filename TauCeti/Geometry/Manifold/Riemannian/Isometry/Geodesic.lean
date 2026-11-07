/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.AlongCurve.Acceleration

/-!
# Geodesics under Riemannian isometries

A local Riemannian isometry carries geodesics to geodesics. This holds on an arbitrary
parameter set with unique derivatives, and the tangent map carries the initial velocity to the
initial velocity of the image geodesic. For a global isometry, applying the result to its inverse
gives equivalences for interval-aware geodesics, all-time geodesics, and geodesics with initial
data.

This is the geodesic form of naturality of the Levi-Civita connection; see do Carmo,
*Riemannian Geometry*, Chapter 2, Theorem 3.6, and Chapter 3, Section 2. The equivalence for
geodesics with prescribed initial data is the input for showing that an isometry preserves
maximal geodesic intervals and intertwines the exponential maps, `Φ ∘ exp_p = exp_{Φ p} ∘ dΦ_p`.

## Main results

* `IsLocalRiemannianIsometry.isGeodesicCurveOn_comp`: local isometries preserve geodesics.
* `IsLocalRiemannianIsometry.isGeodesicCurveOn_comp_iff`: reflection for `C²` source curves.
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

namespace TauCeti

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

namespace IsLocalRiemannianIsometry

/-- A local Riemannian isometry carries geodesics to geodesics on the same parameter set. -/
theorem isGeodesicCurveOn_comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {s : Set ℝ} (h : IsGeodesicCurveOn I γ s) :
    IsGeodesicCurveOn J (f ∘ γ) s where
  uniqueDiffOn := h.uniqueDiffOn
  contMDiffOn := (hf.contMDiff.of_le (by norm_num)).comp_contMDiffOn h.contMDiffOn
  accelerationWithin_eq_zero t ht :=
    (hf.accelerationWithin_comp_eq_zero_iff h.uniqueDiffOn h.contMDiffOn ht).2
      (h.accelerationWithin_eq_zero t ht)

/-- A `C²` curve is a geodesic exactly when its image under a local Riemannian isometry is.
The source regularity prevents discontinuous changes between different local sheets. -/
theorem isGeodesicCurveOn_comp_iff {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {s : Set ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) :
    IsGeodesicCurveOn J (f ∘ γ) s ↔ IsGeodesicCurveOn I γ s := by
  refine ⟨fun h ↦ ⟨h.uniqueDiffOn, hγ, fun t ht ↦ ?_⟩, hf.isGeodesicCurveOn_comp⟩
  exact (hf.accelerationWithin_comp_eq_zero_iff h.uniqueDiffOn hγ ht).1
    (h.accelerationWithin_eq_zero t ht)

end IsLocalRiemannianIsometry

namespace RiemannianIsometry

/-- A smooth Riemannian isometry preserves the geodesic equation on every parameter set with
unique derivatives. -/
@[simp]
theorem isGeodesicCurveOn_comp_iff (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} :
    IsGeodesicCurveOn J (Φ ∘ γ) s ↔ IsGeodesicCurveOn I γ s := by
  constructor
  · intro h
    have h' := Φ.symm.isLocalRiemannianIsometry.isGeodesicCurveOn_comp h
    have hcomp : Φ.symm ∘ (Φ ∘ γ) = γ := by
      funext t
      exact Φ.symm_apply_apply (γ t)
    rw [hcomp] at h'
    exact h'
  · exact Φ.isLocalRiemannianIsometry.isGeodesicCurveOn_comp

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
          (h.isGeodesicCurveOn.mdifferentiableOn 0 h.zero_mem)).symm
      _ = tangentMap I J Φ (TotalSpace.mk' E p v) := by
        simpa only [curveVelocityLiftWithin_apply] using hinitial
      _ = TotalSpace.mk' F (Φ p) (mfderiv I J Φ p v) :=
        TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)

end RiemannianIsometry

end TauCeti

end
