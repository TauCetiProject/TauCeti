/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Tangent

/-!
# Covariant differentiation along curves under local Riemannian isometries

For a local Riemannian isometry `f : M → N`, covariant differentiation along a curve commutes
with the tangent map of `f`. This is the along-curve form of the naturality of the Levi-Civita
connection. It applies to differentiable tangent fields along arbitrary parameter sets with
unique derivatives, including closed intervals.

Naturality for arbitrary tangent fields along a curve, rather than only for fields pulled back
from an ambient vector field, is what allows intrinsic equations involving covariant derivatives
along curves to be transported by an isometry. The main example is the geodesic equation: the
velocity field of a curve is generally not the restriction of an ambient vector field.

## Main results

* `mfderiv_alongCurveWithin_mpullback`: naturality for a field pulled back from the target.
* `mfderiv_alongCurveWithin`: naturality for an arbitrary differentiable tangent field along the
  curve.
* `mfderiv_alongCurve`: the unrestricted form.

See do Carmo, *Riemannian Geometry*, Chapter 2, Theorem 3.6.
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable {f : M → N}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- Covariant differentiation along a curve of an ambient vector field commutes with a
local Riemannian isometry. The field on the source is the pullback of the field on the target. -/
theorem mfderiv_alongCurveWithin_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hY : MDiffAt (T% Y) (f (γ t))) :
    mfderiv I J f (γ t)
        (alongCurveWithin (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J f Y (γ r)) s t) =
      alongCurveWithin (leviCivitaConnection J N) (f ∘ γ)
        (fun r ↦ Y ((f ∘ γ) r)) s t := by
  have hX : MDiffAt (T% (mpullback I J f Y)) (γ t) :=
    hY.mpullback_vectorField (hf.contMDiff.contMDiffAt)
      (hf.isInvertible_mfderiv _) (by simp)
  rw [alongCurveWithin_pullback (leviCivitaConnection I M) γ (mpullback I J f Y)
      hs (hasMFDerivWithinAt_curveVelocityWithin hγ) hX]
  rw [alongCurveWithin_pullback (leviCivitaConnection J N) (f ∘ γ) Y hs
      (hasMFDerivWithinAt_curveVelocityWithin
        ((hf.mdifferentiableAt (γ t)).comp_mdifferentiableWithinAt t hγ)) hY]
  rw [TauCeti.Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (γ t)) hs hγ]
  exact hf.mfderiv_leviCivitaConnection_mpullback hY _

/-- For a differentiable curve, the unrestricted along-curve Levi-Civita derivative of a
pulled-back ambient field is carried to the derivative of that field along the image curve. -/
theorem mfderiv_alongCurve_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hY : MDiffAt (T% Y) (f (γ t))) :
    mfderiv I J f (γ t)
        (alongCurve (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J f Y (γ r)) t) =
      alongCurve (leviCivitaConnection J N) (f ∘ γ)
        (fun r ↦ Y ((f ∘ γ) r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact hf.mfderiv_alongCurveWithin_mpullback uniqueDiffWithinAt_univ
    hγ.mdifferentiableWithinAt hY

/-! ### Arbitrary tangent fields along a curve -/

/-- **Naturality of covariant differentiation along a curve under a local Riemannian isometry.**
The differential of an isometry carries the Levi-Civita derivative of a differentiable tangent
field along `γ` to the derivative of the transported field along `f ∘ γ`.

The hypothesis `hV` expresses differentiability of the tangent field in local bundle
coordinates. -/
theorem mfderiv_alongCurveWithin (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hV : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ V (γ t)) s t) :
    mfderiv I J f (γ t)
        (alongCurveWithin (leviCivitaConnection I M) γ V s t) =
      alongCurveWithin (leviCivitaConnection J N) (f ∘ γ)
        (fun r ↦ mfderiv I J f (γ r) (V r)) s t := by
  let W : ∀ r, TangentSpace J ((f ∘ γ) r) :=
    fun r ↦ mfderiv I J f (γ r) (V r)
  have hfγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) J (f ∘ γ) s t :=
    (hf.mdifferentiableAt (γ t)).comp_mdifferentiableWithinAt t hγ
  have hfV : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (f ∘ γ)
        (fun r ↦ mfderiv I J f (γ r) (V r)) (f (γ t))) s t :=
    hf.contMDiff.contMDiffAt.differentiableWithinAt_sectionCoord_mfderiv (by simp) hγ hV
  -- Test both sides against pullbacks of differentiable fields `Y` on the target: the
  -- metric-compatible product rules on source and target differentiate the same inner product.
  refine injective_inner_mdifferentiableAt_section J F (TangentSpace J) (f (γ t)) ?_
  ext Y hY
  dsimp only
  let X : ∀ x : M, TangentSpace I x := mpullback I J f Y
  have hX : MDiffAt (T% X) (γ t) :=
    hY.mpullback_vectorField (hf.contMDiff.contMDiffAt)
      (hf.isInvertible_mfderiv _) (by simp)
  have hXcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ (fun r ↦ X (γ r))
      (hX.comp_mdifferentiableWithinAt t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hYcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := F) (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r)) (f (γ t))) s t :=
    differentiableWithinAt_sectionCoord (f ∘ γ) (fun r ↦ Y ((f ∘ γ) r))
      (hY.comp_mdifferentiableWithinAt t hfγ)
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))
  have hsource :=
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).derivWithin_inner_alongCurveWithin
      hs hγ hV hXcoord
  have htarget :=
    (isMetricCompatible_leviCivitaConnection (I := J) (M := N)).derivWithin_inner_alongCurveWithin
      hs hfγ hfV hYcoord
  have hXY (r : ℝ) : mfderiv I J f (γ r) (X (γ r)) = Y ((f ∘ γ) r) := by
    dsimp only [X, Function.comp_apply]
    exact hf.mfderiv_apply_mpullback Y (γ r)
  have hinner : (fun r ↦ inner ℝ (V r) (X (γ r))) =
      fun r ↦ inner ℝ (W r) (Y ((f ∘ γ) r)) := by
    funext r
    dsimp only [W]
    rw [← hf.inner_mfderiv (γ r), hXY]
  have hderiv : derivWithin (fun r ↦ inner ℝ (V r) (X (γ r))) s t =
      derivWithin (fun r ↦ inner ℝ (W r) (Y ((f ∘ γ) r))) s t :=
    congrArg (fun f : ℝ → ℝ ↦ derivWithin f s t) hinner
  have htransport := hf.mfderiv_alongCurveWithin_mpullback hs hγ hY
  have hleft :
      inner ℝ
          (mfderiv I J f (γ t)
            (alongCurveWithin (leviCivitaConnection I M) γ V s t))
          (Y (f (γ t))) =
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s t) (X (γ t)) := by
    rw [← hf.inner_mfderiv (γ t), hXY]
    rfl
  have hsecond :
      inner ℝ (V t)
          (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ X (γ r)) s t) =
        inner ℝ (W t)
          (alongCurveWithin (leviCivitaConnection J N) (f ∘ γ)
            (fun r ↦ Y ((f ∘ γ) r)) s t) := by
    rw [← htransport, hf.inner_mfderiv]
  rw [hleft]
  simp only [Function.comp_apply] at htarget hderiv hsecond ⊢
  dsimp only [W] at hderiv hsecond
  linarith [hsource, htarget, hderiv, hsecond]

/-- The unrestricted form of naturality of covariant differentiation along a curve under a
local Riemannian isometry. -/
theorem mfderiv_alongCurve (hf : IsLocalRiemannianIsometry I J f)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    mfderiv I J f (γ t) (alongCurve (leviCivitaConnection I M) γ V t) =
      alongCurve (leviCivitaConnection J N) (f ∘ γ)
        (fun r ↦ mfderiv I J f (γ r) (V r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact hf.mfderiv_alongCurveWithin uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
    hV.differentiableWithinAt

end TauCeti.IsLocalRiemannianIsometry

end
