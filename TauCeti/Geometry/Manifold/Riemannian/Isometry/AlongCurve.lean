/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback

/-!
# Covariant differentiation along curves under Riemannian isometries

For a smooth Riemannian isometry `Φ : M → N`, the derivative along a curve of a vector field
pulled back from an ambient field on `N` commutes with the tangent map of `Φ`. This is the
along-curve form of the naturality of the Levi-Civita connection. It applies on arbitrary
parameter sets with unique derivatives, including closed intervals.

The underlying identity is the naturality of the Levi-Civita connection under isometries;
see do Carmo, *Riemannian Geometry*, Chapter 2, Theorem 3.6.
-/

public section

open Bundle CovariantDerivative Manifold VectorField
open scoped ContDiff Manifold

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

/-- Covariant differentiation along a curve of an ambient vector field commutes with a
Riemannian isometry. The field on the source is the pullback of the field on the target. -/
theorem mfderiv_alongCurveWithin_mpullback (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hY : MDiffAt (T% Y) (Φ (γ t))) :
    mfderiv I J Φ (γ t)
        (alongCurveWithin (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J Φ Y (γ r)) s t) =
      alongCurveWithin (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ Y ((Φ ∘ γ) r)) s t := by
  have hX : MDiffAt (T% (mpullback I J Φ Y)) (γ t) :=
    hY.mpullback_vectorField (Φ.toDiffeomorph.contMDiff.contMDiffAt)
      (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  rw [alongCurveWithin_pullback (leviCivitaConnection I M) γ (mpullback I J Φ Y)
      hs (hasMFDerivWithinAt_curveVelocityWithin hγ) hX]
  rw [alongCurveWithin_pullback (leviCivitaConnection J N) (Φ ∘ γ) Y hs
      (hasMFDerivWithinAt_curveVelocityWithin
        ((Φ.mdifferentiableAt (γ t)).comp_mdifferentiableWithinAt t hγ)) hY]
  rw [TauCeti.Manifold.curveVelocityWithin_map (Φ.mdifferentiableAt (γ t)) hs hγ]
  exact Φ.mfderiv_leviCivitaConnection_mpullback hY _

/-- For a differentiable curve, the unrestricted along-curve Levi-Civita derivative of a
pulled-back ambient field is carried to the derivative of that field along the image curve. -/
theorem mfderiv_alongCurve_mpullback (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {t : ℝ} {Y : Π y : N, TangentSpace J y}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hY : MDiffAt (T% Y) (Φ (γ t))) :
    mfderiv I J Φ (γ t)
        (alongCurve (leviCivitaConnection I M) γ
          (fun r ↦ mpullback I J Φ Y (γ r)) t) =
      alongCurve (leviCivitaConnection J N) (Φ ∘ γ)
        (fun r ↦ Y ((Φ ∘ γ) r)) t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact Φ.mfderiv_alongCurveWithin_mpullback uniqueDiffWithinAt_univ
    hγ.mdifferentiableWithinAt hY

end TauCeti.RiemannianIsometry

end
