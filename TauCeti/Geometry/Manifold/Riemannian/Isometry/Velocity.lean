/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Actual tangent pairings under local Riemannian isometries

Local isometries preserve pairings of actual native curve velocities, including one-sided
velocities at boundary endpoints and explicit transports between equal tangent fibres.

Adapted from Riccardo Brasca's `ForTauCeti` formalization.
-/

public noncomputable section
open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace
namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
/-- Local Riemannian isometries preserve the pairing of two one-sided native curve
velocities at equal base points, with independent parameter sets. -/
theorem IsLocalRiemannianIsometry.inner_curveVelocityWithin_curveVelocityWithin_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ σ : ℝ → M} {a u : ℝ}
    {s T : Set ℝ} (hbase : σ u = γ a) (hT : UniqueDiffWithinAt ℝ T u)
    (hs : UniqueDiffWithinAt ℝ s a)
    (hσ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I σ T u)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s a) :
    ⟪tangentSpaceCast J (f (σ u)) (f (γ a))
        (Manifold.curveVelocityWithin J (f ∘ σ) T u),
      Manifold.curveVelocityWithin J (f ∘ γ) s a⟫_ℝ =
      ⟪tangentSpaceCast I (σ u) (γ a) (Manifold.curveVelocityWithin I σ T u),
        Manifold.curveVelocityWithin I γ s a⟫_ℝ := by
  rw [Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (σ u)) hT hσ,
    Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (γ a)) hs hγ]
  exact hf.inner_mfderiv_cast hbase _ _

/-- Native local isometries preserve the pairing between an endpoint-curve velocity and a
one-sided central-curve velocity. Both tangent vectors use their actual native carriers. -/
theorem IsLocalRiemannianIsometry.inner_curveVelocity_curveVelocityWithin_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ σ : ℝ → M} {a u : ℝ}
    {s : Set ℝ} (hbase : σ u = γ a) (hs : UniqueDiffWithinAt ℝ s a)
    (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I σ u)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s a) :
    ⟪tangentSpaceCast J (f (σ u)) (f (γ a))
        (Manifold.curveVelocity J (f ∘ σ) u),
      Manifold.curveVelocityWithin J (f ∘ γ) s a⟫_ℝ =
      ⟪tangentSpaceCast I (σ u) (γ a) (Manifold.curveVelocity I σ u),
        Manifold.curveVelocityWithin I γ s a⟫_ℝ := by
  simpa only [Manifold.curveVelocityWithin_univ] using
    hf.inner_curveVelocityWithin_curveVelocityWithin_comp hbase uniqueDiffWithinAt_univ hs
      hσ.mdifferentiableWithinAt hγ

/-- Local Riemannian isometries preserve genuine one-sided native curve speeds. -/
@[simp]
theorem IsLocalRiemannianIsometry.norm_curveVelocityWithin_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M}
    {T : Set ℝ} {t : ℝ} (hT : UniqueDiffWithinAt ℝ T t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) I γ T t) :
    ‖Manifold.curveVelocityWithin J (f ∘ γ) T t‖ =
      ‖Manifold.curveVelocityWithin I γ T t‖ := by
  rw [Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (γ t)) hT hγ]
  exact hf.norm_mfderiv _ _
/-- Local Riemannian isometries preserve actual unrestricted native curve speeds. -/
@[simp]
theorem IsLocalRiemannianIsometry.norm_curveVelocity_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    ‖Manifold.curveVelocity J (f ∘ γ) t‖ = ‖Manifold.curveVelocity I γ t‖ := by
  simpa only [Manifold.curveVelocityWithin_univ] using
    hf.norm_curveVelocityWithin_comp uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
end TauCeti
