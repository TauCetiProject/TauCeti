/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Actual tangent pairings under local Riemannian isometries

Local isometries preserve pairings of actual native curve velocities, including one-sided
velocities at boundary endpoints and explicit transports between equal tangent fibres.
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
/-- A local Riemannian isometry preserves inner products of tangent vectors at equal
base points, including the native explicit equal-fibre transports. -/
theorem IsLocalRiemannianIsometry.inner_mfderiv_cast
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {x y : M} (hxy : x = y)
    (v : TangentSpace I x) (w : TangentSpace I y) :
    ⟪tangentSpaceCast J (f x) (f y) (mfderiv I J f x v), mfderiv I J f y w⟫_ℝ =
      ⟪tangentSpaceCast I x y v, w⟫_ℝ := by
  subst y
  exact hf.inner_mfderiv x v w

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
  have hσmap := Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (σ u))
    uniqueDiffWithinAt_univ hσ.mdifferentiableWithinAt
  simp only [Manifold.curveVelocityWithin_univ] at hσmap
  rw [hσmap, Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (γ a)) hs hγ]
  exact hf.inner_mfderiv_cast hbase _ _

/-- The actual differential of a local Riemannian isometry preserves tangent norms. -/
theorem IsLocalRiemannianIsometry.norm_mfderiv
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) (x : M) (v : TangentSpace I x) :
    ‖mfderiv I J f x v‖ = ‖v‖ := by
  simpa only [norm_eq_sqrt_real_inner] using congrArg Real.sqrt (hf.inner_mfderiv x v v)
/-- Local Riemannian isometries preserve genuine one-sided native curve speeds. -/
theorem IsLocalRiemannianIsometry.norm_curveVelocityWithin_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M}
    {T : Set ℝ} {t : ℝ} (hT : UniqueDiffWithinAt ℝ T t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) I γ T t) :
    ‖Manifold.curveVelocityWithin J (f ∘ γ) T t‖ =
      ‖Manifold.curveVelocityWithin I γ T t‖ := by
  rw [Manifold.curveVelocityWithin_map (hf.mdifferentiableAt (γ t)) hT hγ]
  exact hf.norm_mfderiv _ _
/-- Local Riemannian isometries preserve actual unrestricted native curve speeds. -/
theorem IsLocalRiemannianIsometry.norm_curveVelocity_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    ‖Manifold.curveVelocity J (f ∘ γ) t‖ = ‖Manifold.curveVelocity I γ t‖ := by
  simpa only [Manifold.curveVelocityWithin_univ] using
    hf.norm_curveVelocityWithin_comp uniqueDiffWithinAt_univ hγ.mdifferentiableWithinAt
end TauCeti
