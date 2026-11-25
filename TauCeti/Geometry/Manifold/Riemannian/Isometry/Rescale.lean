/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Local Riemannian isometries under conformal rescaling

Multiplying the source metric `gM` by a positive `C^n` function `cM` and the target metric `gN` by
a positive `C^m` function `cN` that agree along a map `f : M → N` (`cN ∘ f = cM`) scales both sides
of the inner-product preservation identity by the same positive factor at every point. Consequently
`f` is a local Riemannian isometry for the rescaled metrics if and only if it is a local Riemannian
isometry for the original metrics.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_rescale_iff`: compatible positive
  rescalings of the source and target metrics preserve and reflect local Riemannian isometries.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- Rescaling both source and target metrics by compatible positive factors preserves and reflects
local Riemannian isometries. -/
theorem isLocalRiemannianIsometry_rescale_iff {n m : ℕ∞ω}
    (gM : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (gN : ContMDiffRiemannianMetric J m F (fun z : N ↦ TangentSpace J z))
    {f : M → N}
    {cM : M → ℝ} (hcM : ContMDiff I 𝓘(ℝ) n cM) (hcM_pos : ∀ y, 0 < cM y)
    {cN : N → ℝ} (hcN : ContMDiff J 𝓘(ℝ) m cN) (hcN_pos : ∀ z, 0 < cN z)
    (hch : ∀ y, cN (f y) = cM y) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(gM.rescale cM hcM hcM_pos).toRiemannianMetric⟩
     letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) :=
      ⟨(gN.rescale cN hcN hcN_pos).toRiemannianMetric⟩
     TauCeti.IsLocalRiemannianIsometry I J f) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gM.toRiemannianMetric⟩
     letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
     TauCeti.IsLocalRiemannianIsometry I J f) := by
  have fwd :
      ∀ (gM' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
        (gN' : ContMDiffRiemannianMetric J m F (fun z : N ↦ TangentSpace J z))
        {cM' : M → ℝ} (hcM' : ContMDiff I 𝓘(ℝ) n cM') (hcM'_pos : ∀ y, 0 < cM' y)
        {cN' : N → ℝ} (hcN' : ContMDiff J 𝓘(ℝ) m cN') (hcN'_pos : ∀ z, 0 < cN' z),
        (∀ y, cN' (f y) = cM' y) →
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gM'.toRiemannianMetric⟩
         letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN'.toRiemannianMetric⟩
         TauCeti.IsLocalRiemannianIsometry I J f) →
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(gM'.rescale cM' hcM' hcM'_pos).toRiemannianMetric⟩
        letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) :=
          ⟨(gN'.rescale cN' hcN' hcN'_pos).toRiemannianMetric⟩
        TauCeti.IsLocalRiemannianIsometry I J f := by
    intro gM' gN' cM' hcM' hcM'_pos cN' hcN' hcN'_pos hch' hf
    obtain ⟨hf_smooth, hf_inv, hf_inner⟩ : ContMDiff I J ∞ f ∧
        (∀ y, (mfderiv I J f y).IsInvertible) ∧
        ∀ (y : M) (u v : TangentSpace I y),
          gN'.inner (f y) (mfderiv I J f y u) (mfderiv I J f y v) = gM'.inner y u v := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gM'.toRiemannianMetric⟩
      let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN'.toRiemannianMetric⟩
      exact ⟨hf.contMDiff, hf.isInvertible_mfderiv, fun y u v ↦ by
        simpa only [inner_riemannianBundle gN', inner_riemannianBundle gM'] using
          hf.inner_mfderiv y u v⟩
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(gM'.rescale cM' hcM' hcM'_pos).toRiemannianMetric⟩
    let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) :=
      ⟨(gN'.rescale cN' hcN' hcN'_pos).toRiemannianMetric⟩
    exact
      { contMDiff := hf_smooth
        isInvertible_mfderiv := hf_inv
        inner_mfderiv := fun y u v ↦ by
          rw [inner_riemannianBundle (gN'.rescale cN' hcN' hcN'_pos),
            inner_riemannianBundle (gM'.rescale cM' hcM' hcM'_pos),
            rescale_inner, rescale_inner, hch' y, hf_inner y u v] }
  refine ⟨fun hf ↦ ?_, fwd gM gN hcM hcM_pos hcN hcN_pos hch⟩
  have h := fwd (gM.rescale cM hcM hcM_pos) (gN.rescale cN hcN hcN_pos)
    (hcM.inv₀ fun y ↦ (hcM_pos y).ne') (fun y ↦ inv_pos.2 (hcM_pos y))
    (hcN.inv₀ fun z ↦ (hcN_pos z).ne') (fun z ↦ inv_pos.2 (hcN_pos z))
    (fun y ↦ by rw [hch y]) hf
  rwa [gM.rescale_inv_rescale, gN.rescale_inv_rescale] at h

end Bundle.ContMDiffRiemannianMetric
