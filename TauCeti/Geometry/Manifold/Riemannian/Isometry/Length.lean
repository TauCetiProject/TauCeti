/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Actual curve length under local Riemannian isometries

The native local-isometry differential preserves tangent norms, so the actual Riemannian
length integral is preserved on curves differentiable almost everywhere. In particular this
holds for `C¹` curves on closed parameter intervals, including in native boundary or corner
source manifolds. Differentiability is required only where the length density is integrated.

Ported from Riccardo Brasca's `ForTauCeti` formalization.
-/

public noncomputable section
open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology
namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
/-- A native local Riemannian isometry preserves actual curve length when the curve is
differentiable almost everywhere on the open parameter interval. -/
theorem IsLocalRiemannianIsometry.pathELength_comp_of_ae_mdifferentiableAt
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    Manifold.pathELength J (f ∘ γ) a b = Manifold.pathELength I γ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply lintegral_congr_ae
  filter_upwards [hγ] with t ht
  rw [mfderiv_comp_apply t (hf.mdifferentiableAt (γ t)) ht 1]
  obtain ⟨L, hL⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv (γ t)
  rw [← hL]
  exact L.eNorm_map _

/-- A native local Riemannian isometry preserves actual length of a `C¹` curve on a closed
parameter interval, including when the source manifold has boundary or corners. -/
theorem IsLocalRiemannianIsometry.pathELength_comp
    {f : M → N} (hf : IsLocalRiemannianIsometry I J f) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    Manifold.pathELength J (f ∘ γ) a b = Manifold.pathELength I γ a b := by
  apply hf.pathELength_comp_of_ae_mdifferentiableAt
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (hγ.mdifferentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
    (Icc_mem_nhds ht.1 ht.2)
end TauCeti
