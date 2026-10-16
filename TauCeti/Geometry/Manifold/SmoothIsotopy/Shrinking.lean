/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Shrinking smooth embeddings near their centre

Positive dilations of the source give a smooth isotopy of an embedding of a real normed
space, fixing the image of the origin. A bounded part of the source can consequently be
moved inside any neighbourhood of that image. For a star-convex source subset, the motion
stays inside its original image throughout the isotopy.

This is the shrinking step used to compare ball embeddings in a common ambient chart.
It gives an isotopy through embeddings; extending it to an ambient isotopy is a separate
assertion. Neither finite dimensionality nor compactness of the source is required.

Reference: M. Hirsch, *Differential Topology*, GTM 33, Chapter 4, §6, Theorem 6.6.
The bounded-set shrinking argument uses Mathlib's von Neumann boundedness and small-sets API.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti.SmoothEmbedding

variable {E F H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N]
  {n : ℕ∞ω}

/-- Reparametrize an embedding by positive source dilations, from scale one to scale `c`.
The image of the origin remains fixed, and every time slice is an embedding. -/
def shrinkingIsotopy (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) {c : ℝ} (hc : 0 < c) :
    SmoothIsotopy f.toContMDiffMap
      (f.toContMDiffMap.comp (c • ContMDiffMap.id)) where
  toContMDiffMap := ⟨fun p => f ((1 - (p.1 : ℝ) + (p.1 : ℝ) * c) • p.2),
    f.contMDiff.comp (((contMDiff_const.sub
      (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).add
        ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).mul contMDiff_const)).smul
          contMDiff_snd)⟩
  map_zero_left x := by simp
  map_one_left x := by
    simp only [ContMDiffMap.comp_apply, ContMDiffMap.coe_smul, Pi.smul_apply]
    dsimp [ContMDiffMap.id]
    simp
  isSmoothEmbedding t := by
    have hpos : 0 < 1 - (t : ℝ) + (t : ℝ) * c := by
      have := t.2.1
      have := t.2.2
      by_cases ht : (t : ℝ) = 0
      · simp [ht]
      · have := mul_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) hc
        linarith
    let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 _ hpos.ne')
    simpa [e, Function.comp_def] using
      isSmoothEmbedding_comp_continuousLinearEquiv e f.isSmoothEmbedding

/-- The shrinking motion interpolates linearly between its positive dilation factors. -/
@[simp] theorem shrinkingIsotopy_apply (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {c : ℝ} (hc : 0 < c) (p : unitInterval × E) :
    f.shrinkingIsotopy hc p = f ((1 - (p.1 : ℝ) + (p.1 : ℝ) * c) • p.2) := (rfl)

/-- Shrinking a star-convex subset never leaves its original embedded image. -/
theorem shrinkingIsotopy_mapsTo_image (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) {s : Set E} (hs : StarConvex ℝ 0 s)
    (t : unitInterval) : MapsTo (fun x => f.shrinkingIsotopy hc (t, x)) s (f '' s) := by
  intro x hx
  have h₀ : 0 ≤ 1 - (t : ℝ) + (t : ℝ) * c := by
    have := t.2.1
    have := t.2.2
    positivity
  have h₁ : 1 - (t : ℝ) + (t : ℝ) * c ≤ 1 := by
    have := t.2.1
    nlinarith
  exact ⟨_, hs.smul_mem hx h₀ h₁, (f.shrinkingIsotopy_apply hc (t, x)).symm⟩

/-- A bounded part of a smooth embedding can be mapped into any neighbourhood of its
centre at the endpoint of a shrinking isotopy. For a star-convex source subset,
`shrinkingIsotopy_mapsTo_image` gives containment in its original image throughout the motion. -/
theorem exists_shrinkingIsotopy_mapsTo (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {s : Set E} (hs : Bornology.IsBounded s) {U : Set N} (hU : U ∈ 𝓝 (f 0)) :
    ∃ (c : ℝ) (hc : 0 < c), c ≤ 1 ∧
      MapsTo (fun x => f.shrinkingIsotopy hc (1, x)) s U := by
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : E) := f.contMDiff.continuous.continuousAt hU
  have hnear : ∀ᶠ c : ℝ in 𝓝 0, MapsTo (fun x => c • x) s (f ⁻¹' U) := by
    simpa only [mapsTo_iff_image_subset, image_smul] using
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hs).tendsto_smallSets_nhds.eventually
        (eventually_smallSets_subset.mpr hpre)
  obtain ⟨a, b, hab, hsmall⟩ := hnear.exists_Ioo_subset
  obtain ⟨c, hc, hcb⟩ := exists_between (lt_min hab.2 (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, hc, (hcb.trans_le (min_le_right _ _)).le, ?_⟩
  intro x hx
  simp only [shrinkingIsotopy_apply]
  simpa using hsmall ⟨hab.1.trans hc, hcb.trans_le (min_le_left _ _)⟩ hx

end TauCeti.SmoothEmbedding
