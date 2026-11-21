/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth contractions of star-convex chart domains

An open subset `U` of an extended chart source `(extChartAt I x).source` in a `C^n` manifold
modelled on a real model with corners `I` whose image under `extChartAt I x` is star-convex with
respect to `extChartAt I x c` admits a global `C^n` contraction `F : ℝ × U → U` with
`F (0, z) = z` and `F (1, z) = c`
(`TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`).

The contraction is defined on all of `ℝ × U` by reparametrizing straight-line interpolation in
chart coordinates via `Real.smoothTransition`, so that the time parameter remains in `[0, 1]` and
the chart coordinates stay inside the star-convex image of `U`.

## Main results

* `TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`: an open subset of an
  extended chart source with star-convex chart image admits a `C^n` contraction.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}

/-- **Smooth contraction of an open chart domain with star-convex chart image.** Let `U` be an open
subset of `M` contained in `(extChartAt I x).source` whose image under `extChartAt I x` is
star-convex with respect to `extChartAt I x c` for `c : U`. Reparametrizing straight-line
interpolation towards `extChartAt I x c` in chart coordinates by `Real.smoothTransition` produces a
`C^n` map `F : ℝ × U → U` with `F (0, z) = z` and `F (1, z) = c`. -/
theorem exists_contMDiff_contraction_of_starConvex_image_extChartAt [IsManifold I n M]
    {x : M} {U : TopologicalSpace.Opens M} (hU : (U : Set M) ⊆ (extChartAt I x).source) (c : U)
    (hc : StarConvex ℝ (extChartAt I x c) (extChartAt I x '' (U : Set M))) :
    ∃ F : ℝ × U → U, ContMDiff (𝓘(ℝ).prod I) I n F ∧
      (∀ z, F (0, z) = z) ∧ (∀ z, F (1, z) = c) := by
  let φ : U → E := fun y ↦ extChartAt I x y.val
  have hφ : ContMDiff I 𝓘(ℝ, E) n φ :=
    (contMDiffOn_extChartAt (I := I) (x := x) (n := n)).comp_contMDiff contMDiff_subtypeVal
      fun y ↦ (extChartAt_source I x) ▸ hU y.property
  let G : ℝ × U → E := fun p ↦ φ c + (1 - Real.smoothTransition p.1) • (φ p.2 - φ c)
  have hG_im (p : ℝ × U) : G p ∈ extChartAt I x '' (U : Set M) :=
    hc.add_smul_sub_mem ⟨p.2.val, p.2.property, rfl⟩
      (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hG_tgt (p : ℝ × U) : G p ∈ (extChartAt I x).target := by
    obtain ⟨w, hwU, hw⟩ := hG_im p
    exact hw ▸ (extChartAt I x).map_source (hU hwU)
  have hF_U (p : ℝ × U) : (extChartAt I x).symm (G p) ∈ U := by
    obtain ⟨w, hwU, hw⟩ := hG_im p
    have heq : (extChartAt I x).symm (G p) = w := by
      rw [← hw]
      exact (extChartAt I x).left_inv (hU hwU)
    exact heq ▸ hwU
  have hlin : ContDiff ℝ n (fun q : ℝ × E ↦ φ c + (1 - Real.smoothTransition q.1) • (q.2 - φ c)) :=
    contDiff_const.add ((contDiff_const.sub
      (Real.smoothTransition.contDiff.comp contDiff_fst)).smul (contDiff_snd.sub contDiff_const))
  have hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) n G :=
    hlin.comp_contMDiff (contMDiff_fst.prodMk_space (hφ.comp contMDiff_snd))
  refine ⟨fun p ↦ ⟨(extChartAt I x).symm (G p), hF_U p⟩, ?_, ?_, ?_⟩
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiffOn_extChartAt_symm (I := I) (n := n) x).comp_contMDiff hG hG_tgt
  · intro z
    refine Subtype.ext ?_
    dsimp only [G, φ]
    rw [Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact (extChartAt I x).left_inv (hU z.property)
  · intro z
    refine Subtype.ext ?_
    dsimp only [G, φ]
    rw [Real.smoothTransition.one, sub_self, zero_smul, add_zero]
    exact (extChartAt I x).left_inv (hU c.property)

end TauCeti
