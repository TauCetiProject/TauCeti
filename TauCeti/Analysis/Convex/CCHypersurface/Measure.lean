/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Convex.CCHypersurface.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Additive-Haar nullity of `c - c` and Lipschitz hypersurfaces

In a finite-dimensional real inner product space `E`, every Borel measurable graph
`{x | ⟪x, e⟫ = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}` over the orthogonal hyperplane of a unit
vector `e` has additive-Haar measure zero (`TauCeti.addHaar_setOf_inner_eq_eq_zero`), by Fubini's
theorem in orthogonal line coordinates. Consequently, both Lipschitz hypersurfaces and `c - c`
hypersurfaces are additive-Haar null (`TauCeti.IsLipschitzHypersurface.addHaar_eq_zero`,
`TauCeti.IsCCHypersurface.addHaar_eq_zero`).
-/

public section

noncomputable section

open Filter MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every Borel measurable graph `{x | ⟪x, e⟫ = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}` over
the orthogonal complement of a unit vector `e` has additive-Haar measure zero. -/
theorem addHaar_setOf_inner_eq_eq_zero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {e : E} (he : ‖e‖ = 1) (h : ↥(ℝ ∙ e)ᗮ → ℝ)
    (hmeas : MeasurableSet {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}) :
    μ {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} = 0 := by
  refine Measure.addHaar_eq_zero_of_prod_mk_preimage_image_eq_zero μ volume volume
    (orthogonalLineEquiv e he).symm hmeas
    (Eventually.of_forall fun y => measure_mono_null (t := {h y}) ?_ (by simp))
  rintro r ⟨x, hx, hφx⟩
  have hx_eq : x = (y : E) + r • e := by
    simpa [orthogonalLineEquiv_apply] using
      (ContinuousLinearEquiv.symm_apply_eq (orthogonalLineEquiv e he)).1 hφx
  rw [mem_ofPred_eq, hx_eq, orthogonalProjectionOnto_coe_add_smul,
    real_inner_comm e _, inner_add_smul e he] at hx
  exact mem_singleton_iff.2 hx

/-- Every Lipschitz hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsLipschitzHypersurface.addHaar_eq_zero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {s : Set E} (hs : IsLipschitzHypersurface s) : μ s = 0 := by
  have hmeas := hs.measurableSet
  rcases isLipschitzHypersurface_def.1 hs with ⟨e, he, _, h, _, rfl⟩
  exact addHaar_setOf_inner_eq_eq_zero μ he h hmeas

/-- Every `c - c` hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsCCHypersurface.addHaar_eq_zero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {s : Set E} (hs : IsCCHypersurface s) : μ s = 0 := by
  have hmeas := hs.measurableSet
  rcases isCCHypersurface_def.1 hs with ⟨e, he, f, g, _, _, _, _, rfl⟩
  exact addHaar_setOf_inner_eq_eq_zero μ he (fun y => f y - g y) hmeas

end TauCeti
