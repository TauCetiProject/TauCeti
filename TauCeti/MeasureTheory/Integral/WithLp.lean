/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.Calculus.FDeriv.Integrable
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Energy of a map into a Euclidean product

For maps `f` and `g`, the derivative of `w ↦ (f w, g w)` into the Euclidean product
`WithLp 2 (F × E)` in a direction `v` has squared length `‖df v‖² + ‖dg v‖²`
(`TauCeti.norm_fderiv_toLp_prodMk_apply_sq`). Integrating over a set, the energy of the pair in
the direction `v` is the sum of the energies of `f` and `g`
(`TauCeti.setIntegral_norm_fderiv_toLp_prodMk_apply_sq`). For the graph `w ↦ (w, u w)` of a map
`u` and a unit vector `v`, this says that the energy of the graph is the measure of the set plus
the energy of `u`, the energy identity of Gromov's graph construction.

For a compactly supported `C¹` function `g` on `ℝ × E` (with the Euclidean norm), the derivative
in the normal direction `e₁` integrates over `Ioi a ×ˢ E` to minus the boundary integral over
`{a} × E` (`TauCeti.integral_prod_fderiv_normal`), and the derivative in a tangential direction
`(0, w)` integrates to zero (`TauCeti.integral_prod_fderiv_tangent`).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [MeasurableSpace G] {μ : Measure G}

/-- On a measurable set where `f` and `g` are differentiable, the energy in the direction `v` of
the map `w ↦ (f w, g w)` into the Euclidean product is the sum of the energies of `f` and `g`. -/
theorem setIntegral_norm_fderiv_toLp_prodMk_apply_sq {f : G → F} {g : G → E} {S : Set G}
    (hS : MeasurableSet S) (hf : ∀ y ∈ S, DifferentiableAt 𝕜 f y)
    (hg : ∀ y ∈ S, DifferentiableAt 𝕜 g y) (v : G)
    (hfi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 f y v‖ ^ 2) S μ)
    (hgi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 g y v‖ ^ 2) S μ) :
    ∫ y in S, ‖fderiv 𝕜 (fun w ↦ WithLp.toLp 2 (f w, g w)) y v‖ ^ 2 ∂μ =
      ∫ y in S, ‖fderiv 𝕜 f y v‖ ^ 2 ∂μ + ∫ y in S, ‖fderiv 𝕜 g y v‖ ^ 2 ∂μ := by
  rw [setIntegral_congr_fun hS fun y hy ↦ norm_fderiv_toLp_prodMk_apply_sq (hf y hy) (hg y hy) v,
    integral_add hfi hgi]

section Prod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The normal part of the divergence theorem on a half-space: for a compactly supported `C¹`
function `g` on `ℝ × E`, the integral of `∂_{e₁} g` over `Ioi a ×ˢ E` is minus the integral of `g`
over the boundary slice `{a} × E`, by the fundamental theorem of calculus on each normal line. -/
theorem integral_prod_fderiv_normal {g : WithLp 2 (ℝ × E) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (a : ℝ) :
    ∫ z, fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E)))
      ∂((volume.restrict (Ioi a)).prod volume) = -∫ y : E, g (WithLp.toLp 2 (a, y)) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  rw [integral_prod_symm _ (integrable_fderiv_apply_prod hg hgc a _), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  have he : IsClosedEmbedding (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y)
        (isClosedMap_prodMk_right y))
  have hline : ContDiff ℝ 1 (fun t : ℝ ↦ g (WithLp.toLp 2 (t, y))) :=
    hg.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
      (contDiff_id.prodMk contDiff_const))
  rw [← (hgc.comp_isClosedEmbedding he).integral_Ioi_deriv_eq hline a]
  exact integral_congr_ae (Eventually.of_forall fun t ↦
    ((hasDerivAt_comp_toLp_fst (hgd _)).deriv).symm)

/-- The tangential part of the divergence theorem on a half-space: the integral over `Ioi a ×ˢ E`
of a derivative of a compactly supported `C¹` function `g` along a direction `(0, w)` tangent to
the slices vanishes, since it integrates to zero on each slice `{t} × E`. -/
theorem integral_prod_fderiv_tangent {g : WithLp 2 (ℝ × E) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (a : ℝ) (w : E) :
    ∫ z, fderiv ℝ g (WithLp.toLp 2 z) (WithLp.toLp 2 (0, w))
      ∂((volume.restrict (Ioi a)).prod volume) = 0 := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  rw [integral_prod _ (integrable_fderiv_apply_prod hg hgc a _)]
  refine (integral_congr_ae (Eventually.of_forall fun t ↦ ?_)).trans (integral_zero _ _)
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (t, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight t)
        (isClosedMap_prodMk_left t))
  have hslice : ContDiff ℝ 1 (fun y : E ↦ g (WithLp.toLp 2 (t, y))) :=
    hg.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
      (contDiff_const.prodMk contDiff_id))
  have hsc := hgc.comp_isClosedEmbedding he
  simp only [← fderiv_comp_toLp_snd (hgd _)]
  exact integral_fderiv_apply_eq_zero_of_hasCompactSupport hslice hsc w

end Prod

end TauCeti
