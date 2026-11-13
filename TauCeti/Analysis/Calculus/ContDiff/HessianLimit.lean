/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.HolderLimit

/-!
# C¹ and C² limits with Hölder derivatives

A locally uniform limit of eventually differentiable functions with a common derivative Hölder
bound and positive exponent is C¹ and inherits that bound. Approximating the derivative by fields
of linear maps gives the C² limit step for the difference quotient method. The domain is finite
dimensional and the codomain is complete.

The first-derivative filter limits and their weaker Cauchy and identification statements are
public in `FDeriv/HolderLimit.lean`. This file applies that API to the higher regularity upgrades.

The proofs are adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/IteratedDerivative/QuotientLimit.lean).
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} {l : Filter ι} [l.NeBot]
  {U : Set E} {f : E → F} {v : ι → E → F} {K α : ℝ≥0}

/-- A locally uniform limit of functions that are eventually differentiable with uniformly Hölder
derivatives on an open set is C¹ and inherits that bound, without a global derivative norm bound. -/
theorem contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ContDiffOn ℝ 1 f U ∧ HolderOnWith K α (fderiv ℝ f) U := by
  have hlim (x : E) (hx : x ∈ U) :=
    tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU hv hD hhol hx
  have hH : HolderOnWith K α (fderiv ℝ f) U := by
    refine HolderOnWith.of_dist_le fun x hx y hy => ?_
    exact le_of_tendsto ((hlim x hx).dist (hlim y hy))
      (hhol.mono fun m hm => hm.dist_le hx hy)
  refine ⟨?_, hH⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).2
  refine ⟨fun x hx => ?_, by simp, ?_⟩
  · exact (hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith
      hα hU hv hD hhol hx (hlim x hx)).differentiableAt.differentiableWithinAt
  · simpa only [contDiffOn_zero] using hH.continuousOn hα

/-- A differentiable function is C² with Hölder second derivative when its derivative is a
locally uniform limit of eventually differentiable linear-map-valued fields with a common
derivative Hölder bound. The fields need not themselves be derivatives of other functions. -/
theorem contDiffOn_two_and_holderOnWith_fderiv_fderiv_of_tendstoLocallyUniformlyOn
    {g : ι → E → E →L[ℝ] F}
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (g m) U)
    (hf : DifferentiableOn ℝ f U)
    (hD : TendstoLocallyUniformlyOn g (fderiv ℝ f) l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (g m)) U) :
    ContDiffOn ℝ 2 f U ∧ HolderOnWith K α (fderiv ℝ (fderiv ℝ f)) U := by
  obtain ⟨hC, hK⟩ := contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    hα hU hv hD hhol
  exact ⟨(contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).2 ⟨hf, by simp, hC⟩, hK⟩

end TauCeti
