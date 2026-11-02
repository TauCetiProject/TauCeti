/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SpecialFunctions.GramSchmidt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Measurable projections onto finite-dimensional ranges

The orthogonal projection onto the span of a finite measurable family is measurable as an
operator. Consequently the projection onto the range of a measurable family of operators
with finite-dimensional source is measurable, even when the rank changes.

Use normalized Gram–Schmidt vectors and sum their rank-one operators. Mathlib's convention
that zero vectors stay zero makes this formula valid across rank changes. No choice of a
basis of each varying range is needed. These projections encode measurable plane fields,
for example the ranges of derivatives of rectifiable parametrizations.
-/

public section

open InnerProductSpace Module Set

variable {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace X]

namespace TauCeti

/-- Orthogonal projections onto spans of finite measurable families are measurable,
including at parameters where the family is linearly dependent. -/
theorem measurable_starProjection_span {ι : Type*} [Finite ι]
    {v : ι → X → E} (hv : ∀ i, Measurable (v i))
    {U : X → Submodule 𝕜 E} [∀ x, (U x).HasOrthogonalProjection]
    (hU : ∀ x, Submodule.span 𝕜 (range fun i ↦ v i x) = U x) :
    Measurable fun x ↦ (U x).starProjection := by
  classical
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  have hspan (x : X) : Submodule.span 𝕜 (range fun i ↦ v (e i) x) = U x := by
    rw [← hU x]
    exact congrArg (Submodule.span 𝕜) (e.surjective.range_comp (fun i ↦ v i x))
  have hformula (x : X) :=
    starProjection_eq_sum_rankOne_gramSchmidtNormed (fun i ↦ v (e i) x) (hspan x)
  simp only [hformula]
  have hc : Continuous fun w : Fin (Fintype.card ι) → E ↦ ∑ i, rankOne 𝕜 (w i) (w i) :=
    continuous_finsetSum _ fun i _ ↦ by
      simp only [rankOne_def]
      exact ((ContinuousLinearMap.smulRightL 𝕜 E E).continuous.comp
        ((innerSL 𝕜).continuous.comp (continuous_apply i))).clm_apply (continuous_apply i)
  exact hc.measurable.comp (measurable_pi_iff.mpr fun i ↦
    Measurable.gramSchmidtNormed (𝕜 := 𝕜) (fun j ↦ hv (e j)) i)

end TauCeti

/-- Orthogonal projection onto the range of a measurable operator family with
finite-dimensional source is measurable. No constant-rank or injectivity hypothesis is
required, and the target may be infinite-dimensional. -/
@[fun_prop]
theorem Measurable.starProjection_range {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] {A : X → F →L[𝕜] E}
    (hA : Measurable A) : Measurable fun x ↦ (A x).range.starProjection := by
  let b := Module.finBasis 𝕜 F
  refine TauCeti.measurable_starProjection_span (𝕜 := 𝕜)
    (fun i ↦ hA.apply_continuousLinearMap (b i)) (fun x ↦ ?_)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe] using
    (by rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top] :
      Submodule.span 𝕜 (range ((A x).toLinearMap ∘ b)) = (A x).range)
