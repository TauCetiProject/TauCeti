/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Strong measurability of operator-valued functions on a finite-dimensional space

A function `T : α → E →L[𝕜] F` is almost everywhere strongly measurable for the operator norm
exactly when each orbit `a ↦ T a v` is, provided `E` is finite-dimensional
(`TauCeti.aestronglyMeasurable_clm_apply_iff`). One direction is Mathlib's
`MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap` and holds in general. For the other,
`T a = ∑ i, (b.coord i).smulRight (T a (b i))` for a basis `b` of `E`, a finite sum of continuous
linear images of the orbits `a ↦ T a (b i)`.

In infinite dimension the orbit condition is weaker in general: the strong operator topology and
the norm topology then give different notions of measurability. Measurability of the orbits is
what is checkable for time-dependent operators, for instance `t ↦ A t v w` for the energy forms of
a parabolic equation; this file upgrades it to the operator norm once the operators are restricted
to a finite-dimensional subspace.

The file also records that evaluating an almost everywhere strongly measurable operator-valued
function on an almost everywhere strongly measurable vector field gives an almost everywhere
strongly measurable function (`MeasureTheory.AEStronglyMeasurable.clm_apply`), in any dimension.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α 𝕜 E F : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a finite-dimensional space, an operator-valued function is almost everywhere strongly
measurable for the operator norm exactly when each of its orbits `a ↦ T a v` is. -/
theorem aestronglyMeasurable_clm_apply_iff {T : α → E →L[𝕜] F} :
    AEStronglyMeasurable T μ ↔ ∀ v, AEStronglyMeasurable (fun a ↦ T a v) μ := by
  refine ⟨fun h v ↦ h.apply_continuousLinearMap v, fun h ↦ ?_⟩
  let b := Module.finBasis 𝕜 E
  have hT : T = fun a ↦ ∑ i, (b.coord i).toContinuousLinearMap.smulRight (T a (b i)) := by
    ext a v
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, ← map_smul, ← map_sum,
      b.sum_repr]
  rw [hT]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
    (ContinuousLinearMap.smulRightL 𝕜 E F
      (b.coord i).toContinuousLinearMap).continuous.comp_aestronglyMeasurable (h (b i))

end TauCeti

namespace MeasureTheory

variable {α 𝕜 E F : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Evaluating an almost everywhere strongly measurable operator-valued function on an almost
everywhere strongly measurable vector field gives an almost everywhere strongly measurable
function. Applied twice, it covers fields of bilinear forms `x ↦ B x (p x) (q x)`. -/
theorem AEStronglyMeasurable.clm_apply {T : α → E →L[𝕜] F} {p : α → E}
    (hT : AEStronglyMeasurable T μ) (hp : AEStronglyMeasurable p μ) :
    AEStronglyMeasurable (fun a ↦ T a (p a)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hT.prodMk hp)

end MeasureTheory
