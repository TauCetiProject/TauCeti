/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported.L1
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# Completion equivalence between `CompactlySupportedL1` and Bochner `L¹`

This file isolates the density and completion identification for
`TauCeti.CompactlySupportedL1 tag E μ` so users of the basic `L¹` wrapper or `liftCLM` do not have
to import Urysohn's lemma and `Lᵖ` density theory.

On a weakly locally compact `R₁` Borel space `X` equipped with a measure `μ` that is finite on
compact sets and inner regular with respect to compact sets on sets of finite measure,
`CompactlySupportedL1.toL1 𝕜` has dense range in `Lp E 1 μ` (`denseRange_toL1`,
`denseRange_toL1LI`) whenever `E` is a real normed space, and extends for any normed scalar ring
`𝕜` and complete target `E` to a `𝕜`-linear isometric equivalence
`CompactlySupportedL1.completionEquivL1 tag E μ 𝕜` between
`UniformSpace.Completion (CompactlySupportedL1 tag E μ)` and `Lp E 1 μ`.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported

namespace TauCeti.CompactlySupportedL1

section CompletionEquiv

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ] [R1Space X] [WeaklyLocallyCompactSpace X] [BorelSpace X]
  [NormedSpace ℝ E] [μ.InnerRegularCompactLTTop]

section DenseRange

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- `CompactlySupportedL1` has dense image in `Lp E 1 μ` on a weakly locally compact `R₁` Borel
space for a real normed space `E` and a measure finite on compact sets and inner regular for
compact sets on sets of finite measure. -/
theorem denseRange_toL1 : DenseRange (toL1 (tag := tag) (E := E) (μ := μ) 𝕜) := by
  refine (CompactlySupportedContinuousMap.denseRange_toLp ENNReal.one_ne_top μ 𝕜).mono ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨ofFun f, toL1_eq_toLp 𝕜 (ofFun f)⟩

/-- `toL1LI` has dense range in `Lp E 1 μ`. -/
theorem denseRange_toL1LI : DenseRange (toL1LI tag E μ 𝕜) := by
  have hfun : (⇑(toL1LI tag E μ 𝕜)) = ⇑(toL1 (tag := tag) (E := E) (μ := μ) 𝕜) :=
    funext fun f => toL1LI_apply 𝕜 f
  rw [DenseRange, hfun]
  exact denseRange_toL1 𝕜

end DenseRange

section Complete

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [CompleteSpace E]

variable (tag E μ) in
/-- **Identification of the abstract `L¹` completion with Bochner `L¹`**: `toL1` extends to a
`𝕜`-linear isometric equivalence between `UniformSpace.Completion (CompactlySupportedL1 tag E μ)`
and `Lp E 1 μ`, valid over any normed ring of scalars `𝕜`. -/
def completionEquivL1 : Completion (CompactlySupportedL1 tag E μ) ≃ₗᵢ[𝕜] Lp E 1 μ :=
  LinearIsometryEquiv.ofSurjective (toL1LI tag E μ 𝕜).fromCompletion
    ((toL1LI tag E μ 𝕜).fromCompletion_surjective_of_denseRange (denseRange_toL1LI 𝕜))

@[simp]
theorem completionEquivL1_coe (f : CompactlySupportedL1 tag E μ) :
    completionEquivL1 tag E μ 𝕜 f = toL1 𝕜 f := by
  rw [completionEquivL1, LinearIsometryEquiv.coe_ofSurjective,
    LinearIsometry.fromCompletion_apply_coe, toL1LI_apply]

@[simp]
theorem completionEquivL1_symm_toL1 (f : CompactlySupportedL1 tag E μ) :
    (completionEquivL1 tag E μ 𝕜).symm (toL1 𝕜 f) = f := by
  apply (completionEquivL1 tag E μ 𝕜).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_coe]

@[simp]
theorem completionEquivL1_symm_toLp (f : C_c(X, E)) :
    (completionEquivL1 tag E μ 𝕜).symm (CompactlySupportedContinuousMap.toLp 1 μ 𝕜 f) =
      ((ofFun f : CompactlySupportedL1 tag E μ) : Completion (CompactlySupportedL1 tag E μ)) := by
  rw [← toL1_eq_toLp 𝕜 (ofFun f), completionEquivL1_symm_toL1]

end Complete

end CompletionEquiv

end TauCeti.CompactlySupportedL1
