/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Measure-level standard Borel disintegration transport

This file provides the measure-level counterpart of Mathlib's
`ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal` from
`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean`: transporting a disintegration
`ρ.fst ⊗ₘ η = ρ.map (Prod.map id (embeddingReal Ω))` along `embeddingReal Ω` to a disintegration
`ρ.fst ⊗ₘ Kernel.borelMarkovFromReal Ω η = ρ` on a nonempty standard Borel space `Ω`.

## Main statements

* `MeasureTheory.Measure.compProd_fst_borelMarkovFromReal`: transporting a real-valued
  disintegrating kernel `η : Kernel β ℝ` to a disintegrating kernel `Kernel.borelMarkovFromReal Ω η`
  for an s-finite measure `ρ : Measure (β × Ω)`.
-/

public section

noncomputable section

open ProbabilityTheory

namespace MeasureTheory.Measure

/-- Measure-level counterpart of `ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal`:
if an s-finite kernel `η : Kernel β ℝ` disintegrates the embedded measure
`ρ.map (Prod.map id (embeddingReal Ω))` of an s-finite measure `ρ : Measure (β × Ω)` on a
nonempty standard Borel space `Ω`, then `Kernel.borelMarkovFromReal Ω η` disintegrates `ρ`. -/
theorem compProd_fst_borelMarkovFromReal {β Ω : Type*} [MeasurableSpace β] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (ρ : Measure (β × Ω)) [SFinite ρ] (η : Kernel β ℝ)
    [IsSFiniteKernel η]
    (hη : ρ.fst ⊗ₘ η = ρ.map (Prod.map (id : β → β) (embeddingReal Ω))) :
    ρ.fst ⊗ₘ Kernel.borelMarkovFromReal Ω η = ρ := by
  let e : Ω → ℝ := embeddingReal Ω
  have he : Measurable e := (measurableEmbedding_embeddingReal Ω).measurable
  let κ : Kernel Unit (β × Ω) := Kernel.const Unit ρ
  have hfst_map : (ρ.map (Prod.map (id : β → β) e)).fst = ρ.fst :=
    Measure.fst_map_prodMk measurable_fst (he.comp measurable_snd)
  have hη' : (κ.map (Prod.map (id : β → β) e)).fst ⊗ₖ η.prodMkLeft Unit =
      κ.map (Prod.map (id : β → β) e) := by
    rw [Kernel.map_const _ (measurable_id.prodMap he), Kernel.fst_const, hfst_map,
      Kernel.const_compProd_prodMkLeft, hη]
  have hdis := Kernel.compProd_fst_borelMarkovFromReal κ (η.prodMkLeft Unit) hη'
  have hprod : Kernel.borelMarkovFromReal Ω (η.prodMkLeft Unit) =
      (Kernel.borelMarkovFromReal Ω η).prodMkLeft Unit := by
    ext p : 1
    rw [Kernel.prodMkLeft_apply, Kernel.borelMarkovFromReal_apply, Kernel.borelMarkovFromReal_apply,
      Kernel.prodMkLeft_apply]
  rw [Kernel.fst_const, hprod, Kernel.const_compProd_prodMkLeft] at hdis
  simpa [κ] using congrArg (fun k ↦ k ()) hdis

end MeasureTheory.Measure
