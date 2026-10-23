/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Process.Tail.ConditionalLaw.Basic
import TauCeti.Probability.DeFinetti.ViaL2.BlockFactorization
import TauCeti.Probability.DeFinetti.ConditionalCommonEnding
import TauCeti.Probability.Process.Tail.ConditionalLaw.BlockCylinder

/-!
# Conditional i.i.d.-ness of a contractable process, via `L²`

A contractable process on a standard Borel state space is conditionally i.i.d. with
`tailConditionalProbabilityMeasure μ X` as its directing measure:

```text
ConditionallyIIDWith μ X (tailConditionalProbabilityMeasure μ X).
```

The `L²` block factorization gives the conditional expectation of an indicator block given
`tailProcess X`, for an arbitrary strictly monotone selection. Testing it on a directing-measure
event uses `measure_inter_blockCylinder_eq_setLIntegral_of_condExp` from
`Process/Tail/ConditionalLaw/BlockCylinder.lean`, which applies to every tail-measurable event.
The resulting measure identity supplies the joint-rectangle criterion
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral`.

The witness is preserved: the conclusion names `tailConditionalProbabilityMeasure μ X` itself rather
than asserting an unnamed existential.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal

namespace TauCeti

namespace Probability

namespace Contractable

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A contractable process on a standard Borel space is conditionally i.i.d.**, with
`tailConditionalProbabilityMeasure μ X` as its directing measure.

This conditions on the directing measure itself. It does not assert conditional independence given
the whole of `tailProcess X`, which would additionally require identifying the σ-algebra generated
by `tailConditionalProbabilityMeasure μ X` with the tail. -/
theorem conditionallyIIDWith_directingProbabilityMeasure [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIIDWith μ X (tailConditionalProbabilityMeasure μ X) := by
  have hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    tailProcess_le_ambient 0 fun c _ => hX_meas c
  refine conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral
    (fun n => (hX_meas n).aemeasurable) (measurable_tailConditionalProbabilityMeasure hTail) ?_
  intro r k hk S hS B hB
  -- The shared lemma states the right-hand side with `tailConditionalMeasure`; `hcore` asks for the
  -- bundled witness, and the two agree by `tailConditionalProbabilityMeasure_toMeasure`.
  simpa only [tailConditionalProbabilityMeasure_toMeasure] using
    measure_inter_blockCylinder_eq_setLIntegral_of_condExp hX_meas hB
      (hX.condExp_blockIndicatorProd_strictMono_tailProcess_ae_eq_prod_directingMeasure
        hX_meas hk hB) (measurable_tailProcess_tailConditionalProbabilityMeasure hS)

end Contractable

end Probability

end TauCeti

end
