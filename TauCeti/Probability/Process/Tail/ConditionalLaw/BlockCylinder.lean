/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.ConditionalLaw.Basic
public import TauCeti.Probability.Process.Cylinder
import TauCeti.Probability.Process.Tail.ConditionalLaw.Integral

/-!
# Testing a conditional block factorization on tail events

If the conditional expectation of a block indicator given `tailProcess X` factors into the
tail-conditioned laws, then its integral on any tail-measurable event `A` is the mass of
`A ∩ blockCylinder X k B`:

```text
μ (A ∩ blockCylinder X k B) = ∫⁻ ω in A, ∏ i, tailConditionalMeasure μ X ω (B i) ∂μ.
```

The conditional factorization is supplied as a hypothesis. This identity converts it into a
measure identity, for example when `A` is an event defined by `tailConditionalProbabilityMeasure`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Given the conditional factorization of a block indicator along `k`, the mass of its cylinder
intersected with any tail-measurable event `A` is the integral of the product of tail-conditioned
law evaluations over `A`. The factorization is a hypothesis; no symmetry assumption on the process
or standard Borel assumption on the sample space is needed to integrate it. -/
theorem measure_inter_blockCylinder_eq_setLIntegral_of_condExp [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {k : Fin r → ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    (hfac : μ[blockIndicatorProd X k B | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i))
    {A : Set Ω} (hA_tail : MeasurableSet[tailProcess X] A) :
    μ (A ∩ blockCylinder X k B)
      = ∫⁻ ω in A, ∏ i, tailConditionalMeasure μ X ω (B i) ∂μ := by
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  have : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  have hA : MeasurableSet A := hTail _ hA_tail
  have hg_int : Integrable (fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i)) μ :=
    integrable_prod_tailConditionalMeasure_real hTail hB
  have hind_int : Integrable (blockIndicatorProd X k B) μ :=
    integrable_blockIndicatorProd (fun i => (hX_meas _).aemeasurable) hB
  -- The factorization, tested against the tail event `A`.
  have hchain : ∫ ω in A, blockIndicatorProd X k B ω ∂μ
      = ∫ ω in A, ∏ i, (tailConditionalMeasure μ X ω).real (B i) ∂μ := by
    rw [← setIntegral_condExp hTail hind_int hA_tail]
    exact setIntegral_congr_ae hA (hfac.mono fun ω hω _ => hω)
  -- The left side is the real mass of the intersection, via the block-indicator integral read
  -- against the restricted measure.
  have hleft : ∫ ω in A, blockIndicatorProd X k B ω ∂μ
      = μ.real (A ∩ blockCylinder X k B) := by
    rw [integral_blockIndicatorProd (μ := μ.restrict A) (fun i => (hX_meas _).aemeasurable) hB,
      blockLaw_blockCylinder X (fun i => (hX_meas _).aemeasurable) hB,
      Measure.restrict_apply (measurableSet_blockCylinder (fun i => hX_meas _) hB),
      Set.inter_comm, measureReal_def]
  have hne : μ (A ∩ blockCylinder X k B) ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, ← hleft, hchain,
    ofReal_integral_eq_lintegral_prod_tailConditionalMeasure hg_int.restrict]

end Probability

end TauCeti

end
