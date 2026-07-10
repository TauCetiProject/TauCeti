module

public import TauCeti.Probability.DeFinetti.BlockFactorization
-- Non-public: used only inside proofs — the Layer-0 bridge from conditional i.i.d. back to
-- exchangeability.
import TauCeti.Probability.Exchangeability.ConditionallyIIDImplications

/-!
# The de Finetti–Ryll-Nardzewski equivalences

The equivalence forms of the de Finetti summit: for a process with measurable coordinates, valued
in a nonempty standard Borel space, under a finite measure,

* exchangeable **iff** conditionally i.i.d. (`exchangeable_iff_conditionallyIID`), and
* contractable **iff** exchangeable and conditionally i.i.d.
  (`contractable_iff_exchangeable_and_conditionallyIID`)

— Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1 (pp. 26–28). The
hard direction is the merged reverse-martingale de Finetti chain
(`conditionallyIID_of_contractable`); the converse directions are the Layer-0 bridges
(`ConditionallyIID.exchangeable`, `contractable_of_exchangeable`). This file assembles the
equivalences and provides the roadmap target handles (`TauCetiRoadmap`, Exchangeability
Layers 6–7): `deFinetti`, `deFinetti_equivalence`, and `deFinetti_RyllNardzewski_equivalence`.

Both equivalences hold on an arbitrary measurable sample space `Ω` under `[IsFiniteMeasure μ]`;
the standard-Borel hypothesis sits only on the state space `α`, where the directing measure lives.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/TheoremViaMartingale.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`); the statements here are the source's final wrappers,
generalized from `[StandardBorelSpace Ω]` + probability measures to arbitrary measurable `Ω` +
finite measures.

## Main results

* `exchangeable_iff_conditionallyIID` — de Finetti's theorem as an equivalence.
* `contractable_iff_exchangeable_and_conditionallyIID` — the Ryll-Nardzewski equivalence.
* `deFinetti`, `deFinetti_equivalence`, `deFinetti_RyllNardzewski_equivalence` — roadmap target
  handles (aliases).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- **De Finetti's theorem, equivalence form** (Kallenberg, Theorem 1.1). A process with
measurable coordinates, valued in a nonempty standard Borel space, under a finite measure, is
exchangeable iff it is conditionally i.i.d. The forward direction is the reverse-martingale
de Finetti chain (`conditionallyIID_of_exchangeable`); the converse is the mixture computation
`ConditionallyIID.exchangeable`, which needs no side hypotheses. -/
theorem exchangeable_iff_conditionallyIID [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Exchangeable μ X ↔ ConditionallyIID μ X :=
  ⟨fun hX => conditionallyIID_of_exchangeable hX hX_meas, fun hX => hX.exchangeable⟩

/-- **The de Finetti–Ryll-Nardzewski equivalence** (Kallenberg, Theorem 1.1). A process with
measurable coordinates, valued in a nonempty standard Borel space, under a finite measure, is
contractable iff it is exchangeable and conditionally i.i.d. Forward: the reverse-martingale
de Finetti chain (`conditionallyIID_of_contractable`), with exchangeability read off the mixture
representation; converse: `contractable_of_exchangeable`. -/
theorem contractable_iff_exchangeable_and_conditionallyIID [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  refine ⟨fun hX => ?_, fun hX =>
    contractable_of_exchangeable hX.1 fun i => (hX_meas i).aemeasurable⟩
  have hiid : ConditionallyIID μ X := conditionallyIID_of_contractable hX hX_meas
  exact ⟨hiid.exchangeable, hiid⟩

/-- Roadmap Layer 6 target name (`TauCetiRoadmap/Exchangeability`) for de Finetti's theorem,
`conditionallyIID_of_exchangeable`. -/
alias deFinetti := conditionallyIID_of_exchangeable

/-- Roadmap Layer 7 target name (`TauCetiRoadmap/Exchangeability`) for the de Finetti equivalence
`exchangeable_iff_conditionallyIID`. -/
alias deFinetti_equivalence := exchangeable_iff_conditionallyIID

/-- Roadmap Layer 6 target name (`TauCetiRoadmap/Exchangeability`) for the Ryll-Nardzewski
equivalence `contractable_iff_exchangeable_and_conditionallyIID`. -/
alias deFinetti_RyllNardzewski_equivalence := contractable_iff_exchangeable_and_conditionallyIID

end Probability

end TauCeti
