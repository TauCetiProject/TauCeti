module

public import TauCeti.Probability.DeFinetti.BlockFactorization
-- Non-public: used only inside proofs — the Layer-0 bridges from conditional i.i.d. back to
-- exchangeability and contractability.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Implications

/-!
# The de Finetti–Ryll-Nardzewski equivalences

The equivalence forms of the de Finetti summit: for a process with measurable coordinates, valued
in a nonempty standard Borel space, under a finite measure,

* exchangeable **iff** conditionally i.i.d. (`exchangeable_iff_conditionallyIID`),
* contractable **iff** conditionally i.i.d. (`contractable_iff_conditionallyIID`, the two-way
  form), and
* contractable **iff** exchangeable and conditionally i.i.d.
  (`contractable_iff_exchangeable_and_conditionallyIID`, the roadmap's conjunction form, derived
  from the two-way form)

— Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1 (pp. 26–28). The
hard direction is the merged reverse-martingale de Finetti chain
(`conditionallyIID_of_contractable`); the converse directions are the Layer-0 bridges
(`ConditionallyIID.exchangeable`, `ConditionallyIID.contractable`). This file assembles the
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
* `contractable_iff_conditionallyIID` — the two-way Ryll-Nardzewski equivalence.
* `contractable_iff_exchangeable_and_conditionallyIID` — the roadmap's conjunction form.
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

/-- **De Finetti–Ryll-Nardzewski, two-way form.** A process with measurable coordinates, valued
in a nonempty standard Borel space, under a finite measure, is contractable iff it is conditionally
i.i.d. Forward: the reverse-martingale de Finetti chain (`conditionallyIID_of_contractable`);
converse: `ConditionallyIID.contractable`, which needs no side hypotheses. -/
theorem contractable_iff_conditionallyIID [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ ConditionallyIID μ X :=
  ⟨fun hX => conditionallyIID_of_contractable hX hX_meas, fun hX => hX.contractable⟩

/-- **The de Finetti–Ryll-Nardzewski equivalence** (Kallenberg, Theorem 1.1), in the roadmap's
conjunction form: contractable iff exchangeable and conditionally i.i.d. Derived from the two-way
`contractable_iff_conditionallyIID`, with the exchangeability conjunct supplied by
`ConditionallyIID.exchangeable` (the conjunct is redundant given conditional i.i.d., but this is
the equivalence the roadmap names). -/
theorem contractable_iff_exchangeable_and_conditionallyIID [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X :=
  (contractable_iff_conditionallyIID hX_meas).trans
    ⟨fun hX => ⟨hX.exchangeable, hX⟩, And.right⟩

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
