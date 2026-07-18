module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic

/-!
# The rectangle common ending for de Finetti

This file provides the first shared de Finetti common-ending adapter.  If a measurable random
probability measure `ν : Ω → ProbabilityMeasure α` has the expected rectangle factorization for
every finite injective block of a process, then the process is `ConditionallyIID`.

The work is done by the `ConditionallyIIDWith` rectangle characterization
(`conditionallyIIDWith_of_forall_rectangles`, next to its definition): rectangles generate the
finite product σ-algebra by Mathlib's `generateFrom_pi` / `isPiSystem_pi`, and Tau Ceti's
product-kernel API evaluates the mixture on rectangles.  This file packages that as the existential
wrapper.  This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 1, the common de Finetti
ending `conditionallyIID_of_directing_forall_rectangles`.

This is adapted from the rectangle common-ending strategy in
`cameronfreer/exchangeability` (`DeFinetti/CommonEnding.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`), but stated over Tau Ceti's current
`ConditionallyIIDWith` and `ProbabilityMeasure.pi` APIs.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Common de Finetti ending.** Rectangle-wise product-kernel factorization against a named
directing measure supplies a `ConditionallyIID` witness for the process. -/
theorem conditionallyIID_of_directing_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
        blockLaw μ X k (Set.univ.pi B) =
          ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing (conditionallyIIDWith_of_forall_rectangles hν h_rect)

end Probability

end TauCeti
