module

public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.Exchangeability.ConditionallyIID

/-!
# The rectangle common ending for de Finetti

This file provides the first shared de Finetti common-ending adapter.  If a measurable random
probability measure `ν : Ω → ProbabilityMeasure α` has the expected rectangle factorization for
every finite injective block of a process, then `ν` is a `ConditionallyIIDWith` directing measure.

The proof is intentionally only a bridge: rectangles generate the finite product σ-algebra by
Mathlib's `generateFrom_pi` / `isPiSystem_pi`, and Tau Ceti's product-kernel API evaluates the
mixture on rectangles.  This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 1, the
common de Finetti ending `conditional_iid_from_directing_measure`.

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

/-- Two finite product measures are equal if they agree on all measurable rectangles
`Set.univ.pi B`. -/
theorem measure_eq_of_forall_univ_pi {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]
    (h : ∀ B : ∀ i, Set (α i), (∀ i, MeasurableSet (B i)) →
      μ (Set.univ.pi B) = ν (Set.univ.pi B)) :
    μ = ν := by
  letI := Fintype.ofFinite ι
  refine Measure.ext_of_generateFrom_of_iUnion
    (C := Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (α i) | MeasurableSet s})
    (B := fun _ : ℕ => Set.univ) generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_
  · simpa using (iUnion_const (Set.univ : Set (∀ i, α i)))
  · intro n
    exact ⟨fun _ => Set.univ, fun i _ => MeasurableSet.univ, by simp⟩
  · intro n
    exact measure_ne_top μ Set.univ
  · rintro _ ⟨B, hB, rfl⟩
    exact h B fun i => hB i (mem_univ i)

/-- A named directing measure is conditionally i.i.d. once every injective finite block has the
same rectangle values as the corresponding random product-measure mixture. -/
theorem conditionallyIIDWith_of_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
        blockLaw μ X k (Set.univ.pi B) =
          ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ) :
    ConditionallyIIDWith μ X ν := by
  refine ConditionallyIIDWith.intro hν ?_
  intro m k hk
  haveI : IsFiniteMeasure (blockLaw μ X k) := by
    rw [blockLaw_apply]
    infer_instance
  refine measure_eq_of_forall_univ_pi ?_
  intro B hB
  rw [h_rect m k hk B hB]
  rw [TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi ν hν.aemeasurable B hB]

/-- A named conditionally i.i.d. directing measure gives the expected rectangle factorization
for every injective finite block. -/
theorem ConditionallyIIDWith.blockLaw_univ_pi {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) =
      ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  rw [h.map k hk]
  have hν_ae : AEMeasurable ν μ := h.measurable_directing.aemeasurable
  rw [TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi ν hν_ae B hB]

/-- Rectangle factorization is equivalent to the named `ConditionallyIIDWith` relation. -/
theorem conditionallyIIDWith_iff_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
            blockLaw μ X k (Set.univ.pi B) =
              ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  constructor
  · intro h
    exact ⟨h.measurable_directing, fun m k hk B hB => h.blockLaw_univ_pi k hk B hB⟩
  · rintro ⟨hν, h_rect⟩
    exact conditionallyIIDWith_of_forall_rectangles hν h_rect

/-- **Common de Finetti ending.** Rectangle-wise product-kernel factorization supplies a
conditionally i.i.d. directing measure. -/
theorem conditional_iid_from_directing_measure {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
        blockLaw μ X k (Set.univ.pi B) =
          ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing (conditionallyIIDWith_of_forall_rectangles hν h_rect)

end Probability

end TauCeti
