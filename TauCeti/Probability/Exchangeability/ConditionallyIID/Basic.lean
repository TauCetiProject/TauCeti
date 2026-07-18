module

public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Conditionally i.i.d. sequences

The directing-measure API for de Finetti's theorem. A process is *conditionally i.i.d.* when
there is a measurable random probability measure `ν : Ω → ProbabilityMeasure α` such that
every finite block of **distinct** coordinates has, as its law, the `ν`-mixture of the
corresponding product measure. `ConditionallyIIDWith μ X ν` names the directing measure;
`ConditionallyIID` is the existential wrapper.

This file adds the Layer 0 directing-measure definitions and destructors, together with the
Layer 1 rectangle-factorization characterization used by the common de Finetti ending. The
exchangeability implications from conditionally i.i.d. processes live in
`ConditionallyIIDImplications.lean`.

These declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Suggested.lean`, Layer 0, refining the existential
`ConditionallyIID` of the roadmap into a named-directing-measure relation
(`ConditionallyIIDWith`) plus its existential wrapper. They are adapted from the
`cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Implementation helper for the rectangle characterization: two measures on a finite product
space are equal if they agree on all measurable rectangles `Set.univ.pi B`. Only the first measure
is assumed finite. -/
private theorem measure_eq_of_forall_univ_pi {ι : Type*} [Finite ι] {α : ι → Type*}
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

/-- Conditional i.i.d.-ness with a specified directing probability measure `ν`: the random
measure `ν` is measurable, and along every finite selection `k` of **distinct** coordinates
the block law is the `ν`-mixture of the product measure
`ProbabilityMeasure.pi (fun _ => ν ω)`. Distinctness (`Function.Injective k`) is what product
laws need, in contrast with the order condition `StrictMono` of `Contractable`. -/
def ConditionallyIIDWith (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Constructor: a measurable directing measure together with the finite-block mixture identity. -/
theorem ConditionallyIIDWith.intro {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (hν : Measurable ν)
    (h : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) :
    ConditionallyIIDWith μ X ν :=
  ⟨hν, h⟩

/-- Simp normal form for `ConditionallyIIDWith`. -/
@[simp]
theorem conditionallyIIDWith_iff {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  Iff.rfl

/-- Conditional i.i.d.-ness: existence of a directing probability measure. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν

/-- Constructor from a directing measure together with its witness. -/
theorem ConditionallyIID.of_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : ConditionallyIID μ X :=
  ⟨ν, h⟩

/-- Simp normal form for the existential wrapper `ConditionallyIID`. -/
@[simp]
theorem conditionallyIID_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    ConditionallyIID μ X ↔ ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  Iff.rfl

/-- The directing measure of a `ConditionallyIIDWith` witness is measurable. -/
@[grind →]
theorem ConditionallyIIDWith.measurable_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Measurable ν :=
  h.1

/-- The defining finite-block mixture identity of a `ConditionallyIIDWith` witness. -/
@[grind =>]
theorem ConditionallyIIDWith.map {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k) :
    blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  h.2 m k hk

/-- A `ConditionallyIID` process has a directing probability measure. -/
theorem ConditionallyIID.exists_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  h

/-- A process is `ConditionallyIIDWith μ X ν` once every injective finite block has the same
rectangle values as the corresponding random product-measure mixture. -/
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
    rw [blockLaw_def]
    infer_instance
  refine measure_eq_of_forall_univ_pi ?_
  intro B hB
  rw [h_rect m k hk B hB]
  rw [TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi ν hν.aemeasurable B hB]

/-- A `ConditionallyIIDWith` witness gives the expected rectangle factorization for every injective
finite block. -/
@[grind =>]
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

/-- Rectangle factorization is equivalent to the existential `ConditionallyIID` relation. -/
theorem conditionallyIID_iff_exists_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} :
    ConditionallyIID μ X ↔
      ∃ ν : Ω → ProbabilityMeasure α, Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
            blockLaw μ X k (Set.univ.pi B) =
              ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  simp_rw [conditionallyIID_iff, conditionallyIIDWith_iff_forall_rectangles]

end Probability

end TauCeti
