module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic

/-!
# Coordinatewise maps of conditionally i.i.d. sequences

This file completes the Layer 0 closure API for the exchangeability symmetry classes: applying a
measurable map `f : α → β` to every coordinate of a conditionally i.i.d. process gives another
conditionally i.i.d. process, whose directing measure is the coordinatewise pushforward
`ω ↦ (ν ω).map f` of the original directing measure `ν`.

`TauCeti.Probability.Exchangeability.Map` already records this closure for `ExchangeableAt`,
`Exchangeable`, `FullyExchangeable`, and `Contractable`.  `ConditionallyIID` is the remaining
symmetry class from the roadmap item asking for closure of each class under the coordinatewise
pushforward `X ↦ (f ∘ Xᵢ)` (`TauCetiRoadmap/Exchangeability/README.md`, Layer 0). The
directing-measure transformation is the honest one: conditionally on `ν ω`, the coordinates are
i.i.d. `ν ω`, so the mapped coordinates are i.i.d. `(ν ω).map f`.

The proof runs at the level of the finite-block mixture identity. It reuses `map_blockLaw`
(the coordinatewise pushforward of a block law) and the random-product measurability of
`TauCeti.MeasureTheory.Measure.ProductKernel`, together with the Giry-monad laws
`Measure.bind_bind` and `Measure.bind_dirac_eq_map` and Mathlib's product pushforward
`Measure.pi_map_pi`.  It needs no material from `cameronfreer/exchangeability` beyond the
existing `ConditionallyIIDWith` API this repository already carries.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- Pushing a `Measure.bind` mixture forward by a measurable map commutes with the bind: the
pushforward of the mixture is the mixture of the pushforwards. This is the Giry-monad identity
`map F ∘ bind g = bind (map F ∘ g)`, obtained from associativity of `bind` and
`bind_dirac_eq_map`. -/
private theorem map_bind_comm {S γ δ : Type*} [MeasurableSpace S] [MeasurableSpace γ]
    [MeasurableSpace δ] {μ : Measure S} {g : S → Measure γ} (hg : AEMeasurable g μ)
    {F : γ → δ} (hF : Measurable F) :
    (μ.bind g).map F = μ.bind fun ω => (g ω).map F := by
  have hdirac : AEMeasurable (fun x : γ => Measure.dirac (F x)) (μ.bind g) :=
    (Measure.measurable_dirac.comp hF).aemeasurable
  rw [← Measure.bind_dirac_eq_map (μ.bind g) hF, Measure.bind_bind hg hdirac]
  simp_rw [Measure.bind_dirac_eq_map _ hF]

/-- Conditional i.i.d.-ness with a named directing measure is preserved by a coordinatewise
measurable map of the value space: if `X` is conditionally i.i.d. with directing measure `ν`, then
`fun i ω => f (X i ω)` is conditionally i.i.d. with directing measure the coordinatewise
pushforward `fun ω => (ν ω).map f`. -/
theorem ConditionallyIIDWith.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    ConditionallyIIDWith μ (fun i ω => f (X i ω)) fun ω => (ν ω).map hf.aemeasurable := by
  refine ConditionallyIIDWith.intro ?_ ?_
  · -- The pushforward directing measure is measurable in the Giry structure.
    have hν : Measurable fun ω => (ν ω : Measure α) :=
      measurable_subtype_coe.comp h.measurable_directing
    exact ((Measure.measurable_map f hf).comp hν).subtype_mk
  · intro m k hk
    have hXk : ∀ i : Fin m, AEMeasurable (X (k i)) μ := fun i => hX (k i)
    have hFmeas : Measurable fun x : Fin m → α => fun i => f (x i) :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    have hg : AEMeasurable
        (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
      MeasureTheory.aemeasurable_probabilityMeasure_pi_toMeasure_of_measurable (fun _ : Fin m => ν)
        (fun _ => h.measurable_directing)
    calc
      blockLaw μ (fun i ω => f (X i ω)) k
          = (blockLaw μ X k).map fun x : Fin m → α => fun i => f (x i) :=
            (map_blockLaw μ k hf hXk).symm
      _ = (μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
            fun x : Fin m → α => fun i => f (x i) := by rw [h.map k hk]
      _ = μ.bind fun ω =>
            ((ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
              fun x : Fin m → α => fun i => f (x i) := map_bind_comm hg hFmeas
      _ = μ.bind fun ω =>
            (ProbabilityMeasure.pi fun _ : Fin m => (ν ω).map hf.aemeasurable).toMeasure := by
            refine congrArg (μ.bind ·) (funext fun ω => ?_)
            haveI : IsProbabilityMeasure ((ν ω : Measure α).map f) :=
              (ν ω : Measure α).isProbabilityMeasure_map hf.aemeasurable
            simp only [ProbabilityMeasure.toMeasure_pi, ProbabilityMeasure.toMeasure_map]
            exact Measure.pi_map_pi fun _ : Fin m => hf.aemeasurable

/-- Conditional i.i.d.-ness is preserved by a coordinatewise measurable map of the value space. -/
theorem ConditionallyIID.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    ConditionallyIID μ (fun i ω => f (X i ω)) := by
  obtain ⟨ν, hν⟩ := h.exists_directing
  exact ConditionallyIID.of_directing (hν.map_values hf hX)

/-- **Transfer of conditional i.i.d.-ness along the path law.** If the coordinate process on path
space is conditionally i.i.d. under `pathLaw μ X`, then `X` is conditionally i.i.d. under `μ`. -/
theorem conditionallyIID_of_conditionallyIID_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n))
    (h : ConditionallyIID (pathLaw μ X) fun n p => p n) :
    ConditionallyIID μ X := by
  obtain ⟨ν, hν⟩ := h.exists_directing
  have hφ : Measurable (fun ω => fun i => X i ω : Ω → ℕ → α) := measurable_pi_lambda _ hX_meas
  refine ConditionallyIID.of_directing
    (ConditionallyIIDWith.intro (hν.measurable_directing.comp hφ) ?_)
  intro m k hk
  have hcoord : Measurable (fun p : ℕ → α => fun i : Fin m => p (k i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (k i)
  have hg : Measurable
      (fun p : ℕ → α => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure) :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure ν
      hν.measurable_directing
  calc blockLaw μ X k
      = blockLaw (pathLaw μ X) (fun n p => p n) k := by
          simp only [blockLaw_def, pathLaw_def]
          rw [Measure.map_map hcoord hφ]
          rfl
    _ = (pathLaw μ X).bind fun p => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure :=
          hν.map k hk
    _ = μ.bind fun ω =>
          (ProbabilityMeasure.pi fun _ : Fin m => ν (fun i => X i ω)).toMeasure := by
          simp only [pathLaw_def, Measure.bind]
          rw [Measure.map_map hg hφ]
          rfl

end Probability

end TauCeti
