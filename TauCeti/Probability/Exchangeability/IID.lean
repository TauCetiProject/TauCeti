module

public import TauCeti.Probability.Exchangeability.ConditionallyIIDImplications
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# An i.i.d. sequence is conditionally i.i.d., exchangeable, and contractable

This file discharges the first worked example of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Worked examples"):

> The law of an i.i.d. sequence is `ConditionallyIID`, `Exchangeable`, and `Contractable`.

For a sequence `X : ℕ → Ω → α` on a probability space whose coordinates are independent
(`ProbabilityTheory.iIndepFun X μ`) and identically distributed
(`∀ i, IdentDistrib (X i) (X 0) μ μ`), the constant random measure `ω ↦ law of X 0` is a
directing measure: `ConditionallyIIDWith.of_iIndepFun_identDistrib`. Exchangeability and
contractability then follow from the Layer 0 implications
`ConditionallyIIDWith.exchangeable` and `ConditionallyIIDWith.contractable`.

The mathematical content is the block-law identity: along an injective selection
`k : Fin m → ℕ` the coordinates `X ∘ k` are independent (a subfamily of an independent
family, `ProbabilityTheory.iIndepFun.precomp`) with common law `μ.map (X 0)`, so their joint
law is the `m`-fold product `Measure.pi (fun _ => μ.map (X 0))`
(`ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`); this is exactly the value of the mixture
against a constant directing measure. The example validates the Layer 0 directing-measure
API on the canonical i.i.d. case and needs no material from
`cameronfreer/exchangeability`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **An i.i.d. sequence is conditionally i.i.d.**, with the constant directing measure
`ω ↦ μ.map (X 0)` (the common law of the coordinates). For independent, identically
distributed measurable coordinates, the law of an injective finite block is the product of
that common law, which is precisely the mixture against the constant directing measure. -/
theorem ConditionallyIIDWith.of_iIndepFun_identDistrib {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConditionallyIIDWith μ X
      (fun _ => ⟨μ.map (X 0), Measure.isProbabilityMeasure_map (hmeas 0).aemeasurable⟩) := by
  refine ConditionallyIIDWith.intro measurable_const ?_
  intro m k hk
  -- The block law along an injective selection is the `m`-fold product of the common law.
  have hindep_k : iIndepFun (fun i : Fin m => X (k i)) μ := hindep.precomp hk
  have hblock : blockLaw μ X k = Measure.pi (fun _ : Fin m => μ.map (X 0)) := by
    have h1 : blockLaw μ X k = Measure.pi (fun i : Fin m => μ.map (X (k i))) := by
      rw [blockLaw_apply]
      exact hindep_k.map_fun_eq_pi_map (fun i => (hmeas (k i)).aemeasurable)
    rw [h1]
    exact congrArg Measure.pi (funext fun i => (hident (k i)).map_eq)
  -- Binding a probability measure against a constant measure returns that measure.
  rw [hblock, Measure.bind_const, measure_univ, one_smul, ProbabilityMeasure.toMeasure_pi]
  rfl

/-- **An i.i.d. sequence is conditionally i.i.d.** (existential directing-measure form). -/
theorem ConditionallyIID.of_iIndepFun_identDistrib {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing
    (ConditionallyIIDWith.of_iIndepFun_identDistrib hindep hmeas hident)

/-- **An i.i.d. sequence is exchangeable.** -/
theorem Exchangeable.of_iIndepFun_identDistrib {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Exchangeable μ X :=
  (ConditionallyIIDWith.of_iIndepFun_identDistrib hindep hmeas hident).exchangeable

/-- **An i.i.d. sequence is contractable.** -/
theorem Contractable.of_iIndepFun_identDistrib {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Contractable μ X :=
  (ConditionallyIIDWith.of_iIndepFun_identDistrib hindep hmeas hident).contractable

end Probability

end TauCeti
