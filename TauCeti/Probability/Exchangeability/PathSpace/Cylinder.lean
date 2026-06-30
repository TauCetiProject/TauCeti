module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# First-`r` cylinders and their indicator products

For a process `X : ℕ → Ω → α`:

* `firstRCylinder X r C = {ω | ∀ i : Fin r, X i ω ∈ C i}` — the cylinder event on the first `r`
  coordinates;
* `indProd X r C ω = ∏ i, 𝟙_{C i}(X i ω)` — its (`ℝ`-valued) indicator product.

These are the events and integrands the de Finetti block-product factorisation manipulates;
`indProd_eq_indicator` identifies the product with the cylinder indicator, and `integrable_indProd`
records that it is integrable under a finite measure.

Adapted from `cameronfreer/exchangeability` (`PathSpace/CylinderHelpers.lean`,
`DeFinetti/ViaMartingale/IndicatorAlgebra.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The cylinder event on the first `r` coordinates: `{ω | ∀ i : Fin r, X i ω ∈ C i}`. -/
@[expose]
def firstRCylinder (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Set Ω :=
  {ω | ∀ i : Fin r, X i ω ∈ C i}

/-- The first-`r` cylinder of a process with measurable coordinates on measurable sets is
measurable. -/
theorem measurableSet_firstRCylinder {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) {r : ℕ}
    {C : Fin r → Set α} (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (firstRCylinder X r C) := by
  rw [firstRCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (hX i) (hC i)

/-- The product of the first-`r` coordinate indicators, `∏ i, 𝟙_{C i}(X i ω)`. -/
@[expose]
def indProd (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Ω → ℝ :=
  fun ω => ∏ i : Fin r, (C i).indicator (fun _ => (1 : ℝ)) (X i ω)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The indicator product is the indicator of the first-`r` cylinder. -/
theorem indProd_eq_indicator (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C = (firstRCylinder X r C).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases h : ω ∈ firstRCylinder X r C
  · rw [Set.indicator_of_mem h]
    have h' : ∀ i : Fin r, X i ω ∈ C i := h
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (h' i) _
  · rw [Set.indicator_of_notMem h]
    have h' : ¬ ∀ i : Fin r, X i ω ∈ C i := h
    obtain ⟨i, hi⟩ := not_forall.1 h'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem indProd_zero (X : ℕ → Ω → α) (C : Fin 0 → Set α) : indProd X 0 C = fun _ => 1 := by
  funext ω
  simp [indProd]

/-- The indicator product is integrable under a finite measure. -/
theorem integrable_indProd {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) {r : ℕ} {C : Fin r → Set α} (hC : ∀ i, MeasurableSet (C i)) :
    Integrable (indProd X r C) μ := by
  rw [indProd_eq_indicator]
  exact Integrable.indicator (integrable_const (1 : ℝ)) (measurableSet_firstRCylinder hX hC)

end Probability

end TauCeti
