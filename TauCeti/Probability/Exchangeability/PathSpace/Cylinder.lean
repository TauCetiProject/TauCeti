module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Block cylinders and their indicator products

For a process `X : ℕ → Ω → α` and a finite coordinate selection `k : Fin m → ℕ`:

* `blockCylinder X k C = {ω | ∀ i, X (k i) ω ∈ C i}` — the cylinder event on the selected
  coordinates (matching the `blockLaw` selection vocabulary; the first-`r` prefix is the case
  `k = fun i => i.val`);
* `blockIndicatorProd X k C ω = ∏ i, 𝟙_{C i}(X (k i) ω)` — its (`ℝ`-valued) indicator product.

These are the events and integrands the de Finetti block-product factorisation manipulates;
`blockIndicatorProd_eq_indicator` identifies the product with the cylinder indicator, and
`integrable_blockIndicatorProd` records that it is integrable under a finite measure.

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

/-- The block cylinder event on the selected coordinates: `{ω | ∀ i, X (k i) ω ∈ C i}`. -/
def blockCylinder (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) (C : Fin m → Set α) : Set Ω :=
  {ω | ∀ i, X (k i) ω ∈ C i}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem mem_blockCylinder {X : ℕ → Ω → α} {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} {ω : Ω} :
    ω ∈ blockCylinder X k C ↔ ∀ i, X (k i) ω ∈ C i :=
  Iff.rfl

/-- The block cylinder of a process with measurable selected coordinates on measurable sets is
measurable. -/
theorem measurableSet_blockCylinder {X : ℕ → Ω → α} {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α}
    (hX : ∀ i, Measurable (X (k i))) (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (blockCylinder X k C) := by
  simp only [blockCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (hX i) (hC i)

/-- The product of the selected coordinate indicators, `∏ i, 𝟙_{C i}(X (k i) ω)`. -/
def blockIndicatorProd (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) (C : Fin m → Set α) : Ω → ℝ :=
  fun ω => ∏ i, (C i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The indicator product is the indicator of the block cylinder. -/
theorem blockIndicatorProd_eq_indicator (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ)
    (C : Fin m → Set α) :
    blockIndicatorProd X k C = (blockCylinder X k C).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  simp only [blockIndicatorProd]
  by_cases h : ω ∈ blockCylinder X k C
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (mem_blockCylinder.mp h i) _
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi⟩ := not_forall.1 (mem_blockCylinder.not.mp h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The empty (zero-coordinate) indicator product is the constant-one function. -/
@[simp]
theorem blockIndicatorProd_empty (X : ℕ → Ω → α) (k : Fin 0 → ℕ) (C : Fin 0 → Set α) :
    blockIndicatorProd X k C = fun _ => 1 := by
  funext ω
  simp [blockIndicatorProd]

/-- The indicator product is integrable under a finite measure. -/
theorem integrable_blockIndicatorProd {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} {m : ℕ}
    {k : Fin m → ℕ} {C : Fin m → Set α} (hX : ∀ i, Measurable (X (k i)))
    (hC : ∀ i, MeasurableSet (C i)) : Integrable (blockIndicatorProd X k C) μ := by
  rw [blockIndicatorProd_eq_indicator]
  exact Integrable.indicator (integrable_const (1 : ℝ)) (measurableSet_blockCylinder hX hC)

end Probability

end TauCeti
