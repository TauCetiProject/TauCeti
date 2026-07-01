module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Block cylinders and their indicator products

For a process `X : ℕ → Ω → α` and a finite coordinate selection `k : Fin m → ℕ`:

* `blockCylinder X k C = {ω | ∀ i, X (k i) ω ∈ C i}` — the cylinder event on the selected
  coordinates (matching the `blockLaw` selection vocabulary; the first-`r` prefix is the case
  `k = fun i => i.val`);
* `blockIndicatorProd X k C ω = ∏ i, 𝟙_{C i}(X (k i) ω)` — its (`ℝ`-valued) indicator product.

These are the finite-dimensional events and integrands the de Finetti block-product factorisation
manipulates. `blockCylinder_eq_preimage_univ_pi` and `blockLaw_blockCylinder` bridge the cylinder to
the existing rectangle/`blockLaw` interface; `blockIndicatorProd_eq_indicator` identifies the
product with the cylinder indicator; and `integrable_blockIndicatorProd` records integrability under
a finite measure.

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
/-- Membership in the block cylinder: `ω` lies in `blockCylinder X k C` iff every selected
coordinate `X (k i) ω` lies in its set `C i`. -/
@[simp]
theorem mem_blockCylinder {X : ℕ → Ω → α} {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} {ω : Ω} :
    ω ∈ blockCylinder X k C ↔ ∀ i, X (k i) ω ∈ C i :=
  Iff.rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The block cylinder is the preimage of the rectangle `Set.univ.pi C` under the
selected-coordinate map `ω ↦ (X (k ·) ω)`. -/
theorem blockCylinder_eq_preimage_univ_pi (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ)
    (C : Fin m → Set α) :
    blockCylinder X k C = (fun ω i => X (k i) ω) ⁻¹' Set.univ.pi C := by
  ext ω
  simp only [mem_blockCylinder, Set.mem_preimage, Set.mem_univ_pi]

/-- The block cylinder of a process with measurable selected coordinates on measurable sets is
measurable. -/
theorem measurableSet_blockCylinder {X : ℕ → Ω → α} {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α}
    (hX : ∀ i, Measurable (X (k i))) (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (blockCylinder X k C) := by
  simp only [blockCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (hX i) (hC i)

/-- The block law evaluated on a measurable rectangle is the measure of the block cylinder:
`blockLaw μ X k (Set.univ.pi C) = μ (blockCylinder X k C)`. A `blockCylinder`-named restatement of
the merged `blockLaw_apply_rectangle`. -/
@[grind =>]
theorem blockLaw_blockCylinder {μ : Measure Ω} (X : ℕ → Ω → α) {m : ℕ} {k : Fin m → ℕ}
    {C : Fin m → Set α} (hX : ∀ i, AEMeasurable (X (k i)) μ) (hC : ∀ i, MeasurableSet (C i)) :
    blockLaw μ X k (Set.univ.pi C) = μ (blockCylinder X k C) := by
  rw [blockLaw_apply_rectangle μ X k hX C hC, blockCylinder]

/-- The product of the selected coordinate indicators, `∏ i, 𝟙_{C i}(X (k i) ω)`. -/
def blockIndicatorProd (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) (C : Fin m → Set α) : Ω → ℝ :=
  fun ω => ∏ i, (C i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Pointwise value of the indicator product: the product of the selected coordinate indicators. -/
@[simp]
theorem blockIndicatorProd_apply (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) (C : Fin m → Set α)
    (ω : Ω) :
    blockIndicatorProd X k C ω = ∏ i, (C i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) := by
  simp only [blockIndicatorProd]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The indicator product is the indicator of the block cylinder. -/
theorem blockIndicatorProd_eq_indicator (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ)
    (C : Fin m → Set α) :
    blockIndicatorProd X k C = (blockCylinder X k C).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  rw [blockIndicatorProd_apply]
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

/-- The block cylinder is null-measurable when the selected coordinates are a.e. measurable. -/
theorem nullMeasurableSet_blockCylinder {μ : Measure Ω} {X : ℕ → Ω → α} {m : ℕ} {k : Fin m → ℕ}
    {C : Fin m → Set α} (hX : ∀ i, AEMeasurable (X (k i)) μ) (hC : ∀ i, MeasurableSet (C i)) :
    NullMeasurableSet (blockCylinder X k C) μ := by
  rw [blockCylinder, Set.setOf_forall]
  exact NullMeasurableSet.iInter fun i => (hX i).nullMeasurableSet_preimage (hC i)

/-- The indicator product is integrable under a finite measure (a.e.-measurable coordinates). -/
theorem integrable_blockIndicatorProd {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} {m : ℕ}
    {k : Fin m → ℕ} {C : Fin m → Set α} (hX : ∀ i, AEMeasurable (X (k i)) μ)
    (hC : ∀ i, MeasurableSet (C i)) : Integrable (blockIndicatorProd X k C) μ := by
  rw [blockIndicatorProd_eq_indicator]
  exact (integrable_const (1 : ℝ)).indicator₀ (nullMeasurableSet_blockCylinder hX hC)

end Probability

end TauCeti
