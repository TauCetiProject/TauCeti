module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Rectangle / indicator-product bridge for finite block laws

The de-Finetti-facing bridge between a process's finite-dimensional **block law**, measurable
**rectangles** `Set.univ.pi B`, and products of coordinate **indicators**:

* `blockLaw_apply_rectangle` — `blockLaw μ X k` on a rectangle is the measure of the coordinate-wise
  preimage `{ω | ∀ i, X (k i) ω ∈ B i}`.
* `indicator_product_eq_indicator_rectangle_preimage` — the product of the coordinate indicators is
  the indicator of that preimage.
* `lintegral_indicator_product_eq_blockLaw_rectangle` — the integral of the indicator product is the
  block law on the rectangle; the form the de Finetti common ending consumes.

Everything is concrete over `Fin m`; Mathlib's product/π-system infrastructure supplies the rest.
The indicator product is `ℝ≥0∞`-valued to line up with the product-kernel mixture
(`TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi`).

These bridge lemmas are motivated by the private `prod_indicators_eq_indicator_intersection` /
`measure_via_indicator_integral` helpers of `cameronfreer/exchangeability`
(`DeFinetti/CommonEnding.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {m : ℕ}

/-- The block law of `X` along `k`, evaluated on a measurable rectangle `Set.univ.pi B`, is the
measure of the coordinate-wise preimage `{ω | ∀ i, X (k i) ω ∈ B i}`. -/
theorem blockLaw_apply_rectangle (k : Fin m → ℕ) (hXk : ∀ i, AEMeasurable (X (k i)) μ)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = μ {ω | ∀ i, X (k i) ω ∈ B i} := by
  rw [blockLaw_apply, Measure.map_apply_of_aemeasurable
    (aemeasurable_pi_lambda _ hXk) (MeasurableSet.univ_pi hB)]
  congr 1
  ext ω
  simp [Set.mem_preimage]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The product of the coordinate indicators `∏ i, 𝟙_{B i}(X (k i) ω)` equals the indicator of the
rectangle preimage `{ω | ∀ i, X (k i) ω ∈ B i}`. -/
theorem indicator_product_eq_indicator_rectangle_preimage (k : Fin m → ℕ) (B : Fin m → Set α) :
    (fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ≥0∞)) (X (k i) ω))
      = {ω | ∀ i, X (k i) ω ∈ B i}.indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ω
  by_cases h : ω ∈ {ω | ∀ i, X (k i) ω ∈ B i}
  · rw [Set.indicator_of_mem h]
    have h' : ∀ i, X (k i) ω ∈ B i := h
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (h' i) _
  · rw [Set.indicator_of_notMem h]
    have h' : ¬ ∀ i, X (k i) ω ∈ B i := h
    obtain ⟨i, hi⟩ := not_forall.1 h'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- The integral of the coordinate indicator product is the block law on the rectangle — the
finite-block identity the de Finetti common ending consumes. -/
theorem lintegral_indicator_product_eq_blockLaw_rectangle (k : Fin m → ℕ)
    (hXk : ∀ i, AEMeasurable (X (k i)) μ) (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i, (B i).indicator (fun _ => (1 : ℝ≥0∞)) (X (k i) ω) ∂μ
      = blockLaw μ X k (Set.univ.pi B) := by
  have hS : NullMeasurableSet {ω | ∀ i, X (k i) ω ∈ B i} μ := by
    have hset : {ω | ∀ i, X (k i) ω ∈ B i}
        = ⋂ i ∈ (Finset.univ : Finset (Fin m)), (X (k i)) ⁻¹' (B i) := by
      ext ω; simp [Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact Finset.nullMeasurableSet_biInter Finset.univ
      fun i _ => (hXk i).nullMeasurableSet_preimage (hB i)
  rw [indicator_product_eq_indicator_rectangle_preimage k B,
    lintegral_indicator_const₀ hS, one_mul, blockLaw_apply_rectangle k hXk B hB]

end Probability

end TauCeti
