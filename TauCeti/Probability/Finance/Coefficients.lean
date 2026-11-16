/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.TimeAverage

/-!
# Predictable representatives of nondegenerate market coefficients

A progressively measurable drift and volatility, with volatility bounded away from zero
and bounded market price of risk, admit predictable representatives with the same bounds
everywhere. The market price of risk of the selected coefficients is itself predictable.
The representatives agree with the original coefficients for Lebesgue-time × sample-measure
almost every point of the declared finite horizon.

Selecting the two representatives separately does not give pointwise nondegeneracy: the
exceptional time-product null set can still contain zeros of the selected volatility. Here
we repair the volatility on its predictable exceptional set, bound the market price of risk,
and reconstruct the drift as rate plus volatility times market price of risk. This makes
pointwise division legitimate in replication holdings, while preserving the coefficient
identity almost everywhere. No completion, right continuity, Brownian motion, or moment
hypothesis is required. Equality is time-product almost everywhere, not a fixed-time
modification or indistinguishability statement. Bounds outside the declared horizon concern
only the selected representatives, not the original coefficients.

The representative construction uses
`MeasureTheory.IsStronglyProgressive.exists_isStronglyPredictable_ae_prod`.
No stochastic integral or change of measure is constructed here.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2, for the drift/volatility/market-price-of-risk identity.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.IsStronglyProgressive

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [SFinite P] {μ σ : ℝ≥0 → Ω → ℝ} {r : ℝ≥0 → ℝ}
  {δ C K : ℝ} {T : ℝ≥0}

/-- Progressive market coefficients with uniformly nonzero bounded volatility and bounded
market price of risk have predictable representatives satisfying these bounds everywhere.
The selected market price of risk is the actual quotient `(μ' - r) / σ'`, not independent
auxiliary data. Both coefficients, and hence that quotient, agree with their originals
for time-product almost every point on `(0,T]`. The rate need only be Borel measurable. -/
theorem exists_isStronglyPredictable_marketCoefficients
    (hμ : IsStronglyProgressive ℱ μ) (hσ : IsStronglyProgressive ℱ σ)
    (hr : Measurable r) (hδ : 0 < δ) (hδC : δ ≤ C) (hK : 0 ≤ K)
    (hcoeff : ∀ᵐ p : ℝ × Ω ∂(volume.restrict (Ioc 0 (T : ℝ))).prod P,
      δ ≤ |σ p.1.toNNReal p.2| ∧ |σ p.1.toNNReal p.2| ≤ C ∧
        |(μ p.1.toNNReal p.2 - r p.1.toNNReal) / σ p.1.toNNReal p.2| ≤ K) :
    ∃ μ' σ' : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable ℱ μ' ∧ IsStronglyPredictable ℱ σ' ∧
      IsStronglyPredictable ℱ (fun t ω ↦ (μ' t ω - r t) / σ' t ω) ∧
      (∀ t ω, δ ≤ |σ' t ω| ∧ |σ' t ω| ≤ C ∧
        |(μ' t ω - r t) / σ' t ω| ≤ K) ∧
      (∀ᵐ p : ℝ × Ω ∂(volume.restrict (Ioc 0 (T : ℝ))).prod P,
        μ' p.1.toNNReal p.2 = μ p.1.toNNReal p.2 ∧
          σ' p.1.toNNReal p.2 = σ p.1.toNNReal p.2) := by
  obtain ⟨U, hU, hUeq⟩ := hμ.exists_isStronglyPredictable_ae_prod P
  obtain ⟨V, hV, hVeq⟩ := hσ.exists_isStronglyPredictable_ae_prod P
  -- Repair only predictable sets, so no augmentation of the filtration is needed.
  let S (t : ℝ≥0) (ω : Ω) := if δ ≤ |V t ω| ∧ |V t ω| ≤ C then V t ω else δ
  have hS : IsStronglyPredictable ℱ S := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    have hnorm := continuous_abs.measurable.comp hV.measurable
    exact (hV.measurable.ite
      ((measurableSet_le measurable_const hnorm).inter
        (measurableSet_le hnorm measurable_const)) measurable_const).stronglyMeasurable
  have hSb (t : ℝ≥0) (ω : Ω) : δ ≤ |S t ω| ∧ |S t ω| ≤ C := by
    dsimp only [S]
    split_ifs with h
    · exact h
    · simpa only [abs_of_pos hδ] using And.intro le_rfl hδC
  have hS0 (t : ℝ≥0) (ω : Ω) : S t ω ≠ 0 := by
    exact abs_pos.mp (hδ.trans_le (hSb t ω).1)
  -- Bound the risk premium, then reconstruct rather than independently repair the drift.
  let L (t : ℝ≥0) (ω : Ω) := (U t ω - r t) / S t ω
  have hL : IsStronglyPredictable ℱ L := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact ((hU.measurable.sub (hr.comp ℱ.measurable_fst_predictable)).div
      hS.measurable).stronglyMeasurable
  let k (t : ℝ≥0) (ω : Ω) := if |L t ω| ≤ K then L t ω else 0
  have hk : IsStronglyPredictable ℱ k := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact (hL.measurable.ite
      (measurableSet_le (continuous_abs.measurable.comp hL.measurable) measurable_const)
      measurable_const).stronglyMeasurable
  have hkb (t : ℝ≥0) (ω : Ω) : |k t ω| ≤ K := by
    dsimp only [k]
    split_ifs with h
    · exact h
    · simpa using hK
  let M (t : ℝ≥0) (ω : Ω) := r t + S t ω * k t ω
  have hM : IsStronglyPredictable ℱ M := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact ((hr.comp ℱ.measurable_fst_predictable).add
      (hS.measurable.mul hk.measurable)).stronglyMeasurable
  have hquot : (fun t ω ↦ (M t ω - r t) / S t ω) = k := by
    funext t ω
    dsimp only [M]
    simp [hS0 t ω]
  refine ⟨M, S, hM, hS, ?_, ?_, ?_⟩
  · rwa [hquot]
  · intro t ω
    rw [congrFun (congrFun hquot t) ω]
    exact ⟨(hSb t ω).1, (hSb t ω).2, hkb t ω⟩
  -- On the original full-measure set neither repair changes a coefficient.
  · filter_upwards [hUeq T, hVeq T, hcoeff] with p hUp hVp hp
    have hSp : S p.1.toNNReal p.2 = σ p.1.toNNReal p.2 := by
      simp only [S, hVp, hp.1, hp.2.1, and_self, ite_true]
    have hLp : L p.1.toNNReal p.2 =
        (μ p.1.toNNReal p.2 - r p.1.toNNReal) / σ p.1.toNNReal p.2 := by
      simp only [L, hUp, hSp]
    refine ⟨?_, hSp⟩
    dsimp only [M, k]
    rw [hLp, ite_eq_left hp.2.2, hSp]
    have hσp : σ p.1.toNNReal p.2 ≠ 0 := hSp ▸ hS0 p.1.toNNReal p.2
    field_simp
    ring

end MeasureTheory.IsStronglyProgressive
