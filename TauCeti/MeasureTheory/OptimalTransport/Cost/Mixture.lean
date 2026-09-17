/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Transport costs of mixtures

For a fixed cost `c`, the transport cost is positively homogeneous and countably subadditive as a
function of the pair of marginals:

`transportCost c (a • μ) (a • ν) = a * transportCost c μ ν` and
`transportCost c (∑ i, μ i) (∑ i, ν i) ≤ ∑ i, transportCost c (μ i) (ν i)`.

Together they say that the transport cost of a mixture `(∑ i, a i • μ i, ∑ i, a i • ν i)` is at
most the corresponding mixture of the transport costs — the convexity of optimal transport in the
two marginals. The reason is that couplings can be mixed: the sum of couplings of the pairs
`(μ i, ν i)` couples the two sums (`TauCeti.IsCoupling.sum`), and the cost of a plan is additive
in the plan.

No finiteness or normalisation is assumed of the measures, and the cost need not be measurable.
Subadditivity cannot in general be improved to an equality: splitting `δ_x + δ_y` against itself
as `(δ_x, δ_y) + (δ_y, δ_x)` with the cost `edist` gives a strict inequality whenever `x ≠ y`.
Homogeneity is stated for a finite scaling factor.

## Main statements

* `TauCeti.transportCost_smul` — scaling both marginals by a finite factor scales the transport
  cost;
* `TauCeti.transportCost_sum_le` — countable subadditivity for `MeasureTheory.Measure.sum`;
* `TauCeti.transportCost_finset_sum_le` and `TauCeti.transportCost_add_le` — the finite and binary
  forms of subadditivity.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 4.8, the
  convexity of the optimal transport cost in the pair of marginals.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y] {a : ℝ≥0∞}

/-- **Homogeneity of the transport cost.** Scaling both marginals by the same finite factor scales
the transport cost by that factor. At `a = 0` both sides vanish, the zero plan coupling the two
zero measures. -/
theorem transportCost_smul (ha : a ≠ ∞) (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) :
    transportCost c (a • μ) (a • ν) = a * transportCost c μ ν := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simpa only [zero_smul, zero_mul, nonpos_iff_eq_zero, lintegral_zero_measure] using
      transportCost_le_lintegral isCoupling_zero c
  refine le_antisymm ?_ (le_transportCost fun π hπ ↦ ?_)
  · calc transportCost c (a • μ) (a • ν)
        ≤ ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), ∫⁻ z, c z ∂(a • π) :=
          le_iInf₂ fun π hπ ↦ transportCost_le_lintegral (hπ.smul a) c
      _ = a * transportCost c μ ν := by
          simp only [lintegral_smul_measure, smul_eq_mul, transportCost_def,
            ENNReal.mul_iInf_of_ne ha₀ ha]
  · have hπ' : IsCoupling (a⁻¹ • π) μ ν := by
      simpa only [smul_smul, ENNReal.inv_mul_cancel ha₀ ha, one_smul] using hπ.smul a⁻¹
    calc a * transportCost c μ ν ≤ a * ∫⁻ z, c z ∂(a⁻¹ • π) :=
          mul_le_mul_right (transportCost_le_lintegral hπ' c) a
      _ = ∫⁻ z, c z ∂π := by
          rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel ha₀ ha,
            one_mul]

/-- **Countable subadditivity of the transport cost.** The transport cost of the sums of two
countable families of marginals is at most the sum of the transport costs of the pairs: near
optimal plans of the pairs sum to a plan of the sums. -/
theorem transportCost_sum_le {ι : Type*} [Countable ι] (c : X × Y → ℝ≥0∞) (μ : ι → Measure X)
    (ν : ι → Measure Y) :
    transportCost c (Measure.sum μ) (Measure.sum ν) ≤ ∑' i, transportCost c (μ i) (ν i) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.coe_ne_zero.2 hε.ne') ι
  -- Each summand is finite, so it is strictly below itself plus its share `δ i` of the slack.
  have hlt' (i : ι) : transportCost c (μ i) (ν i) < transportCost c (μ i) (ν i) + δ i :=
    ENNReal.lt_add_right
      (ne_top_of_le_ne_top hlt.ne (ENNReal.le_tsum (f := fun i ↦ transportCost c (μ i) (ν i)) i))
      (hδ i).ne'
  choose π hπ hπc using fun i ↦ transportCost_lt_iff.1 (hlt' i)
  calc transportCost c (Measure.sum μ) (Measure.sum ν) ≤ ∫⁻ z, c z ∂Measure.sum π :=
        transportCost_le_lintegral (IsCoupling.sum hπ) c
    _ = ∑' i, ∫⁻ z, c z ∂π i := lintegral_sum_measure c π
    _ ≤ ∑' i, (transportCost c (μ i) (ν i) + δ i) := ENNReal.tsum_le_tsum fun i ↦ (hπc i).le
    _ = ∑' i, transportCost c (μ i) (ν i) + ∑' i, δ i := ENNReal.tsum_add
    _ ≤ ∑' i, transportCost c (μ i) (ν i) + ε := add_le_add_right hδε.le _

/-- **Finite subadditivity of the transport cost.** -/
theorem transportCost_finset_sum_le {ι : Type*} (s : Finset ι) (c : X × Y → ℝ≥0∞)
    (μ : ι → Measure X) (ν : ι → Measure Y) :
    transportCost c (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, transportCost c (μ i) (ν i) := by
  simpa only [Measure.sum_fintype, tsum_fintype, Finset.sum_coe_sort,
    Finset.sum_coe_sort s fun i ↦ transportCost c (μ i) (ν i)] using
    transportCost_sum_le c (fun i : s ↦ μ i) (fun i : s ↦ ν i)

/-- **Subadditivity of the transport cost** for two pairs of marginals. -/
theorem transportCost_add_le (c : X × Y → ℝ≥0∞) (μ μ' : Measure X) (ν ν' : Measure Y) :
    transportCost c (μ + μ') (ν + ν') ≤ transportCost c μ ν + transportCost c μ' ν' := by
  simpa only [Finset.sum_pair zero_ne_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using
    transportCost_finset_sum_le {0, 1} c ![μ, μ'] ![ν, ν']

end TauCeti
