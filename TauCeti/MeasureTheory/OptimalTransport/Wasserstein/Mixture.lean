/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# The Wasserstein distance of mixtures

For a finite nonzero exponent `p`, the `p`-th power of the `p`-Wasserstein distance is jointly
convex in the two laws: for weights `a i`,

`W_p (∑ i, a i • μ i, ∑ i, a i • ν i) ^ p ≤ ∑ i, a i * W_p (μ i, ν i) ^ p`.

For a probability vector `a` this is the mixture bound for `W_p`. It is the transport-cost
convexity of `TauCeti.transportCost_smul` and `TauCeti.transportCost_sum_le` read through the
bridge `TauCeti.wassersteinEDist_rpow_eq_transportCost` for the cost `edist ^ p`.

The weights are only required to be finite and need not sum to `1`; the laws are arbitrary
measures, and neither measurability of the ground distance nor `1 ≤ p` is used. The exponent is
finite: at `p = ∞` the power `p.toReal` is `0`, and the corresponding estimate instead bounds
the distance of the mixtures by the largest distance of a pair with positive weight, which is a
different statement not proved here.

## Main statements

* `TauCeti.wassersteinEDist_finset_sum_smul_rpow_le` — the mixture bound for finitely many laws;
* `TauCeti.wassersteinEDist_sum_smul_rpow_le` — the mixture bound for countably many laws, written
  with `MeasureTheory.Measure.sum`;
* `TauCeti.wassersteinEDist_add_rpow_le` — subadditivity of `W_p ^ p` for two pairs of measures.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 4.8, the
  convexity of the optimal transport cost, applied here to the cost `edist ^ p`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] [EDist X] {p : ℝ≥0∞}

/-- **The mixture bound for the Wasserstein distance.** For a finite nonzero exponent, the `p`-th
power of the Wasserstein distance of two finite mixtures with common finite weights is at most the
weighted sum of the `p`-th powers of the distances of the components. -/
theorem wassersteinEDist_finset_sum_smul_rpow_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp0 : p ≠ 0) (hp : p ≠ ∞) {ι : Type*}
    (s : Finset ι) {a : ι → ℝ≥0∞} (ha : ∀ i ∈ s, a i ≠ ∞) (μ ν : ι → Measure X) :
    wassersteinEDist p (∑ i ∈ s, a i • μ i) (∑ i ∈ s, a i • ν i) ^ p.toReal
      ≤ ∑ i ∈ s, a i * wassersteinEDist p (μ i) (ν i) ^ p.toReal := by
  simp only [wassersteinEDist_rpow_eq_transportCost hd hp0 hp]
  exact (transportCost_finset_sum_le s _ _ _).trans_eq
    (Finset.sum_congr rfl fun i hi ↦ transportCost_smul (ha i hi) _ _ _)

/-- **The mixture bound for the Wasserstein distance**, for countable mixtures. -/
theorem wassersteinEDist_sum_smul_rpow_le (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    {a : ι → ℝ≥0∞} (ha : ∀ i, a i ≠ ∞) (μ ν : ι → Measure X) :
    wassersteinEDist p (Measure.sum fun i ↦ a i • μ i) (Measure.sum fun i ↦ a i • ν i)
        ^ p.toReal
      ≤ ∑' i, a i * wassersteinEDist p (μ i) (ν i) ^ p.toReal := by
  simp only [wassersteinEDist_rpow_eq_transportCost hd hp0 hp, ← transportCost_smul (ha _)]
  exact transportCost_sum_le _ _ _

/-- For a finite nonzero exponent, the `p`-th power of the Wasserstein distance is subadditive
under adding measures to both arguments. -/
theorem wassersteinEDist_add_rpow_le (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ μ' ν ν' : Measure X) :
    wassersteinEDist p (μ + μ') (ν + ν') ^ p.toReal
      ≤ wassersteinEDist p μ ν ^ p.toReal + wassersteinEDist p μ' ν' ^ p.toReal := by
  simpa only [wassersteinEDist_rpow_eq_transportCost hd hp0 hp]
    using transportCost_add_le _ μ μ' ν ν'

end TauCeti
