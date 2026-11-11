/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# The Wasserstein distance of mixtures

For a finite nonzero exponent `p`, the `p`-th power of the `p`-Wasserstein distance is jointly
convex in the two laws: for weights `a i`,

`W_p (∑ i, a i • μ i, ∑ i, a i • ν i) ^ p ≤ ∑ i, a i * W_p (μ i, ν i) ^ p`.

For a probability vector `a` this is the mixture bound for `W_p`. It is the transport-cost
convexity of `TauCeti.transportCost_smul` and `TauCeti.transportCost_sum_le` read through the
bridge `TauCeti.wassersteinEDist_rpow_eq_transportCost` for the cost `edist ^ p`.

The weights are only required to be finite and need not sum to `1`, and the laws are arbitrary
measures. For the weighted mixture results the ground distance must be jointly measurable, since
the transport cost is computed through it, but `1 ≤ p` is not used. The additive subadditivity
`TauCeti.wassersteinEDist_add_rpow_le` needs no measurability hypothesis. The exponent is
finite: at `p = ∞` the power `p.toReal` is `0`, and the corresponding estimate instead bounds
the distance of the mixtures by the largest distance of a pair with positive weight, which is a
different statement not proved here.

In one argument, convexity is strict as soon as the optimal plans out of the fixed law into the
mixture are induced by maps: a mixture of optimal plans that is itself optimal is then a graph
plan, which forces the two mixed laws to agree (`TauCeti.transportCost_smul_add_smul_lt`).

## Main statements

* `TauCeti.wassersteinEDist_finset_sum_smul_rpow_le` — the mixture bound for finitely many laws;
* `TauCeti.wassersteinEDist_sum_smul_rpow_le` — the mixture bound for countably many laws, written
  with `MeasureTheory.Measure.sum`;
* `TauCeti.wassersteinEDist_add_rpow_le` — subadditivity of `W_p ^ p` for two pairs of measures;
* `TauCeti.wassersteinEDist_smul_add_smul_rpow_le` — convexity of `W_p ^ p` in one argument, the
  other being fixed;
* `TauCeti.wassersteinEDist_smul_add_smul_rpow_lt` — on a Polish metric space, strict convexity
  of `W_p ^ p` in one argument when the optimal plans for `edist ^ p` from the fixed law to the
  mixture `a • ν₀ + b • ν₁` of two distinct probability laws are induced by maps.

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

/-- The powered Wasserstein bound is subadditive under adding measures to both arguments.
For `p = 0` or `p = ∞`, `p.toReal = 0` and the bound reduces to `1 ≤ 1 + 1`. No measurability of
the ground distance is needed: a coupling for which it is not almost everywhere measurable has
objective `∞`. -/
theorem wassersteinEDist_add_rpow_le (μ μ' ν ν' : Measure X) :
    wassersteinEDist p (μ + μ') (ν + ν') ^ p.toReal
      ≤ wassersteinEDist p μ ν ^ p.toReal + wassersteinEDist p μ' ν' ^ p.toReal := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp : p = ∞
  · simp [hp]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- a coupling realising the powered distance up to any slack
  have key (μ ν : Measure X) {c : ℝ≥0∞} (hc : wassersteinEDist p μ ν ^ p.toReal < c) :
      ∃ π, IsCoupling π μ ν ∧
        eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π ^ p.toReal < c := by
    obtain ⟨π, hπ, h⟩ := wassersteinEDist_lt_iff.1
      ((ENNReal.lt_rpow_inv_iff hr).2 hc : wassersteinEDist p μ ν < c ^ p.toReal⁻¹)
    exact ⟨π, hπ, (ENNReal.lt_rpow_inv_iff hr).1 h⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb ↦ ?_
  have hδ : (ε / 2 : ℝ≥0∞) ≠ 0 := by simp [hε.ne']
  obtain ⟨π, hπ, h₁⟩ := key μ ν (ENNReal.lt_add_right (ne_top_of_lt (lt_of_le_of_lt le_self_add hb))
    hδ)
  obtain ⟨π', hπ', h₂⟩ := key μ' ν' (ENNReal.lt_add_right
    (ne_top_of_lt (lt_of_le_of_lt le_add_self hb)) hδ)
  calc _ ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (π + π') ^ p.toReal :=
        ENNReal.rpow_le_rpow (wassersteinEDist_le (hπ.add hπ') p) hr.le
    _ ≤ _ := eLpNorm_add_measure_rpow_le _ π π'
    _ ≤ _ := add_le_add h₁.le h₂.le
    _ = _ := by rw [add_add_add_comm, ENNReal.add_halves]

/-- **Convexity of `W_p ^ p` in one argument.** For a finite nonzero exponent and weights with
`a + b = 1`, the `p`-th power of the Wasserstein distance from `μ` to the mixture `a • ν₀ + b • ν₁`
is at most the mixture of the `p`-th powers of the distances from `μ` to `ν₀` and to `ν₁`. -/
theorem wassersteinEDist_smul_add_smul_rpow_le (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {a b : ℝ≥0∞} (hab : a + b = 1) (μ ν₀ ν₁ : Measure X) :
    wassersteinEDist p μ (a • ν₀ + b • ν₁) ^ p.toReal
      ≤ a * wassersteinEDist p μ ν₀ ^ p.toReal + b * wassersteinEDist p μ ν₁ ^ p.toReal := by
  obtain ⟨ha, hb⟩ := ENNReal.add_ne_top.1 (hab ▸ ENNReal.one_ne_top)
  simp only [wassersteinEDist_rpow_eq_transportCost hd hp0 hp]
  calc transportCost _ μ (a • ν₀ + b • ν₁) = transportCost _ (a • μ + b • μ) (a • ν₀ + b • ν₁) := by
        rw [← add_smul, hab, one_smul]
    _ ≤ transportCost _ (a • μ) (a • ν₀) + transportCost _ (b • μ) (b • ν₁) :=
        transportCost_add_le _ _ _ _ _
    _ = _ := by rw [transportCost_smul ha, transportCost_smul hb]

/-- **Strict convexity of `W_p ^ p` in one argument.** On a Polish metric space, let `μ`, `ν₀`
and `ν₁` be probability laws with `ν₀ ≠ ν₁`, and let `a, b` be nonzero weights with `a + b = 1`.
If every optimal plan for the cost `edist ^ p` from `μ` to the mixture `a • ν₀ + b • ν₁` is the
graph plan of a map, then the `p`-th power of the Wasserstein distance from `μ` to the mixture is
strictly below the mixture of the `p`-th powers of the distances from `μ` to `ν₀` and to `ν₁`. -/
theorem wassersteinEDist_smul_add_smul_rpow_lt {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] [CompleteSpace Y] (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {μ ν₀ ν₁ : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgraph : ∀ π, IsOptimalCoupling (fun z : Y × Y ↦ edist z.1 z.2 ^ p.toReal) π μ
      (a • ν₀ + b • ν₁) → ∃ T : Y → Y, AEMeasurable T μ ∧ π = graphPlan T μ)
    (hne : ν₀ ≠ ν₁) :
    wassersteinEDist p μ (a • ν₀ + b • ν₁) ^ p.toReal
      < a * wassersteinEDist p μ ν₀ ^ p.toReal + b * wassersteinEDist p μ ν₁ ^ p.toReal := by
  obtain ⟨π₀, h₀⟩ := exists_isOptimalCoupling_edist_rpow μ ν₀ p.toReal
  obtain ⟨π₁, h₁⟩ := exists_isOptimalCoupling_edist_rpow μ ν₁ p.toReal
  simp only [wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp]
  exact transportCost_smul_add_smul_lt hab ha hb h₀ h₁ hgraph hne

end TauCeti
