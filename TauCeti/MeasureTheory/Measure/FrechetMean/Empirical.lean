/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.CATZero
public import TauCeti.MeasureTheory.Measure.FrechetMean.Stability
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Empirical

/-!
# Strong consistency of empirical Fréchet barycenters

Let `Y 0, Y 1, …` be independent random points of a separable pseudometric space `X`, each with
law `μ`, and let `μ` have finite `p`-moment for an exponent `1 ≤ p < ∞`. A Fréchet barycenter of
the empirical measure `(n + 1)⁻¹ ∑_{i ≤ n} δ_{Y i}` is an *empirical barycenter*: a point
minimizing the empirical radius `R_p(μ_n, x) = ((n + 1)⁻¹ ∑_{i ≤ n} d(x, Y i)ᵖ)^(1/p)`. This file
proves that empirical barycenters are strongly consistent estimators of the barycenters of `μ`.

Almost surely the empirical measures converge to `μ` in the `p`-Wasserstein distance
(`TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae`), and on that single event of full
probability the deterministic stability theory of Fréchet barycenters applies. So, almost surely:

* the empirical radii converge to the radii of `μ` at every point simultaneously, and the minimal
  empirical radius converges to the minimal radius of `μ`;
* for **every** choice of empirical barycenters `b n`, every cluster point of `(b n)` is a Fréchet
  barycenter of `μ`.

The exceptional null set does not depend on the choice of the `b n`, which need not be measurable
in `ω`: the statements quantify over all sequences of barycenters inside the almost-sure event.

On a proper metric space every such sequence has a subsequence converging to a barycenter of `μ`,
and the whole sequence converges when `μ` has only one barycenter. In a proper CAT(0) space the
quadratic barycenter of a law with finite second moment exists and is unique, so the empirical
barycenters converge almost surely to it.

The carrier `X` may itself be a Wasserstein space: for `1 ≤ p < ∞` over a Polish base `Z`, the
space `P_p(Z)` is a separable Borel pseudometric space, so for i.i.d. random laws `Y i` in `P_p(Z)`
the empirical laws converge almost surely in `W_p(P_p(Z))`, and the statements above concern the
empirical Wasserstein barycenters of finitely many random laws. That space need not be proper (it
is when `Z` is compact), so the proper-space statements apply there only under a separate
properness hypothesis.

## Main statements

* `TauCeti.tendsto_frechetRadius_empiricalMeasure_ae` and
  `TauCeti.tendsto_iInf_frechetRadius_empiricalMeasure_ae`: almost surely, the empirical radii and
  the minimal empirical radius converge.
* `TauCeti.isFrechetBarycenter_of_mapClusterPt_empiricalMeasure_ae`: almost surely, every cluster
  point of every sequence of empirical barycenters is a barycenter of `μ`.
* `TauCeti.exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae` and
  `TauCeti.tendsto_of_isFrechetBarycenter_empiricalMeasure_ae`: on a proper metric space, almost
  surely every sequence of empirical barycenters converges along a subsequence to a barycenter of
  `μ`, and converges outright when that barycenter is unique.
* `TauCeti.exists_isFrechetBarycenter_two_tendsto_empiricalMeasure_ae`: in a proper CAT(0) space,
  empirical quadratic barycenters converge almost surely to the quadratic barycenter of `μ`.

## References

* H. Ziezold, *On expected figures and a strong law of large numbers for random elements in
  quasi-metric spaces*, Trans. 7th Prague Conf. Inf. Theory, Vol. A (1977), 591--602.
* R. Bhattacharya and V. Patrangenaru, *Large sample theory of intrinsic and extrinsic sample means
  on manifolds I*, Ann. Statist. 31 (2003), 1--29.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

open Probability

section Separable

variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  {P : Measure Ω} {Y : ℕ → Ω → X} {μ : ProbabilityMeasure X} {p : ℝ≥0∞}

/-- **Consistency of the empirical Fréchet radius.** For i.i.d. random points `Y i` with law `μ` of
finite `p`-moment, `1 ≤ p < ∞`, almost surely the `p`-Fréchet radius of the empirical measure of
`Y 0, …, Y n` converges to that of `μ` at every point. -/
theorem tendsto_frechetRadius_empiricalMeasure_ae (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∀ᵐ ω ∂P, ∀ x, Tendsto
      (fun n ↦ frechetRadius p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) x) atTop
      (𝓝 (frechetRadius p (μ : Measure X) x)) := by
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le hp).ne' hp_top hμ hindep hY] with ω hω x
  exact tendsto_frechetRadius_of_tendsto_wassersteinEDist hp hω x

/-- **Consistency of the minimal empirical Fréchet radius.** For i.i.d. random points `Y i` with
law `μ` of finite `p`-moment, `1 ≤ p < ∞`, almost surely the minimal `p`-Fréchet radius of the
empirical measure of `Y 0, …, Y n` converges to that of `μ`. -/
theorem tendsto_iInf_frechetRadius_empiricalMeasure_ae (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ ⨅ x, frechetRadius p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) x) atTop
      (𝓝 (⨅ x, frechetRadius p (μ : Measure X) x)) := by
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le hp).ne' hp_top hμ hindep hY] with ω hω
  exact tendsto_iInf_frechetRadius_of_tendsto_wassersteinEDist hp hω

/-- **Strong consistency of empirical Fréchet barycenters.** For i.i.d. random points `Y i` with
law `μ` of finite `p`-moment, `1 ≤ p < ∞`, almost surely the following holds for every sequence
`b`: if `b n` is eventually a Fréchet barycenter of the empirical measure of `Y 0, …, Y n`, then
every cluster point of `b` is a Fréchet barycenter of `μ`. -/
theorem isFrechetBarycenter_of_mapClusterPt_empiricalMeasure_ae (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∀ᵐ ω ∂P, ∀ b : ℕ → X,
      (∀ᶠ n in atTop,
        IsFrechetBarycenter p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) (b n)) →
      ∀ c, MapClusterPt c atTop b → IsFrechetBarycenter p (μ : Measure X) c := by
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le hp).ne' hp_top hμ hindep hY] with ω hω b hb c hc
  exact isFrechetBarycenter_of_mapClusterPt hp hω hb hc

end Separable

section Proper

variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {P : Measure Ω} {Y : ℕ → Ω → X} {μ : ProbabilityMeasure X} {p : ℝ≥0∞}

/-- **Empirical Fréchet barycenters converge along a subsequence.** On a proper metric space, for
i.i.d. random points `Y i` with law `μ` of finite `p`-moment, `1 ≤ p < ∞`, almost surely every
sequence `b` such that `b n` is eventually a Fréchet barycenter of the empirical measure of
`Y 0, …, Y n` has a subsequence converging to a Fréchet barycenter of `μ`. -/
theorem exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae (hp : 1 ≤ p)
    (hp_top : p ≠ ∞) (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∀ᵐ ω ∂P, ∀ b : ℕ → X,
      (∀ᶠ n in atTop,
        IsFrechetBarycenter p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) (b n)) →
      ∃ c, IsFrechetBarycenter p (μ : Measure X) c ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (b ∘ φ) atTop (𝓝 c) := by
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le hp).ne' hp_top hμ hindep hY] with ω hω b hb
  exact exists_isFrechetBarycenter_tendsto_comp hp hω hb

/-- **Empirical Fréchet barycenters converge to a unique barycenter.** On a proper metric space,
for i.i.d. random points `Y i` with law `μ` of finite `p`-moment, `1 ≤ p < ∞`, whose only Fréchet
barycenter is `c`, almost surely every sequence `b` such that `b n` is eventually a Fréchet
barycenter of the empirical measure of `Y 0, …, Y n` converges to `c`. -/
theorem tendsto_of_isFrechetBarycenter_empiricalMeasure_ae (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) {c : X}
    (hc : IsFrechetBarycenter p (μ : Measure X) c)
    (hu : (frechetBarycenters p (μ : Measure X)).Subsingleton) :
    ∀ᵐ ω ∂P, ∀ b : ℕ → X,
      (∀ᶠ n in atTop,
        IsFrechetBarycenter p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) (b n)) →
      Tendsto b atTop (𝓝 c) := by
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le hp).ne' hp_top hμ hindep hY] with ω hω b hb
  exact tendsto_of_isFrechetBarycenter hp hω hb hc hu

end Proper

section CATZero

variable {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] [ProperSpace X] [IsCATZeroSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {P : Measure Ω} {Y : ℕ → Ω → X} {μ : ProbabilityMeasure X}

/-- **Strong law of large numbers for barycenters in CAT(0) spaces.** In a proper CAT(0) space,
a law `μ` with finite second moment has a quadratic Fréchet barycenter `c` such that, for i.i.d.
random points `Y i` with law `μ`, almost surely every sequence `b` such that `b n` is eventually a
quadratic Fréchet barycenter of the empirical measure of `Y 0, …, Y n` converges to `c`. -/
theorem exists_isFrechetBarycenter_two_tendsto_empiricalMeasure_ae
    (hμ : HasFiniteMoment 2 (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∃ c, IsFrechetBarycenter 2 (μ : Measure X) c ∧
      ∀ᵐ ω ∂P, ∀ b : ℕ → X,
        (∀ᶠ n in atTop,
          IsFrechetBarycenter 2 (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) (b n)) →
        Tendsto b atTop (𝓝 c) := by
  obtain ⟨x₀, hx₀⟩ := hasFiniteMoment_def.1 hμ
  have hx₀' : frechetRadius 2 (μ : Measure X) x₀ ≠ ⊤ := by
    rw [frechetRadius_def]
    exact hx₀.eLpNorm_ne_top
  obtain ⟨c, hc⟩ := exists_isFrechetBarycenter one_le_two (μ : Measure X) hx₀'
  exact ⟨c, hc, tendsto_of_isFrechetBarycenter_empiricalMeasure_ae one_le_two ENNReal.ofNat_ne_top
    hμ hindep hY hc (subsingleton_frechetBarycenters_two (μ : Measure X))⟩

end CATZero

end TauCeti
