/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Empirical
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PopulationBarycenter
import TauCeti.MeasureTheory.Measure.FrechetMean.Stability
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Strong consistency of empirical Wasserstein barycenters

Let `Y 0, Y 1, …` be independent random laws in the Wasserstein space `P_p(X)`, all with
population law `Q`. Almost surely their empirical laws converge to `Q` in `W_p(P_p(X))`. When
`X` is proper, barycenters of finitely supported laws converging to `Q` form a relatively compact
family even though `P_p(X)` itself need not be proper. Combining these two facts gives strong
consistency of empirical Wasserstein barycenters without imposing a false properness hypothesis
on `P_p(X)`.

The conclusions are choice-free: on one event of full probability they hold for every sequence
selecting a barycenter of each empirical law. Every such sequence has compact closure, and every
one of its cluster points is a population Wasserstein barycenter. Hence it has a convergent
subsequence, and it converges outright when the population barycenter is unique. No measurability
of the selected barycenters is assumed or needed.

The cluster-point characterization needs no properness at all: it is the general
`TauCeti.isFrechetBarycenter_of_mapClusterPt_empiricalMeasure_ae`, applied verbatim to the separable
carrier `WassersteinSpace p X`, so it is not restated here.

## Main statements

* `TauCeti.WassersteinSpace.isCompact_closure_range_of_isFrechetBarycenter_empiricalMeasure_ae`:
  almost surely, every sequence of empirical Wasserstein barycenters has compact closure.
* `TauCeti.WassersteinSpace.exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae`: almost
  surely, every such sequence has a subsequence converging to a population barycenter.
* `TauCeti.WassersteinSpace.tendsto_of_isFrechetBarycenter_empiricalMeasure_ae`: uniqueness of the
  population barycenter upgrades this to convergence of every sequence of empirical barycenters.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace TauCeti

open Probability

namespace WassersteinSpace

variable {Omega X : Type*} [MeasurableSpace Omega] [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [ProperSpace X] [PolishSpace X]
  {P : Measure Omega} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Y : ℕ → Omega → WassersteinSpace p X}
  {Q : ProbabilityMeasure (WassersteinSpace p X)}

/-- **Relative compactness of empirical Wasserstein barycenters.** Let `Y i` be i.i.d. random
laws in `P_p(X)` with population law `Q`, where `X` is proper and `1 ≤ p < ∞`. Almost surely,
every sequence choosing a `p`-Wasserstein barycenter of each empirical law has compact closure in
`P_p(X)`.

The exceptional null set is independent of the choice of barycenters, which need not be a
measurable function of the sample. -/
theorem isCompact_closure_range_of_isFrechetBarycenter_empiricalMeasure_ae
    (hp_top : p ≠ ∞) (hQ : HasFiniteMoment p (Q : Measure (WassersteinSpace p X)))
    (hindep : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (Q : Measure (WassersteinSpace p X)) P) :
    ∀ᵐ omega ∂P, ∀ b : ℕ → WassersteinSpace p X,
      (∀ n, IsFrechetBarycenter p
        (empiricalMeasure (fun i ↦ Y i omega) n : Measure (WassersteinSpace p X)) (b n)) →
      IsCompact (closure (range b)) := by
  let _ : Fact (p ≠ ∞) := ⟨hp_top⟩
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le Fact.out).ne' hp_top hQ hindep hY] with omega homega b hb
  exact isCompact_closure_range_of_isFrechetBarycenter hp_top
    (fun n ↦ exists_finset_ae_mem_empiricalMeasure (fun i ↦ Y i omega) n) homega hb

/-- **Strong subsequential consistency of empirical Wasserstein barycenters.** Let `Y i` be i.i.d.
random laws in `P_p(X)` with population law `Q`, where `X` is proper and `1 ≤ p < ∞`. Almost
surely, every sequence choosing one barycenter of each empirical law has a subsequence converging
to a population Wasserstein barycenter. -/
theorem exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae
    (hp_top : p ≠ ∞) (hQ : HasFiniteMoment p (Q : Measure (WassersteinSpace p X)))
    (hindep : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (Q : Measure (WassersteinSpace p X)) P) :
    ∀ᵐ omega ∂P, ∀ b : ℕ → WassersteinSpace p X,
      (∀ n, IsFrechetBarycenter p
        (empiricalMeasure (fun i ↦ Y i omega) n : Measure (WassersteinSpace p X)) (b n)) →
      ∃ c, IsFrechetBarycenter p (Q : Measure _) c ∧
        ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (b ∘ phi) atTop (nhds c) := by
  let _ : Fact (p ≠ ∞) := ⟨hp_top⟩
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
    (zero_lt_one.trans_le Fact.out).ne' hp_top hQ hindep hY] with omega homega b hb
  exact exists_isFrechetBarycenter_tendsto_comp hp_top
    (fun n ↦ exists_finset_ae_mem_empiricalMeasure (fun i ↦ Y i omega) n) homega hb

/-- **Strong consistency under uniqueness.** If `Q` has a unique `p`-Wasserstein barycenter `c`,
then almost surely every sequence choosing a barycenter of each empirical law converges to `c`.
The selected sequence need not be measurable. -/
theorem tendsto_of_isFrechetBarycenter_empiricalMeasure_ae
    (hp_top : p ≠ ∞) (hQ : HasFiniteMoment p (Q : Measure (WassersteinSpace p X)))
    (hindep : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (Q : Measure (WassersteinSpace p X)) P)
    {c : WassersteinSpace p X} (hc : IsFrechetBarycenter p (Q : Measure _) c)
    (hu : (frechetBarycenters p (Q : Measure (WassersteinSpace p X))).Subsingleton) :
    ∀ᵐ omega ∂P, ∀ b : ℕ → WassersteinSpace p X,
      (∀ n, IsFrechetBarycenter p
        (empiricalMeasure (fun i ↦ Y i omega) n : Measure (WassersteinSpace p X)) (b n)) →
      Tendsto b atTop (nhds c) := by
  let _ : Fact (p ≠ ∞) := ⟨hp_top⟩
  filter_upwards [tendsto_wassersteinEDist_empiricalMeasure_ae
      (zero_lt_one.trans_le Fact.out).ne' hp_top hQ hindep hY] with omega homega b hb
  have hcompact := isCompact_closure_range_of_isFrechetBarycenter hp_top
    (fun n ↦ exists_finset_ae_mem_empiricalMeasure (fun i ↦ Y i omega) n) homega hb
  exact hcompact.tendsto_nhds_of_unique_mapClusterPt
    (.of_forall fun n ↦ subset_closure (mem_range_self n)) fun y _ hy ↦
      hu (mem_frechetBarycenters.2
        (TauCeti.isFrechetBarycenter_of_mapClusterPt Fact.out homega (.of_forall hb) hy))
        (mem_frechetBarycenters.2 hc)

end WassersteinSpace

end TauCeti
