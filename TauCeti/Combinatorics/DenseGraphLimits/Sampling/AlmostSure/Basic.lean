/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Summability
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic

/-!
# Almost-sure convergence of sampled homomorphism densities

Sample the infinite `W`-random graph once, from the joint sampling law `infiniteSampleLaw W`, and
read off its growing windows on the labels below `n`; each window has the law `G(n, W)`. This file
shows that, almost surely, the homomorphism densities of the windows converge to those of `W`:
for a fixed finite graph `F`, and simultaneously for every finite graph on `Fin k` and every `k`.

The last form is phrased with the step graphons `finiteGraphGraphon` of the windows, which are
graphons on the unit interval: almost surely every homomorphism density of the windows' step
graphons converges to the corresponding density of `W`. Combined with the equivalence between
convergence of all homomorphism densities and convergence in cut distance, this is what yields
almost-sure convergence of the windows to `W` in cut distance.

## Main results

* `TauCeti.DenseGraphLimits.tendsto_homDensityFin_infiniteSampleLaw_ae` — for a fixed finite graph
  `F`, the homomorphism densities of the windows converge to `t(F, W)` almost surely.
* `TauCeti.DenseGraphLimits.tendsto_homDensityFin_infiniteSampleLaw_ae_forall` — almost surely this
  holds for every graph on `Fin k`, simultaneously for all `k`.
* `TauCeti.DenseGraphLimits.tendsto_homDensity_finiteGraphGraphon_infiniteSampleLaw_ae_forall` —
  the same statement for the step graphons of the windows.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/AlmostSureSampling.lean`, whose
  proof route is adapted here.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Almost-sure convergence of a sampled homomorphism density.** For a fixed finite graph `F`,
almost every infinite `W`-random graph `G` has windows whose homomorphism densities converge to
the graphon density:

`t(F, G[{0, …, n - 1}]) → t(F, W)` as `n → ∞`. -/
theorem tendsto_homDensityFin_infiniteSampleLaw_ae (W : Graphon Ω μ) {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] :
    ∀ᵐ G ∂infiniteSampleLaw W,
      Tendsto (fun n => homDensityFin F (G.restrictFin n)) atTop (𝓝 (homDensity F W)) := by
  -- Borel--Cantelli at each tolerance `1 / (m + 1)`, through the finite marginals.
  have htol (m : ℕ) : ∀ᵐ G ∂infiniteSampleLaw W, ∀ᶠ n in atTop,
      |homDensityFin F (G.restrictFin (n + 1)) - homDensity F W| < 1 / ((m : ℝ) + 1) := by
    have hsum := SimpleGraph.tsum_sampleGraph_homDensityFin_tail_ne_top F W
      (Nat.one_div_pos_of_nat (n := m))
    simp_rw [← infiniteSampleLaw_map_restrictFin W,
      Measure.map_apply (SimpleGraph.measurable_restrictFin _) MeasurableSet.of_discrete] at hsum
    filter_upwards [ae_eventually_notMem hsum] with G hG
    filter_upwards [hG] with n hn
    simpa using hn
  filter_upwards [ae_all_iff.2 htol] with G hG
  rw [← tendsto_add_atTop_iff_nat 1, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hG m] with n hn
  rw [Real.dist_eq]
  exact hn.trans hm

/-- **Almost-sure convergence of all sampled homomorphism densities.** Almost every infinite
`W`-random graph `G` has windows whose homomorphism densities converge to those of `W`, for every
finite graph on `Fin k` and every `k` at once. -/
theorem tendsto_homDensityFin_infiniteSampleLaw_ae_forall (W : Graphon Ω μ) :
    ∀ᵐ G ∂infiniteSampleLaw W, ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      Tendsto (fun n => homDensityFin F (G.restrictFin n)) atTop (𝓝 (homDensity F W)) := by
  classical
  -- A countable intersection over the countably many graphs on `Fin k`, `k : ℕ`.
  have h : ∀ᵐ G ∂infiniteSampleLaw W, ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
      Tendsto (fun n => homDensityFin F (G.restrictFin n)) atTop (𝓝 (homDensity F W)) :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun F => tendsto_homDensityFin_infiniteSampleLaw_ae W F
  filter_upwards [h] with G hG k F _
  convert hG k F

/-- **Almost-sure convergence of the sampled step graphons' homomorphism densities.** Almost every
infinite `W`-random graph `G` has windows `G[{0, …, n}]` whose step graphons on the unit interval
satisfy `t(F, W_{G[{0, …, n}]}) → t(F, W)` for every finite graph `F` on `Fin k` and every `k`
at once. The window has `n + 1` vertices, so the step graphon is defined for every `n`. -/
theorem tendsto_homDensity_finiteGraphGraphon_infiniteSampleLaw_ae_forall (W : Graphon Ω μ) :
    ∀ᵐ G ∂infiniteSampleLaw W, ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      Tendsto (fun n => homDensity F (finiteGraphGraphon (G.restrictFin (n + 1)))) atTop
        (𝓝 (homDensity F W)) := by
  filter_upwards [tendsto_homDensityFin_infiniteSampleLaw_ae_forall W] with G hG k F _
  simp_rw [homDensity_finiteGraphGraphon F (Nat.succ_pos _)]
  exact (tendsto_add_atTop_iff_nat 1).2 (hG k F)

end DenseGraphLimits

end TauCeti
