/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Consistency
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Unbiased

/-!
# The sampling laws of a graphon form an exchangeable graph law

Sampling `l` independent points from a graphon and then tossing an independent coin for each
unordered pair produces a law on `SimpleGraph (Fin l)`. Those laws are consistent under
restriction of the label set — that is
`TauCeti.DenseGraphLimits.sampleGraph_map_comap` — so the whole family is an exchangeable graph
law, which is what this file packages.

The upper mass of a pattern under a sampling law is its graphon homomorphism density: the sample
contains `F` exactly when every edge of `F` wins its coin toss, whose conditional probability at
fixed positions is the product of the edge factors of `F`.

## Main definitions

* `TauCeti.DenseGraphLimits.sampleExchangeableLaw` — the sampling laws of a graphon, packaged as
  an exchangeable graph law.

## Main results

* `TauCeti.DenseGraphLimits.upperMass_sampleExchangeableLaw` — the upper mass of a pattern under
  a sampling law is its homomorphism density.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 10.1.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/ExchangeableGraphLaw.lean`. The packaging of the sampling laws and the identification of
  the upper mass with a homomorphism density follow that source, adapted to Tau Ceti's strict
  graphon carrier.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The sampling laws of a fixed graphon, packaged as an exchangeable graph law. -/
def sampleExchangeableLaw (W : Graphon Ω μ) : ExchangeableGraphLaw where
  law k := sampleGraph W k
  prob k := sampleGraph_isProbabilityMeasure W k
  consistent f := sampleGraph_map_comap W f

@[simp]
theorem sampleExchangeableLaw_law (W : Graphon Ω μ) (k : ℕ) :
    (sampleExchangeableLaw W).law k = sampleGraph W k := (rfl)

open Classical in
/-- **The sampling anchor.** The upper mass of a pattern under a graphon's sampling law is its
homomorphism density: `P(F ≤ G(k, W)) = t(F, W)`. -/
@[simp]
theorem upperMass_sampleExchangeableLaw {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    (sampleExchangeableLaw W).upperMass F = homDensity F W := by
  have hset : {G : SimpleGraph (Fin k) | F ≤ G} = ↑(Finset.univ.filter (F ≤ ·)) := by
    ext G
    simp
  rw [ExchangeableGraphLaw.upperMass_def, sampleExchangeableLaw_law, hset,
    ← sum_measure_singleton]
  simp_rw [sampleGraph_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun G _ => sampleMass_nonneg W G,
    sum_sampleMass_supergraph_eq_homDensity W F,
    ENNReal.toReal_ofReal (homDensity_nonneg F W)]

end DenseGraphLimits

end TauCeti
