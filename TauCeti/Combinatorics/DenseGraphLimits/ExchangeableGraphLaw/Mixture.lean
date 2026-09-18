/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Sampling
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Forward
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.FiniteOrder

/-!
# Graphon mixtures of exchangeable graph laws

A probability measure `P` on graphon space describes a two-stage random graph: first draw a graphon
class `⟦W⟧ ∼ P`, then sample `G(k, W)`. This file makes that construction precise and packages
its marginals as an exchangeable graph law, the *object direction* of the Diaconis–Janson
correspondence between exchangeable random graphs and mixtures of graphons.

The second stage must depend only on the graphon class, and it does: the law of `G(k, W)` is
determined by its upper masses, which are the homomorphism densities of `W`, and those are
unchanged at cut distance zero. So sampling descends to a map from graphon space to laws of
finite graphs. That map is measurable for the Borel σ-algebra of the cut metric, because on the
finite lattice of graphs a law is measurable in a parameter once its upper-ray masses are, and
those masses are the continuous descended homomorphism densities. The mixture law at level `k` is
the Giry-monad bind of `P` against this map. Its consistency under relabelling is inherited
fiberwise from the sampling laws, its upper mass of a pattern `F` is the `P`-average of `t(F, ·)`,
and the mixture of a Dirac mass at `⟦W⟧` is the sampling law of `W`.

## Main definitions

* `TauCeti.DenseGraphLimits.sampleGraphOnSpace` — the law of the sampled graph, as a function of
  the graphon class;
* `TauCeti.DenseGraphLimits.mixtureExchangeableLaw` — the exchangeable graph law of a mixing
  measure on graphon space.

## Main results

* `TauCeti.DenseGraphLimits.sampleGraph_eq_of_cutDist_eq_zero` — graphons at cut distance zero,
  on arbitrary carriers, have the same sampling laws;
* `TauCeti.DenseGraphLimits.measurable_sampleGraphOnSpace` — the sampling law depends measurably
  on the graphon class;
* `TauCeti.DenseGraphLimits.upperMass_mixtureExchangeableLaw` — the upper mass of a pattern under
  a mixture law is the average of its homomorphism density against the mixing measure;
* `TauCeti.DenseGraphLimits.mixtureExchangeableLaw_diracProba` — the mixture of a Dirac mass at a
  graphon class is that graphon's sampling law.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 11.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

section CrossCarrier

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- **Sampling laws are invariant at cut distance zero.** Two graphons, on arbitrary probability
carriers, at cut distance zero have the same sampling laws: a law on the finite lattice of graphs is
determined by its upper-ray masses, which are homomorphism densities. -/
theorem sampleGraph_eq_of_cutDist_eq_zero (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : cutDist U W = 0) (n : ℕ) : sampleGraph U n = sampleGraph W n := by
  classical
  refine Measure.ext_of_Ici_of_finite _ _ fun F => ?_
  rw [sampleGraph_Ici, sampleGraph_Ici, forall_homDensity_eq_of_cutDist_eq_zero U W h n F]

end CrossCarrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The law of the `n`-vertex sampled graph as a function of the graphon class. It is well defined
because sampling laws are invariant at cut distance zero. -/
def sampleGraphOnSpace (n : ℕ) : GraphonSpace Ω μ → Measure (SimpleGraph (Fin n)) :=
  SeparationQuotient.lift (sampleGraph · n) fun U W h =>
    sampleGraph_eq_of_cutDist_eq_zero U W
      ((graphonSpace_mk_eq_mk_iff U W).1 (SeparationQuotient.mk_eq_mk.2 h)) n

/-- On a representative, the descended sampling law is the sampling law. -/
@[simp]
theorem sampleGraphOnSpace_mk (n : ℕ) (W : Graphon Ω μ) :
    sampleGraphOnSpace n (SeparationQuotient.mk W) = sampleGraph W n := (rfl)

/-- A sample from a graphon class has a probability law. -/
instance isProbabilityMeasure_sampleGraphOnSpace (n : ℕ) (x : GraphonSpace Ω μ) :
    IsProbabilityMeasure (sampleGraphOnSpace n x) := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [sampleGraphOnSpace_mk]
  infer_instance

/-- The probability that a sample from a graphon class contains a pattern is the descended
homomorphism density. -/
@[simp]
theorem sampleGraphOnSpace_Ici {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (x : GraphonSpace Ω μ) :
    sampleGraphOnSpace n x (Set.Ici F) = ENNReal.ofReal (homDensityOnSpace F x) := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [sampleGraphOnSpace_mk, homDensityOnSpace_mk, sampleGraph_Ici]

/-- **The sampling law depends measurably on the graphon class.** Its upper-ray masses are the
continuous descended homomorphism densities, and on the finite lattice of graphs these control
every evaluation. -/
@[fun_prop]
theorem measurable_sampleGraphOnSpace (n : ℕ) :
    Measurable (sampleGraphOnSpace (μ := μ) n) := by
  classical
  refine Measurable.measure_of_Ici_of_finite fun F => ?_
  simp_rw [sampleGraphOnSpace_Ici]
  exact ENNReal.measurable_ofReal.comp (continuous_homDensityOnSpace F).measurable

/-- The descended sampling laws are consistent under restriction along every injection of
labels. -/
@[simp]
theorem sampleGraphOnSpace_map_comap {k l : ℕ} (f : Fin k ↪ Fin l) (x : GraphonSpace Ω μ) :
    (sampleGraphOnSpace l x).map (SimpleGraph.comap ⇑f) = sampleGraphOnSpace k x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [sampleGraphOnSpace_mk, sampleGraphOnSpace_mk, sampleGraph_map_comap]

/-- **The mixture map.** The exchangeable graph law of a mixing measure `P` on graphon space:
draw a graphon class from `P`, then sample from it. The level-`k` marginal is the bind of `P`
against the descended sampling law. -/
def mixtureExchangeableLaw (P : ProbabilityMeasure (GraphonSpace Ω μ)) :
    ExchangeableGraphLaw where
  law k := (P : Measure (GraphonSpace Ω μ)).bind (sampleGraphOnSpace k)
  prob k := ⟨by
    rw [Measure.bind_apply MeasurableSet.univ (measurable_sampleGraphOnSpace k).aemeasurable]
    simp⟩
  consistent {k l} f := by
    ext s hs
    have hf := SimpleGraph.measurable_comap (V := Fin k) ⇑f
    rw [Measure.map_apply hf hs,
      Measure.bind_apply (hf hs) (measurable_sampleGraphOnSpace l).aemeasurable,
      Measure.bind_apply hs (measurable_sampleGraphOnSpace k).aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [← Measure.map_apply hf hs, sampleGraphOnSpace_map_comap]

/-- The level-`k` marginal of a mixture law is the bind of the mixing measure against the
descended sampling law. -/
@[simp]
theorem mixtureExchangeableLaw_law (P : ProbabilityMeasure (GraphonSpace Ω μ)) (k : ℕ) :
    (mixtureExchangeableLaw P).law k =
      (P : Measure (GraphonSpace Ω μ)).bind (sampleGraphOnSpace k) := (rfl)

/-- **The coordinate law of a mixture.** The upper mass of a pattern under the mixture law of `P`
is the `P`-average of the pattern's descended homomorphism density:
`upperMass F = ∫ t(F, ·) dP`. -/
@[simp]
theorem upperMass_mixtureExchangeableLaw (P : ProbabilityMeasure (GraphonSpace Ω μ)) {k : ℕ}
    (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    (mixtureExchangeableLaw P).upperMass F =
      ∫ x, homDensityOnSpace F x ∂(P : Measure (GraphonSpace Ω μ)) := by
  have hset : {G : SimpleGraph (Fin k) | F ≤ G} = Set.Ici F := by
    ext
    simp
  rw [ExchangeableGraphLaw.upperMass_def, mixtureExchangeableLaw_law, hset,
    Measure.bind_apply MeasurableSet.of_discrete (measurable_sampleGraphOnSpace k).aemeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (homDensityOnSpace_nonneg F))
      (continuous_homDensityOnSpace F).aestronglyMeasurable]
  simp_rw [sampleGraphOnSpace_Ici]

/-- **Dirac fibers of the mixture map.** Mixing against the Dirac mass at a graphon class samples
from that class. -/
@[simp]
theorem mixtureExchangeableLaw_diracProba (W : Graphon Ω μ) :
    mixtureExchangeableLaw (diracProba (SeparationQuotient.mk W)) = sampleExchangeableLaw W :=
  ExchangeableGraphLaw.ext fun k => by
    rw [mixtureExchangeableLaw_law, sampleExchangeableLaw_law, ← sampleGraphOnSpace_mk]
    exact Measure.dirac_bind (measurable_sampleGraphOnSpace k) _

end DenseGraphLimits

end TauCeti
