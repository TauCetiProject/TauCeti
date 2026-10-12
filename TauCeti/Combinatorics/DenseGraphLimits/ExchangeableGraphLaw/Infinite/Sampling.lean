/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Mixture
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite

/-!
# The infinite graphon sampler as an exchangeable law

There are two constructions of an infinite random graph associated to a graphon. The explicit
joint sampler `infiniteSampleLaw` draws all vertex positions and edge coins on one probability
space. Independently, the finite sampling laws form `sampleExchangeableLaw`, whose consistent
marginals have a unique extension to an infinite exchangeable law through
`exchangeableGraphLawEquivInfinite`.

This file identifies those constructions. They have the same restriction to every finite window,
so extensionality of measures on infinite graphs shows that their laws agree. In particular, the
explicit joint sampling law is invariant under every permutation of its vertex labels. It then
descends this law to graphon space and proves that the descended sampler is measurable.

## Main definitions

* `TauCeti.DenseGraphLimits.infiniteSampleLawOnSpace` — the joint sampling law of an infinite
  random graph, as a function of the graphon class.

## Main results

* `TauCeti.DenseGraphLimits.infiniteSampleLaw_eq_extension` — the explicit joint sampler is the
  infinite extension of its finite sampling laws;
* `TauCeti.DenseGraphLimits.infiniteSampleLaw_map_comap` — the explicit joint sampler is invariant
  under relabelling by every permutation of `ℕ`;
* `TauCeti.DenseGraphLimits.infiniteSampleLaw_eq_of_cutDist_eq_zero` — graphons at cut distance
  zero, on arbitrary carriers, have the same joint sampling law;
* `TauCeti.DenseGraphLimits.measurable_infiniteSampleLawOnSpace` — the joint sampling law depends
  measurably on the graphon class.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/InfiniteSampler.lean`. The identification here follows `map_sampleInfinite` and
  `map_sampleInfinite_eq_infiniteSampleLaw_mk`, adapted to the finite-window extensionality API
  for Tau Ceti's laws on `SimpleGraph ℕ`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The explicit infinite sampler realizes the abstract extension.** The joint sampling law of
a graphon equals the unique infinite exchangeable law whose finite marginals are the graphon's
finite sampling laws. -/
theorem infiniteSampleLaw_eq_extension (W : Graphon Ω μ) :
    infiniteSampleLaw W = (exchangeableGraphLawEquivInfinite (sampleExchangeableLaw W)).law := by
  apply measure_ext_of_map_restrictFin
  intro n
  rw [infiniteSampleLaw_map_restrictFin,
    exchangeableGraphLawEquivInfinite_law_map_restrictFin, sampleExchangeableLaw_law]

/-- The infinite joint sampling law of a graphon is invariant under relabelling along every
permutation of `ℕ`. -/
@[simp]
theorem infiniteSampleLaw_map_comap (W : Graphon Ω μ) (σ : Equiv.Perm ℕ) :
    (infiniteSampleLaw W).map (SimpleGraph.comap ⇑σ) = infiniteSampleLaw W := by
  rw [infiniteSampleLaw_eq_extension W,
    InfiniteExchangeableGraphLaw.exchangeable]

section CrossCarrier

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- **Joint sampling laws are invariant at cut distance zero.** Two graphons, on arbitrary
probability carriers, at cut distance zero have the same law of the infinite random graph: a law
on infinite graphs is determined by its finite windows, and those are the finite sampling laws. -/
theorem infiniteSampleLaw_eq_of_cutDist_eq_zero (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : cutDist U W = 0) : infiniteSampleLaw U = infiniteSampleLaw W :=
  measure_ext_of_map_restrictFin fun n => by
    rw [infiniteSampleLaw_map_restrictFin, infiniteSampleLaw_map_restrictFin,
      sampleGraph_eq_of_cutDist_eq_zero U W h n]

end CrossCarrier

/-- The law of the infinite random graph as a function of the graphon class. It is well defined
because joint sampling laws are invariant at cut distance zero. -/
def infiniteSampleLawOnSpace : GraphonSpace Ω μ → Measure (SimpleGraph ℕ) :=
  SeparationQuotient.lift infiniteSampleLaw fun U W h =>
    infiniteSampleLaw_eq_of_cutDist_eq_zero U W
      ((graphonSpace_mk_eq_mk_iff U W).1 (SeparationQuotient.mk_eq_mk.2 h))

/-- On a representative, the descended joint sampling law is the joint sampling law. -/
@[simp]
theorem infiniteSampleLawOnSpace_mk (W : Graphon Ω μ) :
    infiniteSampleLawOnSpace (SeparationQuotient.mk W) = infiniteSampleLaw W := (rfl)

/-- An infinite sample from a graphon class has a probability law. -/
instance isProbabilityMeasure_infiniteSampleLawOnSpace (x : GraphonSpace Ω μ) :
    IsProbabilityMeasure (infiniteSampleLawOnSpace x) := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [infiniteSampleLawOnSpace_mk]
  infer_instance

/-- The finite windows of the descended joint sampling law are the descended finite sampling
laws. -/
@[simp]
theorem infiniteSampleLawOnSpace_map_restrictFin (x : GraphonSpace Ω μ) (n : ℕ) :
    (infiniteSampleLawOnSpace x).map (·.restrictFin n) = sampleGraphOnSpace n x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [infiniteSampleLawOnSpace_mk, sampleGraphOnSpace_mk, infiniteSampleLaw_map_restrictFin]

/-- The descended joint sampling law is invariant under relabelling along every permutation of
`ℕ`. -/
@[simp]
theorem infiniteSampleLawOnSpace_map_comap (x : GraphonSpace Ω μ) (σ : Equiv.Perm ℕ) :
    (infiniteSampleLawOnSpace x).map (SimpleGraph.comap ⇑σ) = infiniteSampleLawOnSpace x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [infiniteSampleLawOnSpace_mk, infiniteSampleLaw_map_comap]

/-- **The joint sampling law depends measurably on the graphon class.** The window cylinders
generate the σ-algebra on infinite graphs, and the mass of a cylinder is the mass of a finite
graph under the descended finite sampling law. -/
@[fun_prop]
theorem measurable_infiniteSampleLawOnSpace :
    Measurable (infiniteSampleLawOnSpace (μ := μ)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    SimpleGraph.generateFrom_restrictFinCylinders.symm
    SimpleGraph.isPiSystem_restrictFinCylinders ?_
  intro s hs
  obtain ⟨n, H, rfl⟩ := SimpleGraph.mem_restrictFinCylinders.1 hs
  have hfib : ∀ x : GraphonSpace Ω μ,
      infiniteSampleLawOnSpace x ((fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H}) =
        sampleGraphOnSpace n x {H} := fun x => by
    rw [← infiniteSampleLawOnSpace_map_restrictFin x n,
      Measure.map_apply (SimpleGraph.measurable_restrictFin n) (measurableSet_singleton H)]
  simp_rw [hfib]
  exact (Measure.measurable_coe (measurableSet_singleton H)).comp
    (measurable_sampleGraphOnSpace n)

end DenseGraphLimits

end TauCeti
