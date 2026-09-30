/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Correspondence
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Exchangeable laws on infinite graphs are integrals of joint sampling laws

A probability measure `P` on graphon space describes a two-stage infinite random graph: draw a
graphon class from `P`, then run the joint sampler of that class on all of `ℕ` at once. This file
builds the second stage as a map out of graphon space and identifies the two-stage law with the
Giry-monad bind, so that the correspondence between mixing measures and exchangeable laws on
infinite graphs reads as a genuine mixture on `SimpleGraph ℕ`.

The second stage is well defined because the joint sampling law of a graphon is determined by its
finite windows, which are the finite sampling laws, and those are unchanged at cut distance zero.
It is measurable for the Borel σ-algebra of the cut metric because the window cylinders generate
the σ-algebra on infinite graphs and each cylinder mass is a finite sampling mass, already known
to be measurable in the graphon class.

With the mixture identity in hand, every exchangeable law on infinite graphs is the integral of
joint sampling laws against one mixing measure on graphon space, and that mixing measure is
unique. This is the integral form of the Diaconis–Janson correspondence; its finite-window form
is `mixtureExchangeableLaw`.

## Main definitions

* `TauCeti.DenseGraphLimits.infiniteSampleLawOnSpace` — the joint sampling law of an infinite
  random graph, as a function of the graphon class.

## Main results

* `TauCeti.DenseGraphLimits.infiniteSampleLaw_eq_of_cutDist_eq_zero` — graphons at cut distance
  zero, on arbitrary carriers, have the same joint sampling law;
* `TauCeti.DenseGraphLimits.measurable_infiniteSampleLawOnSpace` — the joint sampling law depends
  measurably on the graphon class;
* `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_law` — the law attached to a mixing measure is
  the integral of the joint sampling laws against it;
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`
  — every exchangeable law on infinite graphs is such an integral, for exactly one mixing measure.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Theorem 5.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

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

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

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

/-- **A graphon mixture is an integral of joint sampling laws.** The exchangeable law on infinite
graphs attached to a mixing measure `P` on graphon space is the bind of `P` against the descended
joint sampling law: draw a graphon class from `P`, then run the infinite sampler. -/
@[simp]
theorem graphonMixtureLawEquiv_law (P : ProbabilityMeasure GraphonSpaceI) :
    (graphonMixtureLawEquiv P).law =
      (P : Measure GraphonSpaceI).bind infiniteSampleLawOnSpace := by
  refine measure_ext_of_map_restrictFin fun n => ?_
  rw [TauCeti.MeasureTheory.map_bind measurable_infiniteSampleLawOnSpace.aemeasurable
    (SimpleGraph.measurable_restrictFin n)]
  simp_rw [infiniteSampleLawOnSpace_map_restrictFin]
  rw [graphonMixtureLawEquiv_apply, exchangeableGraphLawEquivInfinite_law_map_restrictFin,
    mixtureExchangeableLaw_law]

/-- **Every exchangeable law on infinite graphs is a graphon mixture, for exactly one mixing
measure.** The integral form of the Diaconis–Janson correspondence: the law is the bind of a
unique probability measure on graphon space against the joint sampling laws. -/
theorem InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace
    (L : InfiniteExchangeableGraphLaw) :
    ∃! P : ProbabilityMeasure GraphonSpaceI,
      (P : Measure GraphonSpaceI).bind infiniteSampleLawOnSpace = L.law := by
  refine ⟨graphonMixtureLawEquiv.symm L, ?_, fun Q hQ => ?_⟩
  · have hP := graphonMixtureLawEquiv_law (graphonMixtureLawEquiv.symm L)
    rw [Equiv.apply_symm_apply] at hP
    exact hP.symm
  · refine graphonMixtureLawEquiv.injective ?_
    rw [Equiv.apply_symm_apply]
    exact InfiniteExchangeableGraphLaw.ext (by rw [graphonMixtureLawEquiv_law, hQ])

end DenseGraphLimits

end TauCeti
