/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Expose inner regularity of Polish measures for the bundled compactness instance.
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.MetricSpace.Polish
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
-- Proof-only: continuous marginal maps and Prokhorov's relative compactness theorem.
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# The transport plans of two probability measures form a compact set

The couplings of two fixed probability measures form a subset of the probability measures on the
product, and the weak topology restricts to it. This file proves that this set is weakly **closed**
and, on a Polish factor pair, weakly **compact**. Compactness is what makes the primal transport
problem solvable: a lower semicontinuous cost attains its infimum on a nonempty compact set.

The two halves are proved at their own generality and for their own reasons.

*Closedness* is a statement about the marginal maps. Pushing forward along the two coordinate
projections is continuous for the weak topology, and being a coupling of `μ` and `ν` says exactly
that the two pushforwards are `μ` and `ν`; so the coupling set is an intersection of two preimages
of points. The factors and their product need measurable opens; neither Borel sigma algebras nor
second countability is needed for this argument. The set is closed as soon as points are closed in
the two spaces of marginals, which is the `T1Space` hypothesis carried here. Mathlib derives it from
`MeasureTheory.ProbabilityMeasure.t2Space`, whose hypotheses are `BorelSpace` together with
`HasOuterApproxClosed` — so it is available on the metrizable factors the later sections work
with, but is asked for explicitly here rather than assumed.

*Compactness* is Prokhorov's theorem. Tightness of the coupling set follows from tightness of the
two marginals alone: a compact rectangle `K₁ ×ˢ K₂` misses at most the mass its two sides miss,
uniformly over all couplings, because every coupling has the same two marginals. Tightness is
therefore stated for arbitrary measures with tight marginals, and the topological hypotheses enter
only when Prokhorov's theorem is applied.

Both halves are then run with *moving* marginals: a family of plans that is eventually feasible for
two tight families of marginals is relatively compact, and each of its weak limits along a finer
filter is a coupling of the limiting marginals. Nothing about a cost function enters, which is why
this lives here rather than in the stability file that consumes it.

## Main statements

* `TauCeti.isClosed_setOfPred_isCoupling` — the couplings of `μ` and `ν` are a weakly closed set of
  probability measures on the product, with canonical Polish and compact-pseudometrizable
  specialisations;
* `TauCeti.isTightMeasureSet_setOfPred_exists_isCoupling` and
  `TauCeti.isTightMeasureSet_setOfPred_isCoupling` — the couplings of two tight families of
  measures, and of two tight measures, form a tight family, with no topological hypothesis beyond
  the two topologies themselves;
* `TauCeti.isCompact_setOfPred_isCoupling_of_prokhorov` — the abstract compactness theorem for a
  product on which tight families of probability measures have compact closure;
* `TauCeti.isCompact_setOfPred_isCoupling` — the Prokhorov theorem for a Hausdorff Borel product,
  with compact-metrizable and Polish specialisations;
* `TauCeti.isCoupling_of_tendsto` — the coupling constraint passes to weak limits when the
  marginals converge;
* `TauCeti.exists_isCoupling_tendsto_of_isTightMeasureSet` — relative compactness of a family of
  plans with tight varying marginals;
* `TauCeti.Coupling.instCompactSpace` — the bundled couplings of inner-regular probability
  measures form a compact space when the factors are Hausdorff with measurable opens, the product
  is Borel, and both spaces of marginal probability measures are `T1`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 4 — the tightness lemma for
  transference plans that precedes the existence theorem for an optimal coupling.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Springer 2015, Chapter 1 — the
  same compactness argument, run through Prokhorov's theorem.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Closed

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)]

/-- **The couplings of two probability measures are weakly closed.** The coupling set is the
intersection of the preimages of `{μ}` and `{ν}` under the two marginal maps, both of which are
continuous for the topology of convergence in distribution. The `T1Space` hypotheses are what make
the two singletons closed. They hold for Borel factors with `HasOuterApproxClosed`, in particular
for pseudometrizable Borel factors, by `MeasureTheory.ProbabilityMeasure.t2Space`. The factors and
their product need only measurable opens for the marginal maps to be continuous. -/
theorem isClosed_setOfPred_isCoupling [T1Space (ProbabilityMeasure X)]
    [T1Space (ProbabilityMeasure Y)] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsClosed {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  simpa only [preimage, mem_singleton_iff, ← ofPred_and, ← isCoupling_toMeasure_iff] using
    (isClosed_singleton.preimage
      (ProbabilityMeasure.continuous_map_of_measurable continuous_fst measurable_fst)).inter
      (isClosed_singleton.preimage
        (ProbabilityMeasure.continuous_map_of_measurable continuous_snd measurable_snd))

end Closed

section Tight

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- **The couplings of two tight families of measures form a tight family.** A coupling gives the
complement of a compact rectangle at most the mass its two marginals give the complements of the
two sides, and those bounds are uniform over the two families because a coupling is exhausted by
its marginals. No hypothesis beyond the two topologies is needed. The marginals are allowed to
range over sets rather than to be fixed, which is what a stability argument with moving marginals
consumes. -/
theorem isTightMeasureSet_setOfPred_exists_isCoupling {S : Set (Measure X)} {T : Set (Measure Y)}
    (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet {π : Measure (X × Y) | ∃ μ ∈ S, ∃ ν ∈ T, IsCoupling π μ ν} := by
  refine IsTightMeasureSet.prodMk (hS.subset ?_) (hT.subset ?_)
  · rintro - ⟨π, ⟨μ, hμ, ν, -, hπ⟩, rfl⟩
    rwa [hπ.fst_eq]
  · rintro - ⟨π, ⟨μ, -, ν, hν, hπ⟩, rfl⟩
    rwa [hπ.snd_eq]

/-- **The couplings of two tight measures form a tight family.** This is the fixed-marginal case of
`TauCeti.isTightMeasureSet_setOfPred_exists_isCoupling`, and it is the tightness that Prokhorov's
theorem is applied to below. -/
theorem isTightMeasureSet_setOfPred_isCoupling (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) :
    IsTightMeasureSet {π : Measure (X × Y) | IsCoupling π μ ν} :=
  (isTightMeasureSet_setOfPred_exists_isCoupling hμ hν).subset fun _ hπ ↦ ⟨μ, rfl, ν, rfl, hπ⟩

end Tight

section AbstractCompact

/-! The abstract theorem exposes exactly the Prokhorov property used by the coupling argument:
every tight family of probability measures on the product has compact closure. -/

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T1Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [T1Space (ProbabilityMeasure Y)]
  [OpensMeasurableSpace (X × Y)]

/-- **Compactness of couplings under an abstract Prokhorov property.** If every tight family of
probability measures on the product has compact closure, then the couplings of two tight marginals
form a compact set. This keeps the compactness argument available beyond the concrete Hausdorff
Borel version of Prokhorov's theorem without inferring the property from Radon regularity. -/
theorem isCompact_setOfPred_isCoupling_of_prokhorov
    (hprokhorov : ∀ S : Set (ProbabilityMeasure (X × Y)),
      IsTightMeasureSet {((π : ProbabilityMeasure (X × Y)).toMeasure) | π ∈ S} →
        IsCompact (closure S))
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : IsTightMeasureSet {μ.toMeasure}) (hν : IsTightMeasureSet {ν.toMeasure}) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  have hclosed := isClosed_setOfPred_isCoupling μ ν
  have htight : IsTightMeasureSet {(π : ProbabilityMeasure (X × Y)).toMeasure |
      π ∈ {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure}} := by
    refine (isTightMeasureSet_setOfPred_isCoupling hμ hν).subset ?_
    rintro - ⟨π, hπ, rfl⟩
    exact hπ
  simpa only [hclosed.closure_eq] using hprokhorov _ htight

end AbstractCompact

section Compact

/-! Prokhorov's theorem asks the product to be Hausdorff and Borel. Assuming `BorelSpace` for the
product directly avoids imposing second countability on either factor. Closedness additionally
asks that the two spaces of probability measures be `T1`; these hypotheses do not choose a metric
on either factor. -/

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [T1Space (ProbabilityMeasure X)]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [T1Space (ProbabilityMeasure Y)] [BorelSpace (X × Y)]

/-- **The couplings of two tight probability measures are weakly compact.** The set is tight by
`TauCeti.isTightMeasureSet_setOfPred_isCoupling`, hence relatively compact by Prokhorov's theorem,
and it is closed by `TauCeti.isClosed_setOfPred_isCoupling`; so it equals its own closure and is
compact. Hausdorffness is required only of the product. -/
theorem isCompact_setOfPred_isCoupling [T2Space (X × Y)]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : IsTightMeasureSet {μ.toMeasure}) (hν : IsTightMeasureSet {ν.toMeasure}) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isCompact_setOfPred_isCoupling_of_prokhorov
    (fun _ ↦ isCompact_closure_of_isTightMeasureSet) hμ hν

/-- The bundled couplings of two inner-regular probability measures form a compact space for weak
convergence when both factors are Hausdorff with measurable opens, their product is a Borel space,
and both spaces of marginal probability measures are `T1`. This applies in particular to
probability measures on Polish Borel spaces. -/
instance Coupling.instCompactSpace [T2Space X] [T2Space Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    [μ.toMeasure.InnerRegular] [ν.toMeasure.InnerRegular] : CompactSpace (Coupling μ ν) :=
  isCompact_iff_compactSpace.mp (isCompact_setOfPred_isCoupling
    isTightMeasureSet_singleton_of_innerRegular isTightMeasureSet_singleton_of_innerRegular)

end Compact

section MovingMarginals

/-! Weak limits of plans whose marginals move. The hypotheses are those of the two sections above,
strengthened from `T1` to `T2` on the two spaces of marginals because a limit is identified here,
not merely trapped in a closed set. Passing to limits needs only measurable opens on the factors
and product; extracting a convergent refinement additionally needs a Hausdorff Borel product. -/

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [T2Space (ProbabilityMeasure Y)]
  [OpensMeasurableSpace (X × Y)] {l : Filter ι}
  {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}
  {π : ProbabilityMeasure (X × Y)}

/-- **The coupling constraint passes to weak limits.** If the plans `πs i` are eventually couplings
of `μs i` and `νs i`, and the plans and both marginals converge weakly along the same filter,
then the limiting plan is a coupling of the limiting marginals.
The two marginal maps are weakly continuous, so this is uniqueness of weak limits applied to the
two marginals of `πs`. -/
theorem isCoupling_of_tendsto [l.NeBot]
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l (𝓝 π)) (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  refine isCoupling_toMeasure_iff.mpr ⟨?_, ?_⟩
  · have h₁ : Tendsto (fun i ↦ (πs i).map Prod.fst) l
        (𝓝 (π.map Prod.fst)) :=
      (ProbabilityMeasure.continuous_map_of_measurable continuous_fst measurable_fst).tendsto π
        |>.comp hπ
    refine tendsto_nhds_unique h₁ (hμ.congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).1.symm
  · have h₂ : Tendsto (fun i ↦ (πs i).map Prod.snd) l
        (𝓝 (π.map Prod.snd)) :=
      (ProbabilityMeasure.continuous_map_of_measurable continuous_snd measurable_snd).tendsto π
        |>.comp hπ
    refine tendsto_nhds_unique h₂ (hν.congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).2.symm

/-- **Relative compactness of a family of transport plans with moving marginals.** If a tail of
each marginal family is tight, then any eventually feasible family of plans has a weakly convergent
refinement whose limit is a coupling of the limiting marginals. Prokhorov's theorem needs
Hausdorffness and the Borel sigma algebra only on the product; no second-countability hypothesis
on either factor is required. -/
theorem exists_isCoupling_tendsto_of_isTightMeasureSet [T2Space (X × Y)]
    [BorelSpace (X × Y)]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) [l.NeBot]
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l'' : Filter ι) (π : ProbabilityMeasure (X × Y)), l''.NeBot ∧ l'' ≤ l ∧
      Tendsto πs l'' (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨s, hs, hμs⟩ := hμt
  obtain ⟨t, ht, hνt⟩ := hνt
  set S : Set (ProbabilityMeasure (X × Y)) :=
    {σ | ∃ i ∈ s ∩ t, IsCoupling σ.toMeasure (μs i).toMeasure (νs i).toMeasure}
  have htight : IsTightMeasureSet {(σ : ProbabilityMeasure (X × Y)).toMeasure | σ ∈ S} := by
    refine (isTightMeasureSet_setOfPred_exists_isCoupling hμs hνt).subset ?_
    rintro - ⟨σ, ⟨i, hi, hσ⟩, rfl⟩
    exact ⟨(μs i).toMeasure, ⟨i, hi.1, rfl⟩, (νs i).toMeasure, ⟨i, hi.2, rfl⟩, hσ⟩
  have hcompact : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  have hmem : ∀ᶠ i in l, πs i ∈ closure S := by
    filter_upwards [hπs, inter_mem hs ht] with i hi hit
    have hiS : πs i ∈ S := ⟨i, hit, hi⟩
    exact subset_closure hiS
  obtain ⟨π, -, hπ⟩ := hcompact.exists_mapClusterPt_of_frequently
    hmem.frequently
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hπ
  exact ⟨U, π, U.neBot, hUle, hUtend, isCoupling_of_tendsto
    (hπs.filter_mono hUle) hUtend (hμ.mono_left hUle) (hν.mono_left hUle)⟩

end MovingMarginals

section CompactMetrizable

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.MetrizableSpace Y] in
/-- **Closedness of couplings on compact pseudometrizable spaces.** This is the directly usable
compact-pseudometrizable specialisation of `TauCeti.isClosed_setOfPred_isCoupling`. -/
theorem isClosed_setOfPred_isCoupling_of_compactSpace
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.PseudoMetrizableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsClosed
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  let : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  let : UniformSpace Y := TopologicalSpace.pseudoMetrizableSpaceUniformity Y
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  let : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  exact isClosed_setOfPred_isCoupling μ ν

/-- **Compactness of couplings on compact metrizable spaces.** Compactness makes every family of
measures tight, so the general coupling compactness theorem applies without marginal hypotheses. -/
theorem isCompact_setOfPred_isCoupling_of_compactSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  let : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  let : UniformSpace Y := TopologicalSpace.pseudoMetrizableSpaceUniformity Y
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  let : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  exact isCompact_setOfPred_isCoupling IsTightMeasureSet.of_compactSpace
    IsTightMeasureSet.of_compactSpace

end CompactMetrizable

section Polish

/-! The Polish specialisation is stated for Mathlib's `PolishSpace`, the topological notion: second
countable and completely metrizable, with no distance chosen. That is what makes the two factors
tight and hence the coupling set compact. -/

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Closedness of couplings on Polish Borel spaces.** This is the canonical weak/Borel
specialisation: the probability-measure spaces are Hausdorff, so the two marginal fibers are
closed. -/
theorem isClosed_setOfPred_isCoupling_of_polishSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsClosed
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isClosed_setOfPred_isCoupling μ ν

/-- **The couplings of two probability measures on Polish spaces are weakly compact.** On a Polish
space every finite Borel measure is tight, so the tightness hypotheses of
`TauCeti.isCompact_setOfPred_isCoupling` are automatic. This is the compactness that the direct
method of the calculus of variations consumes. -/
theorem isCompact_setOfPred_isCoupling_of_polishSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isCompact_setOfPred_isCoupling isTightMeasureSet_singleton isTightMeasureSet_singleton

end Polish

end TauCeti
