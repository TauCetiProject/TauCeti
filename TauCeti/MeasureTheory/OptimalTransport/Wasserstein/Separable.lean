/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Separability of the finite-moment Wasserstein space

For a finite exponent `1 ≤ p < ∞` the Wasserstein space `TauCeti.WassersteinSpace p X` of laws of
finite `p`-moment is separable when the ground space is second countable and its measurable
structure is standard Borel and induced by the metric topology. The countable dense family is the
expected one: the laws carried by finitely many terms of a dense sequence of `X`, each term
receiving a rational share of the total mass. Concretely it is the range of a map defined on
`Finset (ℕ × ℕ)`, a pair `(i, k)` contributing the multiplicity `k` to the `i`-th term of the
sequence and the resulting weights being normalised to total mass `1`.

Three approximations take an arbitrary law to a member of that family, each costing a quarter of
the prescribed accuracy, and all three are supplied by the imported finite-support module: the
finite-support approximation `TauCeti.exists_ae_mem_finset_wassersteinEDist_le`, then
`TauCeti.exists_map_range_wassersteinEDist_le`, which pushes the resulting finitely supported law
onto terms of the dense sequence, and finally the rational-weight approximation
`TauCeti.exists_nat_weights_wassersteinEDist_le`.

The exponent must be finite. Finitely supported laws are not `W_∞`-dense on a general separable
metric space, and indeed `P_∞ (X)` need not be separable.

## Main statements

* `TauCeti.WassersteinSpace.separableSpace` — separability of `P_p (X)` for `1 ≤ p < ∞`, with
  `TauCeti.WassersteinSpace.instSeparableSpace` its instance form.
* `TauCeti.WassersteinComponent.separableSpace_of_hasFiniteMoment` — separability of the component
  anchored at a law with finite `p`-moment.

## Implementation notes

The imported approximation estimates take the measurability of the ground distance explicitly,
and the separability theorem reads it off the Borel structure. Finiteness of the exponent cannot
be an instance argument, so `TauCeti.WassersteinSpace.separableSpace` takes it explicitly and the
instance reads it off a `Fact`, exactly as the metric structure of `TauCeti.WassersteinSpace`
reads `1 ≤ p` off `Fact (1 ≤ p)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.18.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

namespace WassersteinSpace

section Separable

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **`P_p (X)` is separable.** For a finite exponent `1 ≤ p < ∞`, the finite-moment Wasserstein
space over a second-countable ground space whose measurable structure is standard Borel and
induced by the metric topology is separable: the laws carried by finitely many terms of a dense
sequence and giving each of them a rational share of the mass form a countable dense set. -/
theorem separableSpace (hp_top : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have := hX
    exact ⟨∅, Set.countable_empty, fun μ ↦ (isEmpty_of_isEmpty.false μ).elim⟩
  set u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  -- the countable family of laws with natural multiplicities on terms of the dense sequence
  set G : Finset (ℕ × ℕ) → Measure X := fun t ↦
    (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ • ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) with hG_def
  refine ⟨(fun μ : WassersteinSpace p X ↦ ((μ : ProbabilityMeasure X) : Measure X)) ⁻¹'
    Set.range G, (Set.countable_range G).preimage fun _ _ h ↦ toProbabilityMeasure_injective
      (ProbabilityMeasure.toMeasure_injective h), ?_⟩
  refine Metric.dense_iff.2 fun μ r hr ↦ ?_
  have hquarter : (0 : ℝ) < r / 4 := by linarith
  obtain ⟨S, m, hSu, hmpos, hle⟩ := exists_natWeights_wassersteinEDist_le hu Fact.out hp_top
    μ.hasFiniteMoment hquarter
  set ν₃ : Measure X := (∑ x ∈ S, (m x : ℝ≥0∞))⁻¹ •
    ∑ x ∈ S, (m x : ℝ≥0∞) • Measure.dirac x with hν₃_def
  have hprob₃ : IsProbabilityMeasure ν₃ := isProbabilityMeasure_natWeights hmpos
  obtain ⟨x₁, _⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hmpos
  have hmom₃ : HasFiniteMoment p ν₃ :=
    hasFiniteMoment_of_ae_mem_finset x₁ (mem_ae_iff.2 (S.natWeights_compl_eq_zero m))
  -- the approximating law belongs to the countable family
  have hrange : ν₃ ∈ Set.range G := by
    obtain ⟨t, ht⟩ := exists_finset_prod_natWeights_eq m hSu
    exact ⟨t, ht⟩
  have hcoe : ((mk (⟨ν₃, hprob₃⟩ : ProbabilityMeasure X) hmom₃ : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν₃, hprob₃⟩ := coe_mk _ _
  refine ⟨mk ⟨ν₃, hprob₃⟩ hmom₃, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, dist_def, hcoe]
    refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) hle) ?_
    linarith
  · rw [Set.mem_preimage, hcoe]
    exact hrange

/-- The separability of `P_p (X)` as an instance, reading the finiteness of the exponent off a
`Fact`, as the metric structure reads off `Fact (1 ≤ p)`. -/
instance instSeparableSpace [Fact (p ≠ ∞)] :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) :=
  separableSpace Fact.out

end Separable

end WassersteinSpace

namespace WassersteinComponent

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- For a finite exponent `1 ≤ p < ∞`, the finite-distance component of an anchor law of finite
`p`-moment is separable, being isometric to the separable space `P_p (X)`. -/
theorem separableSpace_of_hasFiniteMoment (hp : p ≠ ∞) (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    TopologicalSpace.SeparableSpace (WassersteinComponent p μ₀) :=
  have := WassersteinSpace.separableSpace (X := X) hp
  let e := WassersteinSpace.isometryEquivComponentOfFiniteMoment hμ₀
  e.surjective.denseRange.separableSpace e.continuous

end WassersteinComponent

end TauCeti
