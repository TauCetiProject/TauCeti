/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Attainment
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.WeakIsomorphism

/-!
# Zero Gromov–Wasserstein distance and presentation invariance

For probability measures on standard Borel carriers and a.e. strongly measurable kernels into an
extended metric space, zero Gromov–Wasserstein distance is equivalent to weak isomorphism. This
holds at every nonzero exponent, including infinity, without moment bounds or separability of
the target. More generally, tight Borel probability measures on second-countable metrizable
carriers suffice. A compatible Polish topology on each standard Borel carrier recovers the
standard Borel result from this tight-measure criterion.
At the measurable root, the criterion needs only an optimal coupling, with no topology,
finiteness, or measurability assumptions on the kernels.

For exponents at least one, weak isomorphisms preserve distance to a third measured kernel.
These invariance statements need only an extended pseudometric target and finite measures on
the two isomorphic carriers, assuming couplings glue in both orders. A standard Borel comparison
carrier supplies these gluings. Together with
the zero-distance characterization, they supply the separation and representative-independence
needed to put Gromov–Wasserstein distance on weak-isomorphism classes. No equality of the raw
presentations is asserted.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Definition 28 and the weak-isomorphism characterization
  underlying the metric on its classes. Here the target may be extended metric, and the distance
  has no factor of one half.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X Y W Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure W}
  {ωX : X × X → Z} {ωY : Y × Y → Z} {ωW : W × W → Z} {p : ℝ≥0∞}

/-- When an optimal coupling exists, zero Gromov–Wasserstein distance is exactly weak
isomorphism at every nonzero exponent. The carriers need only measurable structures;
the measures need not be finite and the kernels need not be measurable. -/
theorem gromovWassersteinEDist_eq_zero_iff_of_exists_optimal_coupling [EMetricSpace Z]
    (hopt : ∃ π, IsCoupling π μ ν ∧
      gromovWassersteinDistortion p ωX ωY π = gromovWassersteinEDist p μ ωX ν ωY)
    (hp : p ≠ 0) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 ↔ AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  constructor
  · intro hzero
    obtain ⟨π, hπ, hdist⟩ := hopt
    exact (areWeaklyIsomorphicKernels_iff_exists_distortion_eq_zero hp).mpr
      ⟨π, hπ, hdist.trans hzero⟩
  · intro h
    exact h.gromovWassersteinEDist_eq_zero edist_self p

/-- For a.e. strongly measurable kernels with tight Borel probability measures on
second-countable metrizable spaces, zero Gromov–Wasserstein distance is exactly weak isomorphism
at every nonzero exponent. The target needs neither a measurable structure nor separability,
completeness, or finite moments. -/
theorem gromovWassersteinEDist_eq_zero_iff_of_isTightMeasureSet [EMetricSpace Z]
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [BorelSpace X] [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [SecondCountableTopology Y] [BorelSpace Y]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsTightMeasureSet {μ}) (hν : IsTightMeasureSet {ν})
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (hp : p ≠ 0) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 ↔ AreWeaklyIsomorphicKernels μ ωX ν ωY :=
  gromovWassersteinEDist_eq_zero_iff_of_exists_optimal_coupling
    (exists_isCoupling_gromovWassersteinDistortion_eq_of_isTightMeasureSet hμ hν hωX hωY p) hp

/-- For a.e. strongly measurable kernels on standard Borel probability spaces, zero
Gromov–Wasserstein distance is exactly weak isomorphism, at every nonzero exponent. The target
needs neither a measurable structure nor separability, completeness, or finite moments. -/
theorem gromovWassersteinEDist_eq_zero_iff [EMetricSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (hp : p ≠ 0) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 ↔ AreWeaklyIsomorphicKernels μ ωX ν ωY :=
  gromovWassersteinEDist_eq_zero_iff_of_exists_optimal_coupling
    (exists_isCoupling_gromovWassersteinDistortion_eq_of_standardBorelSpace μ ν hωX hωY p) hp

section Invariance

variable [PseudoEMetricSpace Z] [IsFiniteMeasure μ]

/-- Replacing the first measured kernel by a weakly isomorphic one preserves its distance to
a third measured kernel whenever couplings glue in both orders of the isomorphic carriers.
No standard Borel structure is required, and the comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_left_of_exists_glue
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p)
    (hglueXYW : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ)
    (hglueYXW : ∀ π σ, IsCoupling π ν μ → IsCoupling σ μ ρ →
      ∃ γ : Measure (Y × X × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p μ ωX ρ ωW = gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  apply le_antisymm
  · simpa only [h.gromovWassersteinEDist_eq_zero edist_self p, zero_add] using
      (gromovWassersteinEDist_triangle_of_exists_glue hp hωX hωY hωW hglueXYW)
  · simpa only [h.symm.gromovWassersteinEDist_eq_zero edist_self p, zero_add] using
      (gromovWassersteinEDist_triangle_of_exists_glue hp hωY hωX hωW hglueYXW)

/-- Replacing the second measured kernel by a weakly isomorphic one preserves its distance
from a third measured kernel whenever couplings glue in both orders of the isomorphic carriers,
with the comparison carrier last. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_right_of_exists_glue
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p)
    (hglueXYW : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ)
    (hglueYXW : ∀ π σ, IsCoupling π ν μ → IsCoupling σ μ ρ →
      ∃ γ : Measure (Y × X × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p ρ ωW μ ωX = gromovWassersteinEDist p ρ ωW ν ωY := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  rw [← gromovWassersteinEDist_comm p μ ωX ρ ωW,
    ← gromovWassersteinEDist_comm p ν ωY ρ ωW]
  exact h.gromovWassersteinEDist_congr_left_of_exists_glue hωX hωY hωW hp hglueXYW hglueYXW

/-- Replacing the first measured kernel by a weakly isomorphic one preserves its distance to
a standard Borel measured kernel. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_left [StandardBorelSpace W]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p) :
    gromovWassersteinEDist p μ ωX ρ ωW = gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  exact h.gromovWassersteinEDist_congr_left_of_exists_glue hωX hωY hωW hp
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))

/-- Replacing the second measured kernel by a weakly isomorphic one preserves its distance
from a standard Borel measured kernel. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_right [StandardBorelSpace W]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p) :
    gromovWassersteinEDist p ρ ωW μ ωX = gromovWassersteinEDist p ρ ωW ν ωY := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  exact h.gromovWassersteinEDist_congr_right_of_exists_glue hωX hωY hωW hp
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))

end Invariance

end TauCeti
