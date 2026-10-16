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
the target. A compatible Polish topology on each carrier allows the optimal-coupling theorem to
supply the exact coupling witnessing weak isomorphism.

For exponents at least one, weak isomorphisms preserve distance to a third measured kernel.
These invariance statements need only an extended pseudometric target and finite measures on
the two isomorphic carriers; only the comparison carrier must be standard Borel. Together with
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

/-- For a.e. strongly measurable kernels on standard Borel probability spaces, zero
Gromov–Wasserstein distance is exactly weak isomorphism, at every nonzero exponent. The target
needs neither a measurable structure nor separability, completeness, or finite moments. -/
theorem gromovWassersteinEDist_eq_zero_iff [EMetricSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (hp : p ≠ 0) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 ↔ AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  constructor
  · intro hzero
    -- Attainment uses topology, but both its conclusion and the kernels use only measurable data.
    let := upgradeStandardBorel X
    let := upgradeStandardBorel Y
    obtain ⟨π, hπ, hdist⟩ := exists_isCoupling_gromovWassersteinDistortion_eq μ ν hωX hωY p
    exact (areWeaklyIsomorphicKernels_iff_exists_distortion_eq_zero hp).mpr
      ⟨π, hπ, hdist.trans hzero⟩
  · intro h
    exact h.gromovWassersteinEDist_eq_zero edist_self p

section Invariance

variable [PseudoEMetricSpace Z] [StandardBorelSpace W] [IsFiniteMeasure μ]

/-- Replacing the first measured kernel by a weakly isomorphic one preserves its distance to
a standard Borel measured kernel. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_eq_left
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p) :
    gromovWassersteinEDist p μ ωX ρ ωW = gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  apply le_antisymm
  · simpa only [h.gromovWassersteinEDist_eq_zero edist_self p, zero_add] using
      (gromovWassersteinEDist_triangle hp hωX hωY hωW)
  · simpa only [h.symm.gromovWassersteinEDist_eq_zero edist_self p, zero_add] using
      (gromovWassersteinEDist_triangle hp hωY hωX hωW)

/-- Replacing the second measured kernel by a weakly isomorphic one preserves its distance
from a standard Borel measured kernel. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_eq_right
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) (hp : 1 ≤ p) :
    gromovWassersteinEDist p ρ ωW μ ωX = gromovWassersteinEDist p ρ ωW ν ωY := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  rw [← gromovWassersteinEDist_comm p μ ωX ρ ωW,
    ← gromovWassersteinEDist_comm p ν ωY ρ ωW]
  exact h.gromovWassersteinEDist_eq_left hωX hωY hωW hp

end Invariance

end TauCeti
