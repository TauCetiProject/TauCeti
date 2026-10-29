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
At the measurable root, the criterion needs only an optimal coupling and a weak extended metric
target, with no topology on the carriers, finiteness, or measurability assumptions on the kernels.

At every exponent, weak isomorphisms preserve distance to a third measured kernel.
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
the measures need not be finite and the kernels need not be measurable. The target's topology
need not be induced by its extended distance. -/
theorem gromovWassersteinEDist_eq_zero_iff_of_exists_optimal_coupling [TopologicalSpace Z]
    [WeakEMetricSpace Z]
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

private theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_le_of_exists_glue
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglue : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p μ ωX ρ ωW ≤ gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  refine le_gromovWassersteinEDist fun σ hσ ↦ ?_
  obtain ⟨γ, hγπ, hγσ⟩ := hglue π σ hπ hσ
  have hleft : MeasurePreserving (Prod.map id Prod.fst) γ π :=
    ⟨measurable_id.prodMap measurable_fst, hγπ⟩
  have hright : MeasurePreserving Prod.snd γ σ := ⟨measurable_snd, hγσ⟩
  have : SigmaFinite γ := hleft.sigmaFinite
  -- The three coordinate projections are parametrizations of the marginals. Read the
  -- second plan through its paired projections to use the common-parametrization API.
  have hX : MeasurePreserving (fun w : X × Y × W ↦ w.1) γ μ :=
    hπ.measurePreserving_fst.comp hleft
  have hY : MeasurePreserving (fun w : X × Y × W ↦ w.2.1) γ ν :=
    hσ.measurePreserving_fst.comp hright
  have hW : MeasurePreserving (fun w : X × Y × W ↦ w.2.2) γ ρ :=
    hσ.measurePreserving_snd.comp hright
  have heq' := (hleft.prod hleft).quasiMeasurePreserving.ae_eq_comp heq
  have hσγ : σ = γ.map fun w ↦ (w.2.1, w.2.2) := by
    rw [← hγσ, Measure.snd]
  rw [hσγ, gromovWassersteinDistortion_map_prodMk hY hW hωY hωW]
  refine (gromovWassersteinEDist_le_eLpNorm hX hW hωX hωW p).trans_eq
    (eLpNorm_congr_ae ?_)
  filter_upwards [heq'] with q hq
  exact congrArg (fun z ↦ edist z (ωW (q.1.2.2, q.2.2.2))) hq

/-- Replacing the first measured kernel by a weakly isomorphic one preserves its distance to
a third measured kernel whenever couplings glue in both orders of the isomorphic carriers.
This holds at every exponent. No standard Borel structure is required, and the comparison
measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_left_of_exists_glue
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglueXYW : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ)
    (hglueYXW : ∀ π σ, IsCoupling π ν μ → IsCoupling σ μ ρ →
      ∃ γ : Measure (Y × X × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p μ ωX ρ ωW = gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  exact le_antisymm (h.gromovWassersteinEDist_le_of_exists_glue hωX hωY hωW hglueXYW)
    (h.symm.gromovWassersteinEDist_le_of_exists_glue hωY hωX hωW hglueYXW)

/-- Replacing the second measured kernel by a weakly isomorphic one preserves its distance
from a third measured kernel whenever couplings glue in both orders of the isomorphic carriers,
with the comparison carrier last. This holds at every exponent, and the comparison measure
need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_right_of_exists_glue
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglueXYW : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ)
    (hglueYXW : ∀ π σ, IsCoupling π ν μ → IsCoupling σ μ ρ →
      ∃ γ : Measure (Y × X × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p ρ ωW μ ωX = gromovWassersteinEDist p ρ ωW ν ωY := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  rw [← gromovWassersteinEDist_comm p μ ωX ρ ωW,
    ← gromovWassersteinEDist_comm p ν ωY ρ ωW]
  exact h.gromovWassersteinEDist_congr_left_of_exists_glue hωX hωY hωW hglueXYW hglueYXW

/-- Replacing the first measured kernel by a weakly isomorphic one preserves its distance to
a standard Borel measured kernel at every exponent. The comparison measure need not be finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_left [StandardBorelSpace W]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) :
    gromovWassersteinEDist p μ ωX ρ ωW = gromovWassersteinEDist p ν ωY ρ ωW := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  exact h.gromovWassersteinEDist_congr_left_of_exists_glue hωX hωY hωW
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))
    (fun π σ hπ hσ ↦
      have : IsFiniteMeasure σ := hσ.isFiniteMeasure
      Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm))

/-- Replacing the second measured kernel by a weakly isomorphic one preserves its distance
from a standard Borel measured kernel at every exponent. The comparison measure need not be
finite. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_right [StandardBorelSpace W]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) :
    gromovWassersteinEDist p ρ ωW μ ωX = gromovWassersteinEDist p ρ ωW ν ωY := by
  obtain ⟨π, hπ, -⟩ := h.exists_isCoupling
  have : IsFiniteMeasure ν := ⟨hπ.measure_univ_eq ▸ measure_lt_top μ _⟩
  rw [← gromovWassersteinEDist_comm p μ ωX ρ ωW,
    ← gromovWassersteinEDist_comm p ν ωY ρ ωW]
  exact h.gromovWassersteinEDist_congr_left hωX hωY hωW

end Invariance

end TauCeti
