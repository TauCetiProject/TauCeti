/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Zero

/-!
# The metric space of measured kernels

`GromovWassersteinPresentation p Z` bundles a standard Borel probability carrier and an
almost-everywhere strongly measurable `Z`-valued kernel with finite `p`-size. This is the
finite-distance category, not a replacement for the unrestricted raw-measure definitions in
`GromovWasserstein.Basic`. The exponent is a parameter, and the moment condition existentially
quantifies its basepoint, so no chosen basepoint is part of a presentation.

For `1 ≤ p`, presentations carry the Gromov–Wasserstein pseudometric.
`GromovWassersteinSpace p Z` uses Mathlib's `SeparationQuotient` of this pseudometric.
Two presentations have the same class exactly when their kernels are weakly isomorphic,
not when their carriers or kernels are equal.
The quotient has a genuine metric, with the original coupling formula as its extended distance.
This includes `p = ∞`, where finite size means essential boundedness.

One-point kernels give an isometric embedding of `Z` into this space. Comparing with these
kernels proves finiteness of all distances without requiring a globally separable or complete
target. Carrier universes are fixed independently of the target universe.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Definition 28 and the metric on weak-isomorphism classes.
  The distance here uses the full distortion, without their factor of one half.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

/-- A finite-`p` measured-kernel presentation on a standard Borel probability carrier.
The target needs no separability or completeness. Presentations themselves are not identified
under null changes or measure-preserving parametrizations; `GromovWassersteinSpace` makes
exactly those identifications. -/
structure GromovWassersteinPresentation (p : ℝ≥0∞) (Z : Type v) [MetricSpace Z] where
  /-- The measurable carrier of the kernel. -/
  Carrier : Type u
  /-- The sigma-algebra on the carrier. -/
  [measurableSpace : MeasurableSpace Carrier]
  /-- Standard Borel structure supplies coupling gluing and attainment. -/
  [standardBorelSpace : StandardBorelSpace Carrier]
  /-- The probability law on the carrier. -/
  measure : Measure Carrier
  /-- The carrier law has total mass one. -/
  [isProbabilityMeasure : IsProbabilityMeasure measure]
  /-- The target-valued kernel, with no symmetry assumption. -/
  kernel : Carrier × Carrier → Z
  /-- Strong measurability is needed only almost everywhere on the square. -/
  aestronglyMeasurable_kernel : AEStronglyMeasurable kernel (measure.prod measure)
  /-- Finite size about some target point, including essential boundedness at infinity. -/
  finite_moment : ∃ z : Z, MemLp (fun q ↦ edist (kernel q) z) p (measure.prod measure)

attribute [instance] GromovWassersteinPresentation.measurableSpace
  GromovWassersteinPresentation.standardBorelSpace
  GromovWassersteinPresentation.isProbabilityMeasure

namespace GromovWassersteinPresentation

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z]

/-- The one-point presentation with constant kernel value `z`. -/
-- Implicit reduction lets the projected carrier and measurable structure elaborate together.
@[implicit_reducible]
def point (z : Z) : GromovWassersteinPresentation.{u} p Z where
  Carrier := ULift.{u} Unit
  measure := Measure.dirac ⟨()⟩
  kernel := fun _ ↦ z
  aestronglyMeasurable_kernel := aestronglyMeasurable_const
  finite_moment := ⟨z, by simp⟩

/-- Distance to the constant one-point kernel is exactly the size about that point. -/
@[simp]
theorem gromovWassersteinEDist_point (K : GromovWassersteinPresentation.{u} p Z) (z : Z) :
    gromovWassersteinEDist p K.measure K.kernel (point (p := p) z).measure
      (point (p := p) z).kernel =
      eLpNorm (fun q ↦ edist (K.kernel q) z) p (K.measure.prod K.measure) :=
  gromovWassersteinEDist_dirac_right (ULift.up ()) (fun _ ↦ z)
    K.aestronglyMeasurable_kernel p

/-- Between constant one-point kernels, GW recovers the target metric at nonzero exponents. -/
theorem gromovWassersteinEDist_point_point (hp : p ≠ 0) (z w : Z) :
    gromovWassersteinEDist p (point (p := p) z).measure (point (p := p) z).kernel
      (point (p := p) w).measure (point (p := p) w).kernel = edist z w := by
  rw [gromovWassersteinEDist_point]
  simp only [point]
  rw [eLpNorm_const (edist z w) hp (IsProbabilityMeasure.ne_zero _)]
  simp

/-- Finite size at possibly different basepoints suffices for finite GW distance. -/
theorem gromovWassersteinEDist_ne_top (hp : 1 ≤ p)
    (K L : GromovWassersteinPresentation.{u} p Z) :
    gromovWassersteinEDist p K.measure K.kernel L.measure L.kernel ≠ ∞ := by
  obtain ⟨z, hz⟩ := K.finite_moment
  obtain ⟨w, hw⟩ := L.finite_moment
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hzw := gromovWassersteinEDist_triangle (μ := (point.{u} (p := p) z).measure)
    (ν := (point.{u} (p := p) w).measure) (ρ := L.measure)
    hp (point.{u} z).aestronglyMeasurable_kernel (point.{u} w).aestronglyMeasurable_kernel
    L.aestronglyMeasurable_kernel
  rw [gromovWassersteinEDist_point_point hp₀,
    gromovWassersteinEDist_comm p (point.{u} w).measure (point.{u} w).kernel,
    gromovWassersteinEDist_point] at hzw
  have hzL : gromovWassersteinEDist p (point.{u} z).measure (point.{u} z).kernel
      L.measure L.kernel ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨edist_ne_top z w, hw.eLpNorm_ne_top⟩) hzw
  have hKL := gromovWassersteinEDist_triangle (μ := K.measure)
    (ν := (point.{u} (p := p) z).measure) (ρ := L.measure)
    hp K.aestronglyMeasurable_kernel (point.{u} z).aestronglyMeasurable_kernel
    L.aestronglyMeasurable_kernel
  rw [gromovWassersteinEDist_point] at hKL
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz.eLpNorm_ne_top, hzL⟩) hKL

/-- The GW pseudometric on finite-size standard Borel presentations. Distinct presentations
may have distance zero; only the subsequent quotient is a metric space. -/
instance instPseudoMetricSpace [Fact (1 ≤ p)] :
    PseudoMetricSpace (GromovWassersteinPresentation.{u} p Z) := by
  letI : PseudoEMetricSpace (GromovWassersteinPresentation.{u} p Z) :=
    PseudoEMetricSpace.ofEDist
      (fun K L ↦ gromovWassersteinEDist p K.measure K.kernel L.measure L.kernel)
      (fun K ↦ gromovWassersteinEDist_self K.aestronglyMeasurable_kernel p)
      (fun K L ↦ gromovWassersteinEDist_comm p K.measure K.kernel L.measure L.kernel)
      (fun K L M ↦ gromovWassersteinEDist_triangle Fact.out
        K.aestronglyMeasurable_kernel L.aestronglyMeasurable_kernel
        M.aestronglyMeasurable_kernel)
  exact PseudoEMetricSpace.toPseudoMetricSpace (fun K L ↦
    gromovWassersteinEDist_ne_top Fact.out K L)

/-- The pseudometric on presentations is the original infimum over couplings. -/
@[simp]
theorem edist_eq [Fact (1 ≤ p)] (K L : GromovWassersteinPresentation.{u} p Z) :
    edist K L = gromovWassersteinEDist p K.measure K.kernel L.measure L.kernel := (rfl)

end GromovWassersteinPresentation

/-- Finite-size standard Borel measured kernels modulo weak isomorphism, with the full
Gromov–Wasserstein metric. The carrier universe is fixed, but is independent of the target. -/
def GromovWassersteinSpace (p : ℝ≥0∞) (Z : Type v) [MetricSpace Z] [Fact (1 ≤ p)] :=
  SeparationQuotient (GromovWassersteinPresentation.{u} p Z)

namespace GromovWassersteinSpace

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- The separation quotient of the presentation pseudometric is a genuine metric space. -/
instance instMetricSpace : MetricSpace (GromovWassersteinSpace.{u} p Z) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (GromovWassersteinPresentation.{u} p Z)))

/-- Pass from a presentation to its weak-isomorphism class. -/
def mk (K : GromovWassersteinPresentation.{u} p Z) : GromovWassersteinSpace.{u} p Z :=
  SeparationQuotient.mk K

/-- Every GW class has a presentation in the fixed carrier universe. -/
theorem mk_surjective : Function.Surjective (mk.{u} (p := p) (Z := Z)) :=
  SeparationQuotient.surjective_mk

/-- The quotient extended distance is exactly the raw GW coupling infimum. -/
@[simp]
theorem edist_mk (K L : GromovWassersteinPresentation.{u} p Z) :
    edist (mk K) (mk L) = gromovWassersteinEDist p K.measure K.kernel L.measure L.kernel :=
  SeparationQuotient.edist_mk K L

/-- The real metric is the finite raw GW value read in `ℝ`. -/
@[simp]
theorem dist_mk (K L : GromovWassersteinPresentation.{u} p Z) :
    dist (mk K) (mk L) =
      (gromovWassersteinEDist p K.measure K.kernel L.measure L.kernel).toReal := by
  rw [dist_edist, edist_mk]

/-- Equality of classes is precisely weak isomorphism, witnessed by an exact coupling.
It does not assert equality of presentations, even after null modifications. -/
@[simp]
theorem mk_eq_mk_iff (K L : GromovWassersteinPresentation.{u} p Z) :
    mk K = mk L ↔ AreWeaklyIsomorphicKernels K.measure K.kernel L.measure L.kernel := by
  rw [← edist_eq_zero, edist_mk]
  exact gromovWassersteinEDist_eq_zero_iff K.aestronglyMeasurable_kernel
    L.aestronglyMeasurable_kernel (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))

/-- Descend any weak-isomorphism-invariant function on presentations to GW classes. -/
def lift {β : Type*} (f : GromovWassersteinPresentation.{u} p Z → β)
    (hf : ∀ K L, AreWeaklyIsomorphicKernels K.measure K.kernel L.measure L.kernel →
      f K = f L) : GromovWassersteinSpace.{u} p Z → β :=
  SeparationQuotient.lift f fun K L h ↦
    hf K L ((mk_eq_mk_iff K L).mp (SeparationQuotient.mk_eq_mk.mpr h))

/-- A descended function takes its prescribed value on every presentation. -/
@[simp]
theorem lift_mk {β : Type*} (f : GromovWassersteinPresentation.{u} p Z → β)
    (hf : ∀ K L, AreWeaklyIsomorphicKernels K.measure K.kernel L.measure L.kernel →
      f K = f L) (K : GromovWassersteinPresentation.{u} p Z) : lift f hf (mk K) = f K := (rfl)

/-- The class of the one-point kernel with value `z`. -/
def point (z : Z) : GromovWassersteinSpace.{u} p Z :=
  mk (GromovWassersteinPresentation.point z)

/-- Distance from a presented kernel to a one-point class is its size about that point. -/
@[simp]
theorem edist_mk_point (K : GromovWassersteinPresentation.{u} p Z) (z : Z) :
    edist (mk K) (point z) =
      eLpNorm (fun q ↦ edist (K.kernel q) z) p (K.measure.prod K.measure) := by
  rw [point, edist_mk, GromovWassersteinPresentation.gromovWassersteinEDist_point]

/-- A measured-kernel presentation is the one-point class at `z` exactly when its kernel
is almost everywhere equal to `z`. -/
@[simp]
theorem mk_eq_point_iff {K : GromovWassersteinPresentation.{u} p Z} {z : Z} :
    mk K = point z ↔ K.kernel =ᵐ[K.measure.prod K.measure] fun _ ↦ z := by
  rw [← edist_eq_zero, edist_mk_point, eLpNorm_eq_zero_iff
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))]
  simp only [Filter.EventuallyEq, Pi.zero_apply, edist_eq_zero]

/-- One-point classes recover the ground extended distance, without a normalization factor. -/
@[simp]
theorem edist_point (z w : Z) : edist (point (p := p) z) (point (p := p) w) = edist z w := by
  rw [point, point, edist_mk]
  exact GromovWassersteinPresentation.gromovWassersteinEDist_point_point
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) z w

/-- The target embeds isometrically as constant one-point kernels in GW space. -/
theorem isometry_point : Isometry (point.{u} (p := p) (Z := Z)) :=
  fun z w ↦ edist_point z w

/-- The real distance of one-point classes is exactly their ground distance. -/
@[simp]
theorem dist_point (z w : Z) : dist (point (p := p) z) (point (p := p) w) = dist z w :=
  isometry_point.dist_eq z w

end GromovWassersteinSpace

end TauCeti
