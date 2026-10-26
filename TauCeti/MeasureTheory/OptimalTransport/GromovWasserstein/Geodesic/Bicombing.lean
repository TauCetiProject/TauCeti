/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Geodesic.Basic

/-!
# Gromov–Wasserstein geodesics from bicombings

A supplied geodesic bicombing gives geodesics between measured kernels by interpolating their
values over an optimal coupling. On a separable metric target, Borel measurability of each time
slice suffices; neither completeness of the target nor continuity in the endpoints is needed.
The exponent may be any `1 ≤ p ≤ ∞`.

For a possibly nonseparable metric target, the continuous-bicombing theorem instead preserves
the separable essential ranges of the endpoint kernels. In particular, affine interpolation
makes the GW space over any real normed space geodesic.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 45. The distance here uses the full distortion,
  without their factor of one half.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.GromovWassersteinSpace

universe u v

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- **Geodesics from a Borel bicombing.** On a separable metric target, a geodesic bicombing
whose time slices are Borel measurable makes the measured-kernel GW quotient geodesic for
every `1 ≤ p ≤ ∞`. The target need not be complete, and the bicombing need not depend
continuously on its endpoints. -/
theorem isGeodesicSpace_of_measurable_bicombing [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] (β : Z → Z → ℝ → Z)
    (hβ : ∀ a b, IsGeodesicSegment (β a b) a b)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, Measurable fun ab : Z × Z ↦ β ab.1 ab.2 t) :
    IsGeodesicSpace (GromovWassersteinSpace.{u} p Z) :=
  isGeodesicSpace_of_ae_isGeodesicSegment fun K L π hπ ↦ by
    have : IsFiniteMeasure π := hπ.isFiniteMeasure
    refine ⟨fun q ↦ β (K.kernel (q.1.1, q.2.1)) (L.kernel (q.1.2, q.2.2)),
      .of_forall fun q ↦ hβ _ _, fun t ht ↦ ?_⟩
    exact ((hm t ht).comp_aemeasurable
      (hπ.aestronglyMeasurable_kernel_prodMk K.aestronglyMeasurable_kernel
        L.aestronglyMeasurable_kernel).aemeasurable).aestronglyMeasurable

/-- **Geodesics from a continuous bicombing.** If every two points `a, b` of the metric space `Z`
are joined by a geodesic segment `β a b` whose point at each time `t ∈ [0, 1]` depends continuously
on `(a, b)`, then `GromovWassersteinSpace p Z` is a geodesic space, for every `1 ≤ p ≤ ∞`. No
separability or completeness of `Z` is needed. -/
theorem isGeodesicSpace_of_continuous_bicombing (β : Z → Z → ℝ → Z)
    (hβ : ∀ a b, IsGeodesicSegment (β a b) a b)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, Continuous fun ab : Z × Z ↦ β ab.1 ab.2 t) :
    IsGeodesicSpace (GromovWassersteinSpace.{u} p Z) :=
  isGeodesicSpace_of_ae_isGeodesicSegment fun K L π hπ ↦ by
    have : IsFiniteMeasure π := hπ.isFiniteMeasure
    exact ⟨fun q ↦ β (K.kernel (q.1.1, q.2.1)) (L.kernel (q.1.2, q.2.2)),
      .of_forall fun q ↦ hβ _ _, fun t ht ↦ (hc t ht).comp_aestronglyMeasurable
        (hπ.aestronglyMeasurable_kernel_prodMk K.aestronglyMeasurable_kernel
          L.aestronglyMeasurable_kernel)⟩

/-- **The Gromov–Wasserstein space over a real normed space is geodesic**, for every
`1 ≤ p ≤ ∞` and without separability or completeness: the kernels are interpolated affinely,
`(1 - t) • ωX (x, x') + t • ωY (y, y')`, over an optimal coupling. -/
instance instIsGeodesicSpaceOfNormedSpace {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsGeodesicSpace (GromovWassersteinSpace.{u} p E) :=
  isGeodesicSpace_of_continuous_bicombing (fun a b ↦ AffineMap.lineMap a b)
    isGeodesicSegment_lineMap fun t _ ↦ by
      simp_rw [AffineMap.lineMap_apply_module]
      fun_prop

end TauCeti.GromovWassersteinSpace
