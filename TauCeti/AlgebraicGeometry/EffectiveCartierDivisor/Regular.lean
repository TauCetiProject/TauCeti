/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.RegularLocalRing.OfQuotient

/-!
# Ambient regularity along a regular effective Cartier divisor

If an effective Cartier divisor on a locally Noetherian scheme has regular local rings,
then the ambient local rings at points of the divisor are regular. No regularity is required
away from the divisor. This supplies the local regularity condition needed to extend covers
across a regular divisor.

On an affine chart with equation `a`, the divisor has coordinate ring `A/(a)`. Regularity of
the divisor makes this quotient regular, and regularity lifts at primes containing `a`
because `a` is a nonzerodivisor.

## References

* [Stacks Project, Lemma 58.31.3](https://stacks.math.columbia.edu/tag/0EYE).
* [Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU).
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}

/-- If an effective Cartier divisor has regular local rings, then the ambient local rings
at all points of its support are regular. The ambient scheme need not be regular off the
divisor. -/
theorem IsEffectiveCartier.isRegularLocalRing_stalk_of_mem_support
    (hI : I.IsEffectiveCartier)
    (hD : ∀ y : I.subscheme, IsRegularLocalRing (I.subscheme.presheaf.stalk y))
    {x : X} (hx : x ∈ I.support) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI x
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ U.1) := U.2.preimage I.subschemeι
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : IsNoetherianRing Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hV⟩
  have : IsRegularRing Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) :=
    (TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk hV).mpr
      fun y _ ↦ hD y
  have : IsRegularRing (Γ(X, U) ⧸ I.ideal U) :=
    .of_ringEquiv (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  have : IsRegularRing (Γ(X, U) ⧸ Ideal.span {a}) := hUa ▸ ‹IsRegularRing _›
  let P := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  have haP : a ∈ P := by
    by_contra haP
    have hunit := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) P a).mpr haP
    have hz := (mem_support_iff_of_mem hxU).mp hx
    exact (X.mem_zeroLocus_iff _ x).mp hz a
      (hUa ▸ Ideal.mem_span_singleton_self a) ((X.mem_basicOpen a x hxU).mpr hunit)
  have := TauCeti.IsRegularLocalRing.localization_of_isRegularRing_quotient
    (isLeftRegular_iff_isRegular.mp ha.isLeftRegular).mem_nonZeroDivisors P haP
  exact .of_ringEquiv (IsLocalization.algEquiv P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv

end AlgebraicGeometry.Scheme.IdealSheafData
