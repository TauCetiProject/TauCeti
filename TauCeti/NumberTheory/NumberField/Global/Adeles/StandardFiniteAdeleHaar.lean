/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar

/-!
# The standard Haar measure on the finite adeles of a number field

Let `K` be a number field with `r₂` complex places, discriminant `d_K`, finite adeles `𝔸_f` and
integral finite adeles `Ô`. The *standard Haar measure* on `𝔸_f`
(`TauCeti.GlobalNumberFields.standardFiniteAdeleHaar`) is the additive Haar measure for which `Ô`
has volume `vol(Ô) = 2^{r₂}/√|d_K|` (`TauCeti.GlobalNumberFields.volIntegralAdeles`). This is the
normalisation of the Haar measure of `𝔸_f` used for the Fourier integrals over the finite adeles
of a totally complex field, such as the density of a function at a norm
(`TauCeti.standardNormDensity`).

## Main declarations

* `TauCeti.GlobalNumberFields.volIntegralAdeles`: the number `2^{r₂}/√|d_K|`.
* `TauCeti.GlobalNumberFields.standardFiniteAdeleHaar`: the Haar measure on `𝔸_f` giving `Ô`
  this volume (`TauCeti.GlobalNumberFields.standardFiniteAdeleHaar_integralAdeles`), defined as
  `vol(Ô)` times the Haar measure giving `Ô` volume one
  (`TauCeti.GlobalNumberFields.standardFiniteAdeleHaar_def`).

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), §4.1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
  MeasureTheory MeasureTheory.Measure
open scoped NumberField.AdeleRing NNReal

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- The volume `vol(Ô) = 2^{r₂}/√|d_K|` of the integral finite adeles of a number field `K` for its
standard Haar measure, where `r₂` is the number of complex places and `d_K` the discriminant. -/
def volIntegralAdeles : ℝ≥0 :=
  2 ^ nrComplexPlaces K / NNReal.sqrt ‖(discr K : ℝ)‖₊

/-- The volume `2^{r₂}/√|d_K|` of the integral finite adeles is nonzero. -/
theorem volIntegralAdeles_ne_zero : volIntegralAdeles K ≠ 0 := by
  simp [volIntegralAdeles, discr_ne_zero]

/-- The **standard Haar measure** on the finite adeles `𝔸_f` of a number field `K`: the additive
Haar measure for which the integral finite adeles `Ô` have volume `2^{r₂}/√|d_K|`. -/
def standardFiniteAdeleHaar : Measure 𝔸ᶠ[K] :=
  volIntegralAdeles K • addHaarMeasure (integralAdelesPositiveCompacts (𝓞 K) K)

/-- Unfolding `standardFiniteAdeleHaar`: it is `vol(Ô)` times the Haar measure giving `Ô` volume
one. -/
theorem standardFiniteAdeleHaar_def :
    standardFiniteAdeleHaar K =
      volIntegralAdeles K • addHaarMeasure (integralAdelesPositiveCompacts (𝓞 K) K) :=
  (rfl)

instance : IsAddHaarMeasure (standardFiniteAdeleHaar K) :=
  .nnreal_smul _ (volIntegralAdeles_ne_zero K)

/-- The integral finite adeles `Ô` have volume `2^{r₂}/√|d_K|` for the standard Haar measure. -/
@[simp]
theorem standardFiniteAdeleHaar_integralAdeles :
    standardFiniteAdeleHaar K (integralAdeles (𝓞 K) K) = volIntegralAdeles K := by
  rw [standardFiniteAdeleHaar_def, _root_.smul_apply, ← coe_integralAdelesPositiveCompacts,
    addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one]

end TauCeti.GlobalNumberFields
