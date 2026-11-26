/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Countable
public import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar

/-!
# Checks for the normalized Haar measure on the finite adeles

Checks of AdelicAlgebraicGroups §0.4 for a number field `K`. For *finite-adele-haar*, with `μ_f`
the additive Haar measure on `𝔸_{K,f}` giving `∏_v 𝒪_v` mass one:

* for a nonzero ideal `𝔞` of `𝓞 K`, the closure of `𝔞` in `∏_v 𝒪_v` has measure
  `(Ideal.absNorm 𝔞)⁻¹`;
* `μ_f` is not a finite measure.
-/

public section

open MeasureTheory Measure IsDedekindDomain FiniteAdeleRing NumberField
open scoped ENNReal

namespace TauCeti.Examples

variable (K : Type*) [Field K] [NumberField K]

/-- For a nonzero ideal `𝔞` of `𝓞 K`, the closure of `𝔞` in the integral finite adeles has
measure `(Ideal.absNorm 𝔞)⁻¹` for the Haar measure giving them mass one. -/
example {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) :
    have : Finite (𝓞 K ⧸ 𝔞) := (Ideal.absNorm_ne_zero_iff 𝔞).1
      (Ideal.absNorm_eq_zero_iff.not.2 h𝔞)
    addHaarMeasure (integralAdelesPositiveCompacts (𝓞 K) K)
        (((↑) : integralAdeles (𝓞 K) K → FiniteAdeleRing (𝓞 K) K) ''
          (completedIdeal K 𝔞 : Set (integralAdeles (𝓞 K) K))) =
      (Ideal.absNorm 𝔞 : ℝ≥0∞)⁻¹ := by
  intro _
  rw [Ideal.absNorm_eq_natCard]
  exact addHaarMeasure_image_completedIdeal h𝔞

/-- The normalized Haar measure on the finite adeles is not a finite measure. -/
example : addHaarMeasure (integralAdelesPositiveCompacts (𝓞 K) K) Set.univ = ∞ :=
  addHaar_univ_eq_top _

end TauCeti.Examples
