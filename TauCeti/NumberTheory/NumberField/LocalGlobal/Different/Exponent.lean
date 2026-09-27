/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity

/-!
# The different exponent in the completed integer ring

The coefficient of the different ideal of a number-field extension at a prime `w` equals the
coefficient of the different ideal of the completed integer-ring extension at its maximal ideal.
The global different extends to the completed different, and completion preserves the
multiplicity of an ideal at the selected prime. This is the coefficient comparison needed to
transport local different-exponent theorems to number fields.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, Proposition 2.2 and Theorem 2.6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The exponent of the completed different at the maximal ideal is the exponent of the global
different at `w`. -/
@[simp]
theorem multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal :
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  calc
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        ((differentIdeal (𝓞 K) (𝓞 L)).map
          (algebraMap (𝓞 L) (w.adicCompletionIntegers L))) := by
        rw [map_differentIdeal_eq_differentIdeal_adicCompletionIntegers v w]
    _ = _ := w.multiplicity_map_adicCompletionIntegers (K := L)
      (differentIdeal (𝓞 K) (𝓞 L)) differentIdeal_ne_bot

end IsDedekindDomain.HeightOneSpectrum

end
