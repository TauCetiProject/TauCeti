/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Away
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralIdeal

/-!
# Compatibility of integral and fractional prime-to finite-idele maps

For a number field, the Dedekind-domain homomorphism `TauCeti.toIntegralIdealsAway` agrees
with `toIdealsAway` after passage to fractional ideals through
`NumberFieldArithmetic.integralIdealsAwayHom`.

This identifies the integral part of the finite-idele dictionary with the existing monoid
of prime-to ideals, so integral ray-class representatives can be handled adelically.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Passing to the fractional prime-to ideals agrees with the finite-idele map. -/
@[simp]
theorem integralIdealsAwayHom_toIntegralIdealsAway
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : integralFiniteIdelesAway (K := K) S) :
    NumberFieldArithmetic.integralIdealsAwayHom K S (toIntegralIdealsAway S x) =
      toIdealsAway S ⟨(x.1 : 𝔸ᶠ[𝓞 K, K]ˣ),
        (mem_adicOrdAway_iff S _).mpr ((mem_integralFiniteIdelesAway_iff S x.1).mp x.2)⟩ := by
  apply Subtype.ext
  apply Units.ext
  simp only [NumberFieldArithmetic.coe_integralIdealsAwayHom,
    coe_toIntegralIdealsAway, coe_toIntegralIdeal, toIdealsAway_apply]

end TauCeti.GlobalNumberFields
