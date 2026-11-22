/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic

/-!
# Trivial Hecke L-functions and the continued Dedekind zeta function

At the trivial modulus `Modulus.one K`, the presented Hecke L-function
`TauCeti.LFunctions.heckeLFunctionC (1 : RayClassCharacter (Modulus.one K))` equals the continued
Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K`. At any modulus `𝔪`, the trivial
character differs from `dedekindZetaC K` by the finite Euler correction at `𝔪.support` as
punctured germs everywhere.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_one_modulus_one`: the trivial character at `Modulus.one K`
  has continued Hecke L-function equal to `dedekindZetaC K`.
* `TauCeti.LFunctions.heckeLFunctionC_one_eventuallyEq`: punctured-germ comparison at an
  arbitrary modulus `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open Filter IsDedekindDomain
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **At the trivial modulus `Modulus.one K`, the presented Hecke L-function of the trivial
character is `dedekindZetaC K`.** -/
@[simp]
theorem heckeLFunctionC_one_modulus_one :
    heckeLFunctionC (1 : RayClassCharacter (Modulus.one K)) = dedekindZetaC K := by
  have hw : (1 : RayClassCharacter (Modulus.one K)).toUnitaryIdealWeight = 1 := by
    apply Subtype.ext
    ext I
    rw [RayClassCharacter.val_toUnitaryIdealWeight,
      RayClassCharacter.toMultiplicativeIdealWeight_one,
      MultiplicativeIdealWeight.ofBadPrimes_apply, Modulus.support_one]
    by_cases hI : I = ⊥
    · simp [hI, Ideal.isPrimeTo_iff]
    · simp [hI, Ideal.isPrimeTo_iff]
  rw [heckeLFunctionC_def, hw, UnitaryIdealWeight.toIdealArithmeticFunction_one, dedekindZetaC_def]
  exact meromorphicContinuation_congr fun s _ ↦ (dedekindZeta_eq_LSeries_normCoeff_one K s).symm

/-- **As punctured germs everywhere, the presented Hecke L-function of the trivial character of `𝔪`
is `dedekindZetaC K` times the finite Euler correction at the primes dividing `𝔪`.** -/
theorem heckeLFunctionC_one_eventuallyEq (𝔪 : Modulus K) (s : ℂ) :
    heckeLFunctionC (1 : RayClassCharacter 𝔪) =ᶠ[𝓝[≠] s] fun z ↦
      dedekindZetaC K z * ∏ 𝔭 ∈ 𝔪.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-z)) := by
  rw [← map_one (RayClassCharacter.induced (Modulus.one_dvd 𝔪))]
  filter_upwards [heckeLFunctionC_induced_eventuallyEq (Modulus.one_dvd 𝔪) 1 s] with z hz
  rw [hz, heckeLFunctionC_one_modulus_one, RayClassCharacter.eulerCorrection_one]

end TauCeti.LFunctions
