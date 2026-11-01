/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# Presented Hecke L-functions of ray class characters

For a ray class character `χ` of a modulus `𝔪`, `TauCeti.LFunctions.heckeLFunctionC χ` is the
canonical meromorphic continuation (`TauCeti.meromorphicContinuation`) of the L-series
`L(χ, s) = ∑_𝔞 χ(𝔞) N𝔞 ^ (-s)`, summed over the ideals prime to the finite part of `𝔪`, with
the coefficients of the unitary weight `RayClassCharacter.toUnitaryIdealWeight`. The series
depends on the presentation and not only on the character: presenting `χ` at a multiple `𝔫` of
`𝔪` deletes the Euler factors at the primes dividing `𝔫` but not `𝔪`. Those factors are
`RayClassCharacter.eulerCorrection χ 𝔫 s = ∏_{𝔭 ∣ 𝔫, 𝔭 ∤ 𝔪} (1 - χ(𝔭) N𝔭 ^ (-s))`, an entire
function (`RayClassCharacter.differentiable_eulerCorrection`) without zeros on `Re s > 0`, and on
`Re s > 1` the series of the induced character is the series of `χ` times these factors
(`RayClassCharacter.LSeries_induced`).

The comparison of presentations holds on `Re s > 1`, where the series converge absolutely, and as
an equality of punctured germs at every point of the plane. The germ statements make no assertion
about the values at the point itself: where a zero of the correction factor meets a pole, the
normal form of the product need not be the product of the values, so no identity of values on the
whole plane is claimed. The comparison holds whether or not a continuation to the plane exists,
because dividing by the correction factor turns a continuation of one series into a continuation of
the other. Every presented series is in particular the series of the primitive character
`PrimitiveRayClassCharacter.of χ` times the Euler factors at the primes dividing `𝔪` but not the
conductor.

## Main definitions

* `TauCeti.LFunctions.heckeLFunctionC`: the continued L-series of a ray class character at its
  presentation modulus.

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_induced` and
  `TauCeti.LFunctions.heckeLFunctionC_induced_eventuallyEq`: inducing multiplies the continued
  function by the deleted Euler factors, on `Re s > 1` and as germs everywhere.
* `TauCeti.LFunctions.heckeLFunctionC_eq_primitive` and
  `TauCeti.LFunctions.heckeLFunctionC_eventuallyEq_primitive`: the comparison with the primitive
  character.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section
noncomputable section

open Filter Set IsDedekindDomain
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-! ### The presented series and its continuation -/

/-- **The presented Hecke L-function** of a ray class character `χ` of `𝔪`: the canonical
meromorphic continuation from `Re s > 1` of the L-series of `χ`, summed over the ideals prime to
the finite part of `𝔪`. It depends on the presentation and not only on the character
(`heckeLFunctionC_induced`). It agrees with the L-series on `Re s > 1` once a continuation to the
plane exists (`meromorphicContinuation_eqOn`), and is `0` otherwise. -/
def heckeLFunctionC (χ : RayClassCharacter 𝔪) : ℂ → ℂ :=
  meromorphicContinuation 1 (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))

/-- The defining equation of the presented Hecke L-function, through which the general results on
`meromorphicContinuation` apply to it. -/
theorem heckeLFunctionC_def (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ = meromorphicContinuation 1
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) := (rfl)

/-- The presented Hecke L-function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_heckeLFunctionC (χ : RayClassCharacter 𝔪) :
    MeromorphicNFOn (heckeLFunctionC χ) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The presented Hecke L-function is holomorphic on `Re s > 1`. -/
theorem analyticOnNhd_heckeLFunctionC (χ : RayClassCharacter 𝔪) :
    AnalyticOnNhd ℂ (heckeLFunctionC χ) {s | 1 < s.re} :=
  analyticOnNhd_meromorphicContinuation (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight)

/-- The presented Hecke L-function of an induced character is the canonical continuation of the
L-series of the original character times the deleted Euler factors. -/
private theorem heckeLFunctionC_induced_eq_meromorphicContinuation (h : 𝔪 ∣ 𝔫)
    (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC (χ.induced h) = meromorphicContinuation 1 (χ.eulerCorrection 𝔫 •
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) :=
  meromorphicContinuation_congr fun s hs ↦ by
    rw [RayClassCharacter.LSeries_induced h χ hs, Pi.smul_apply', smul_eq_mul, mul_comm]

/-- **Inducing deletes Euler factors, for the continued functions on `Re s > 1`.** -/
theorem heckeLFunctionC_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC (χ.induced h) s = heckeLFunctionC χ s * χ.eulerCorrection 𝔫 s := by
  rw [heckeLFunctionC_induced_eq_meromorphicContinuation, meromorphicContinuation_smul_apply
    (fun z ↦ ((χ.differentiable_eulerCorrection 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (χ.differentiable_eulerCorrection 𝔫).analyticAt z)
    (fun z hz ↦ χ.eulerCorrection_ne_zero 𝔫 (zero_lt_one.trans hz))
    (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight) hs, smul_eq_mul, mul_comm,
    heckeLFunctionC_def]

/-- **Inducing deletes Euler factors, as germs.** At every point of the plane, the presented
Hecke L-function of `χ.induced h` has the punctured germ of that of `χ` times the deleted Euler
factors. This says nothing about the values at `s` itself: where a zero of the correction factor
meets a pole, the normal form of the product need not be the product of the values. -/
theorem heckeLFunctionC_induced_eventuallyEq (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC (χ.induced h) =ᶠ[𝓝[≠] s]
      fun z ↦ heckeLFunctionC χ z * χ.eulerCorrection 𝔫 z := by
  rw [heckeLFunctionC_induced_eq_meromorphicContinuation]
  filter_upwards [meromorphicContinuation_smul_eventuallyEq
    (fun z ↦ ((χ.differentiable_eulerCorrection 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (χ.differentiable_eulerCorrection 𝔫).analyticAt z)
    (fun z hz ↦ χ.eulerCorrection_ne_zero 𝔫 (zero_lt_one.trans hz))
    (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight) s] with z hz
  rw [hz, Pi.smul_apply', smul_eq_mul, mul_comm, heckeLFunctionC_def]

/-- **The presented series is the primitive series times the deleted Euler factors**, on
`Re s > 1`. The conductor is supplied by `PrimitiveRayClassCharacter.of`, not by the
presentation. -/
theorem heckeLFunctionC_eq_primitive (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC χ s = heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character s *
      (PrimitiveRayClassCharacter.of χ).character.eulerCorrection 𝔪 s := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ]
  exact heckeLFunctionC_induced _ _ hs

/-- **The presented series is the primitive series times the deleted Euler factors**, as germs at
every point of the plane. -/
theorem heckeLFunctionC_eventuallyEq_primitive (χ : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC χ =ᶠ[𝓝[≠] s]
      fun z ↦ heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character z *
        (PrimitiveRayClassCharacter.of χ).character.eulerCorrection 𝔪 z := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ]
  exact heckeLFunctionC_induced_eventuallyEq _ _ s

end TauCeti.LFunctions
