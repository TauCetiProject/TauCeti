/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# Transport between isomorphic number-field extensions

This file records how properties of primes of rings of integers transport along isomorphisms of
field extensions. Over a fixed base, use `AlgEquiv.isUnramifiedIn_iff` applied to
`NumberField.RingOfIntegers.mapAlgEquiv`.

## Main results

* `RingEquiv.forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff`: unramifiedness at every
  height-one prime of the ring of integers is invariant under a commuting square of field
  isomorphisms.
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace RingEquiv

variable {K L K' L' : Type*} [Field K] [Field L] [Algebra K L]
  [Field K'] [Field L'] [Algebra K' L']

/-- **Unramifiedness at every height-one prime of the ring of integers transports across compatible
field isomorphisms.** -/
theorem forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L)) :
    (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ↔
      ∀ w : HeightOneSpectrum (𝓞 L'), Algebra.IsUnramifiedAt (𝓞 K') w.asIdeal := by
  refine forall_heightOneSpectrum_isUnramifiedAt_iff
    (NumberField.RingOfIntegers.mapRingEquiv eK)
    (NumberField.RingOfIntegers.mapRingEquiv eL) (RingHom.ext fun x ↦ ?_)
  apply NumberField.RingOfIntegers.coe_injective
  simp only [RingHom.comp_apply, RingHom.coe_coe,
    ← IsScalarTower.algebraMap_apply (𝓞 K') (𝓞 L') L',
    IsScalarTower.algebraMap_apply (𝓞 K') K' L',
    NumberField.RingOfIntegers.mapRingEquiv_apply,
    NumberField.RingOfIntegers.coe_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
    IsScalarTower.algebraMap_apply (𝓞 K) K L]
  exact RingHom.congr_fun he _

end RingEquiv
