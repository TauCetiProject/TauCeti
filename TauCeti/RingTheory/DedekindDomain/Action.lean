/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Ideal

/-!
# Actions on the height-one spectrum

A group acting by ring automorphisms permutes the height-one primes. The action is induced by
Mathlib's `HeightOneSpectrum.equivOfRingEquiv`; on underlying ideals it is the pointwise action.
This allows a stable set of finite places to be used as a permutation module.
-/

public section

open IsDedekindDomain
open scoped Pointwise

namespace TauCeti

variable {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- Transport of height-one primes by a ring automorphism. -/
noncomputable instance instSMulHeightOneSpectrum : SMul G (HeightOneSpectrum R) where
  smul g v := HeightOneSpectrum.equivOfRingEquiv (MulSemiringAction.toRingEquiv G R g) v

/-- Ring automorphisms act on height-one primes by transport of ideals. -/
noncomputable instance instMulActionHeightOneSpectrum : MulAction G (HeightOneSpectrum R) where
  one_smul v := by
    ext x
    -- Transport is comap along the inverse ring automorphism.
    change (1 : G)⁻¹ • x ∈ v.asIdeal ↔ x ∈ v.asIdeal
    simp
  mul_smul g h v := by
    ext x
    -- The inverse of a product acts in the opposite order.
    change (g * h)⁻¹ • x ∈ v.asIdeal ↔ h⁻¹ • (g⁻¹ • x) ∈ v.asIdeal
    simp [mul_smul]

/-- The action on height-one primes agrees with the pointwise action on ideals. -/
@[simp]
theorem heightOneSpectrum_asIdeal_smul (g : G) (v : HeightOneSpectrum R) :
    (g • v).asIdeal = g • v.asIdeal :=
  HeightOneSpectrum.asIdeal_equivOfRingEquiv (MulSemiringAction.toRingEquiv G R g) v

end TauCeti
