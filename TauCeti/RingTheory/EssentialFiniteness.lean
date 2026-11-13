/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local algebras essentially of finite type

An `R`-algebra `S` essentially of finite type is a localization of the finite type subalgebra
`Algebra.EssFiniteType.subalgebra R S`. When `S` is local, it is the localization of that
subalgebra at a prime: the contraction of the maximal ideal of `S`. This presents `S` as the
local ring of a finite type `R`-algebra at a point, the setting of the local criteria for
smoothness and regularity.

## Main results

* `Algebra.EssFiniteType.isLocalization_atPrime_subalgebra`: a local algebra essentially of
  finite type is the localization of `Algebra.EssFiniteType.subalgebra R S` at the contraction of
  its maximal ideal.
-/

public section

open IsLocalRing

namespace Algebra.EssFiniteType

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [EssFiniteType R S]
  [IsLocalRing S]

/-- A local algebra `S` essentially of finite type over `R` is the localization of its finite type
subalgebra `Algebra.EssFiniteType.subalgebra R S` at the prime `𝔪_S ∩ subalgebra R S`. -/
theorem isLocalization_atPrime_subalgebra :
    IsLocalization.AtPrime S ((maximalIdeal S).comap (algebraMap (subalgebra R S) S)) :=
  IsLocalization.of_le (submonoid R S) _
    (fun r hr h ↦ (maximalIdeal.isMaximal S).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.map_units S ⟨r, hr⟩)))
    fun _ hr ↦ not_not.mp ((mem_maximalIdeal _).not.mp hr)

end Algebra.EssFiniteType
