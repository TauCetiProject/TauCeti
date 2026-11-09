/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# Extension of ideal classes over arbitrary fraction fields

Mathlib's computation of `ClassGroup.extendedHom` on fractional ideals uses the canonical
fraction fields. Here the same comparison is established for any fraction fields, so it can
be used with the fractional ideals attached to finite ideles.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable {R B K L : Type*} [CommRing R] [IsDomain R]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra B L] [IsFractionRing B L]

/-- Extension of an ideal class can be computed using any choices of fraction fields. -/
theorem extendedHom_mk_of_isFractionRing (I : (FractionalIdeal R⁰ K)ˣ) :
    extendedHom R B (mk K I) = mk L
      (Units.map (FractionalIdeal.extendedHom L B :
        FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom I) := by
  have h (J : FractionalIdeal R⁰ K) :
      FractionalIdeal.extendedHom (FractionRing B) B
          (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R) J) =
        FractionalIdeal.canonicalEquiv B⁰ L (FractionRing B)
          (FractionalIdeal.extendedHom L B J) := by
    obtain ⟨a, A, _, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
    simp only [map_mul, FractionalIdeal.canonicalEquiv_spanSingleton,
      FractionalIdeal.canonicalEquiv_coeIdeal, FractionalIdeal.extendedHom_spanSingleton,
      FractionalIdeal.extendedHom_coeIdeal_eq_map]
    simp only [IsFractionRing.map, map_inv₀]
    -- The proof argument introduced by canonicalEquiv_spanSingleton requires unfolding
    -- Submonoid membership beyond the transparency used by rw.
    erw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq,
      IsLocalization.map_eq]
    rfl
  rw [← mk_canonicalEquiv K (FractionRing R) I, extendedHom_mk,
    ← mk_canonicalEquiv L (FractionRing B)]
  apply congrArg (mk (FractionRing B))
  apply Units.ext
  exact h I

end ClassGroup
