/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Extension of ideal classes over arbitrary fraction fields

Mathlib's computation of `ClassGroup.extendedHom` on fractional ideals uses the canonical
fraction fields. Here the same comparison is established for any fraction fields, so it can
be used with the fractional ideals attached to finite ideles.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace ClassGroup

variable {R B K L : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.IsTorsionFree R B]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra B L] [IsFractionRing B L]

/-- Extension of an ideal class can be computed using any choices of fraction fields. -/
theorem extendedHom_mk_of_isFractionRing (I : (FractionalIdeal R⁰ K)ˣ) :
    extendedHom R B (mk K I) = mk L
      (Units.map (FractionalIdeal.extendedHom L B :
        FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom I) := by
  let f := (extendedHom R B).comp (mk K)
  let g := (mk L).comp (Units.map (FractionalIdeal.extendedHom L B :
    FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom)
  have hprime (v : HeightOneSpectrum R) : f (v.unitOfPrime K) = g (v.unitOfPrime K) := by
    let J : (Ideal R)⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
    have hv : v.unitOfPrime K = FractionalIdeal.mk0 K J := by
      apply Units.ext
      simp [J]
    simp only [f, g, MonoidHom.comp_apply, hv, mk_mk0, extendedHom_mk0]
    rw [← mk_mk0 L]
    apply congrArg (mk L)
    apply Units.ext
    simp only [FractionalIdeal.coe_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, FractionalIdeal.extendedHom_coeIdeal_eq_map]
  have hgen : Subgroup.closure
      ((fun v : HeightOneSpectrum R ↦ v.unitOfPrime K) '' Set.univ) = ⊤ := by
    apply top_unique
    intro J _
    exact FractionalIdeal.mem_closure_unitOfPrime_of_count_eq_zero (by simp)
  have heq : f = g := MonoidHom.eq_of_eqOn_dense hgen <| by
    rintro _ ⟨v, _, rfl⟩
    exact hprime v
  exact DFunLike.congr_fun heq I

end ClassGroup
