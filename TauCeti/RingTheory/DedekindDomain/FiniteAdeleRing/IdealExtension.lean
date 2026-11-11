/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Extension
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.FractionalIdeal.Extended
public import TauCeti.RingTheory.ClassGroup.Extension

/-!
# Extension of finite ideles and fractional ideals

The fractional ideal associated to an extended finite idele is the extension of its fractional
ideal. Both constructions multiply the order at a prime by the ramification index. This
comparison connects the idelic and ideal-theoretic descriptions of extension of scalars.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K B L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower R B L]

/-- Extension of a finite idele multiplies its order at a prime by the ramification index. -/
@[simp]
theorem adicOrd_unitsMap_finiteAdeleExtension (x : (FiniteAdeleRing R K)ˣ)
    (w : HeightOneSpectrum B) :
    adicOrd (Units.map (finiteAdeleExtension R K B L :
      FiniteAdeleRing R K →* FiniteAdeleRing B L) x) w =
      (((w.under R).asIdeal.ramificationIdx' w.asIdeal : ℕ) : ℤ) * adicOrd x (w.under R) := by
  simp only [adicOrd_def, Units.coe_map, MonoidHom.coe_ofClass,
    finiteAdeleExtension_apply, HeightOneSpectrum.valued_adicCompletionExtension,
    WithZero.log_pow]
  ring

variable [Module.IsTorsionFree R B]

/-- **The fractional ideal of an extended finite idele is the extended fractional ideal.** -/
@[simp]
theorem toFractionalIdeal_unitsMap_finiteAdeleExtension (x : (FiniteAdeleRing R K)ˣ) :
    toFractionalIdeal (Units.map (finiteAdeleExtension R K B L :
      FiniteAdeleRing R K →* FiniteAdeleRing B L) x) =
      Units.map (FractionalIdeal.extendedHom L B :
        FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom (toFractionalIdeal x) := by
  let y := Units.map (finiteAdeleExtension R K B L :
    FiniteAdeleRing R K →* FiniteAdeleRing B L) x
  let J := Units.map (FractionalIdeal.extendedHom L B :
    FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom (toFractionalIdeal x)
  have h (w : HeightOneSpectrum B) :
      FractionalIdeal.count L w (toFractionalIdeal y : FractionalIdeal B⁰ L) =
        FractionalIdeal.count L w (J : FractionalIdeal B⁰ L) := by
    rw [count_coe_toFractionalIdeal, adicOrd_unitsMap_finiteAdeleExtension]
    simp only [J, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      FractionalIdeal.extendedHom'_apply, FractionalIdeal.count_extended,
      count_coe_toFractionalIdeal]
  exact FractionalIdeal.units_ext_count h

/-- Extension of finite ideles induces the usual extension map on ideal classes.
The simplifier uses `toClassGroup_apply`; this is the folded class-group comparison. -/
theorem toClassGroup_unitsMap_finiteAdeleExtension (x : (FiniteAdeleRing R K)ˣ) :
    toClassGroup B L (Units.map (finiteAdeleExtension R K B L :
      FiniteAdeleRing R K →* FiniteAdeleRing B L) x) =
      ClassGroup.extendedHom R B (toClassGroup R K x) := by
  rw [toClassGroup_apply, toClassGroup_apply, toFractionalIdeal_unitsMap_finiteAdeleExtension,
    ClassGroup.extendedHom_mk_of_isFractionRing (L := L)]

end IsDedekindDomain.FiniteAdeleRing
