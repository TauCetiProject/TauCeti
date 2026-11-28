/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.RingTheory.ClassGroup.RelNorm
public import TauCeti.RingTheory.DedekindDomain.SInteger.Inclusion
import TauCeti.RingTheory.ClassGroup.Extension
import TauCeti.RingTheory.Localization.Integral

/-!
# Localization and norms in extensions of rings of `S`-integers

In an integral extension, enlarge the set of inverted primes in the base and invert exactly the
primes above it in the extension. If the base enlargement is a localization, the upper
enlargement is a localization at the images of the same denominators. This gives a pushout
square of algebras. For finite extensions, extension of ideal classes along its horizontal maps
commutes with the relative class-group norm. When `ClassGroup R` is torsion,
`IsDedekindDomain.relNorm_integer_primesAbove_map_inclusion` gives this square for the canonical
inclusions for every enlargement `S ⊆ T`.

The two inputs are localization of the integral closure
(`TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure`) and localization of the
relative ideal norm (`Ideal.spanIntNorm_localization`), applied on integral representatives
of ideal classes.
-/

public section

open IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable {R B K L : Type*} [CommRing R] [CommRing B] [IsDedekindDomain R]
  [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  [Field K] [Field L] [Algebra R K] [Algebra B L] [IsFractionRing R K]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]
  {S T : Set (HeightOneSpectrum R)}

section Localization

variable [Algebra (S.integer K) (T.integer K)] [IsScalarTower R (S.integer K) (T.integer K)]
  [Algebra ((primesAbove R B S).integer L) ((primesAbove R B T).integer L)]
  [IsScalarTower B ((primesAbove R B S).integer L) ((primesAbove R B T).integer L)]

/-- When enlarging the inverted primes localizes the base ring of `S`-integers at `M`,
the induced enlargement upstairs localizes the upper ring of `S`-integers at the image of `M`. -/
theorem integer_primesAbove_isLocalization (M : Submonoid (S.integer K))
    [IsLocalization M (T.integer K)] :
    IsLocalization (Algebra.algebraMapSubmonoid ((primesAbove R B S).integer L) M)
      ((primesAbove R B T).integer L) := by
  have : IsScalarTower (S.integer K) (T.integer K) L := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (S.integer K) K L,
      IsScalarTower.algebraMap_apply (T.integer K) K L]
    exact congrArg (algebraMap K L) (coe_algebraMap_integer K x).symm
  have : IsScalarTower ((primesAbove R B S).integer L) ((primesAbove R B T).integer L) L :=
    .of_algebraMap_eq fun x ↦ (coe_algebraMap_integer L x).symm
  exact TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure
    (Rₘ := (T.integer K)) (L := L)

variable [Algebra (S.integer K) ((primesAbove R B T).integer L)]
  [IsScalarTower (S.integer K) (T.integer K) ((primesAbove R B T).integer L)]
  [IsScalarTower (S.integer K) ((primesAbove R B S).integer L) ((primesAbove R B T).integer L)]

/-- Enlarging the inverted primes by a localization gives a pushout square, with both sets
of inverted primes upstairs taken to be the full inverse images of those downstairs. -/
theorem integer_primesAbove_isPushout (M : Submonoid (S.integer K))
    [IsLocalization M (T.integer K)] :
    Algebra.IsPushout (S.integer K) ((primesAbove R B S).integer L)
      (T.integer K) ((primesAbove R B T).integer L) :=
  have := integer_primesAbove_isLocalization (B := B) (L := L) (T := T) M
  Algebra.isPushout_of_isLocalization M (T.integer K)
    ((primesAbove R B S).integer L) ((primesAbove R B T).integer L)

variable [Module.Finite R B]
  [Module.IsTorsionFree (S.integer K) (T.integer K)]
  [Module.IsTorsionFree ((primesAbove R B S).integer L) ((primesAbove R B T).integer L)]

/-- The norm of an ideal class followed by enlargement of the inverted primes equals
enlargement followed by the norm, for any localization presentation of the base enlargement.
The inverted primes upstairs are the full inverse images of those downstairs. -/
theorem relNorm_integer_primesAbove_extendedHom_eq_extendedHom_relNorm
    (M : Submonoid (S.integer K))
    [IsLocalization M (T.integer K)] (c : ClassGroup ((primesAbove R B S).integer L)) :
    ClassGroup.relNorm (T.integer K)
        (ClassGroup.extendedHom ((primesAbove R B S).integer L) ((primesAbove R B T).integer L) c) =
      ClassGroup.extendedHom (S.integer K) (T.integer K) (ClassGroup.relNorm (S.integer K) c) :=
  have := integer_primesAbove_isLocalization (B := B) (L := L) (T := T) M
  ClassGroup.relNorm_extendedHom_eq_extendedHom_relNorm M c

end Localization

variable [Module.Finite R B]

/-- For a base ring with torsion class group, the relative norm commutes with the canonical
inclusions of rings of `S`-integers for every enlargement `S ⊆ T`. -/
theorem relNorm_integer_primesAbove_map_inclusion [Fact (IsMulTorsion (ClassGroup R))]
    (h : S ⊆ T) (c : ClassGroup ((primesAbove R B S).integer L)) :
    ClassGroup.relNorm (T.integer K)
        (ClassGroup.map (Subalgebra.inclusion
          (Set.integer_mono L (primesAbove_mono R B h))).toRingHom
          (Subalgebra.inclusion_injective (Set.integer_mono L (primesAbove_mono R B h))) c) =
      ClassGroup.map (Subalgebra.inclusion (Set.integer_mono K h)).toRingHom
        (Subalgebra.inclusion_injective (Set.integer_mono K h))
        (ClassGroup.relNorm (S.integer K) c) := by
  let f := Subalgebra.inclusion (Set.integer_mono K h)
  let g := Subalgebra.inclusion (Set.integer_mono L (primesAbove_mono R B h))
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  let := ((algebraMap (T.integer K) ((primesAbove R B T).integer L)).comp f.toRingHom).toAlgebra
  have : IsScalarTower R (S.integer K) (T.integer K) :=
    .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have : IsScalarTower B ((primesAbove R B S).integer L) ((primesAbove R B T).integer L) :=
    .of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : IsScalarTower (S.integer K) (T.integer K) ((primesAbove R B T).integer L) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower (S.integer K) ((primesAbove R B S).integer L)
      ((primesAbove R B T).integer L) :=
    .of_algebraMap_eq' (algebraMap_integer_primesAbove_comp_inclusion K L h)
  have : Module.IsTorsionFree (S.integer K) (T.integer K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (Subalgebra.inclusion_injective _)
  have : Module.IsTorsionFree ((primesAbove R B S).integer L)
      ((primesAbove R B T).integer L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (Subalgebra.inclusion_injective _)
  let M := Algebra.algebraMapSubmonoid (S.integer K) (Localization.submonoid T)
  have : IsLocalization M (T.integer K) :=
    integer_isLocalization_algebraMapSubmonoid K (Localization.submonoid T)
  simpa only [ClassGroup.extendedHom_eq_map, RingHom.algebraMap_toAlgebra] using
    relNorm_integer_primesAbove_extendedHom_eq_extendedHom_relNorm (T := T) M c

end IsDedekindDomain
