/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Basic lemmas on localizations

For a localization `S` of a commutative semiring `R` at a submonoid `M`:

* `IsLocalization.lift_injective_of_injective`: if an injective ring homomorphism `g : R →+* P`
  maps `M` into the units of `P`, then its lift `IsLocalization.lift hg : S →+* P` is injective
  (complementing Mathlib's `IsLocalization.lift_injective_iff` and `IsLocalization.eq_of_eq`).
* `TauCeti.IsLocalization.isUnit_mk'_iff` and `TauCeti.Localization.isUnit_mk_iff`: a fraction
  `a / m` (`m ∈ M`) is a unit in `S` (or `Localization M`) if and only if `algebraMap R S a` is a
  unit, since `m` already maps to a unit.
-/

public section

namespace IsLocalization

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S] {P : Type*} [CommSemiring P] {g : R →+* P}

/-- If an injective ring homomorphism `g : R →+* P` sends every element of `M` to a unit, then its
lift `S →+* P` out of a localization `S` of `R` at `M` is injective. -/
theorem lift_injective_of_injective (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (lift (M := M) (S := S) hg) :=
  (lift_injective_iff hg).mpr fun _ _ ↦
    ⟨eq_of_eq (S := S) hg, fun h ↦ congrArg (algebraMap R S) (hinj h)⟩

end IsLocalization

namespace TauCeti.IsLocalization

open _root_.IsLocalization

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S]

/-- A fraction `IsLocalization.mk' S x y` is a unit in `S` if and only if its numerator `x` maps to
a unit in `S`. -/
@[simp]
theorem isUnit_mk'_iff {x : R} {y : M} :
    IsUnit (mk' S x y) ↔ IsUnit (algebraMap R S x) :=
  ⟨fun h ↦ mk'_spec S x y ▸ h.mul (map_units S y),
    fun h ↦ isUnit_of_dvd_unit ⟨algebraMap R S y, (mk'_spec S x y).symm⟩ h⟩

end TauCeti.IsLocalization

namespace TauCeti.Localization

open _root_.Localization

variable {R : Type*} [CommSemiring R] {M : Submonoid R}

/-- A fraction `Localization.mk x y` is a unit in `Localization M` if and only if `x` maps to a unit
in `Localization M`. -/
@[simp]
theorem isUnit_mk_iff {x : R} {y : M} :
    IsUnit (mk x y) ↔ IsUnit (algebraMap R (_root_.Localization M) x) := by
  rw [mk_eq_mk'_apply, TauCeti.IsLocalization.isUnit_mk'_iff]

end TauCeti.Localization
