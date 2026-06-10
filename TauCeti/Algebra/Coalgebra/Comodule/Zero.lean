/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import TauCeti.Algebra.Coalgebra.Comodule.Finite

/-!
# The zero comodule

This file adds the zero object for right comodules over a coalgebra. This is Layer 1
infrastructure for the reductive-groups roadmap target "Comodules over a coalgebra/Hopf
algebra": before the finite-dimensional comodule category can be used as the additive
representation category, it needs the standard zero object compatible with the existing zero
morphisms.

The zero comodule is the unique coaction on `PUnit`. We expose it both unbundled and bundled,
and register zero-object instances for `ComoduleCat` and `FGComoduleCat`.

## Main declarations

* `TauCeti.Comodule.instPUnit`: the zero right comodule on `PUnit`.
* `TauCeti.ComoduleCat.zero`: the bundled zero comodule.
* `HasZeroObject (ComoduleCat R C)`.
* `HasZeroObject (FGComoduleCat R C)`.

## References

The construction is the standard zero object in the category of comodules; see Sweedler,
*Hopf Algebras*, Chapter 2. It supplies an additive-category prerequisite for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1, "Comodules over a coalgebra/Hopf
algebra". The proof that a subsingleton bundled comodule is zero follows Mathlib's
`SemimoduleCat.isZero_of_subsingleton` / `ModuleCat.isZero_of_subsingleton` pattern.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

variable (R : Type u) (C : Type v)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The unique right-comodule structure on the zero module `PUnit`. -/
instance instPUnit : Comodule R C PUnit where
  coact := 0
  coassoc := by
    ext x
    exact Subsingleton.elim _ _
  lTensor_counit_comp_coact := by
    ext x
    exact Subsingleton.elim _ _

/-- The coaction on the zero comodule is the zero linear map. -/
@[simp]
theorem punit_coact : coact (R := R) (C := C) (M := PUnit) = 0 :=
  rfl

end Comodule

namespace ComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The bundled zero right comodule. -/
abbrev zero : ComoduleCat.{u, v, w} R C :=
  of R C PUnit.{w + 1}

/-- The bundled zero comodule has carrier `PUnit`. -/
@[simp]
theorem zero_carrier : (zero R C : Type) = PUnit :=
  rfl

/-- The coaction on the bundled zero comodule is zero. -/
@[simp]
theorem zero_coact :
    Comodule.coact (R := R) (C := C) (M := zero R C) = 0 :=
  rfl

/-- A comodule whose underlying type is subsingleton is a zero object. -/
theorem isZero_of_subsingleton (M : ComoduleCat.{u, v, w} R C) [Subsingleton M] : IsZero M where
  unique_to N :=
    ⟨{ default := (0 : M ⟶ N)
       uniq := by
        intro f
        ext m
        rw [Subsingleton.elim m (0 : M)]
        exact map_zero f.toLinearMap }⟩
  unique_from N :=
    ⟨{ default := (0 : N ⟶ M)
       uniq := by
        intro f
        ext m
        subsingleton }⟩

/-- The category of right comodules has a zero object. -/
instance hasZeroObject : HasZeroObject (ComoduleCat.{u, v, w} R C) :=
  ⟨⟨zero R C, isZero_of_subsingleton (R := R) (C := C) (zero R C)⟩⟩

/-- The finite-generation property contains the zero comodule. -/
instance isFG_containsZero : (isFG (R := R) (C := C)).ContainsZero where
  exists_zero :=
    ⟨zero R C, isZero_of_subsingleton (R := R) (C := C) (zero R C),
      show Module.Finite R (zero R C) from inferInstance⟩

end ComoduleCat

namespace FGComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The bundled finitely generated zero right comodule. -/
abbrev zero : FGComoduleCat.{u, v, w} R C :=
  ⟨ComoduleCat.zero R C, show Module.Finite R (ComoduleCat.zero R C) from inferInstance⟩

/-- The ambient comodule underlying the finitely generated zero comodule is the zero comodule. -/
@[simp]
theorem zero_obj :
    (zero R C : FGComoduleCat.{u, v, w} R C).obj = ComoduleCat.zero R C :=
  rfl

/-- The category of finitely generated right comodules has a zero object. -/
instance hasZeroObject : HasZeroObject (FGComoduleCat.{u, v, w} R C) :=
  inferInstance

end FGComoduleCat

end TauCeti
