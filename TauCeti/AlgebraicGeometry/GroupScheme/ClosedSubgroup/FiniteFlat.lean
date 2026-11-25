/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat

/-!
# Finite locally free closed subgroup schemes

A closed subgroup scheme `P` of a commutative group scheme `G₀` over a base scheme `S` whose
structure morphism to `S` is finite, flat, and locally of finite presentation bundles into a
`FiniteFlatCommGroupScheme S` (`TauCeti.ClosedSubgroupScheme.toFiniteFlatCommGroupScheme`).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.ClosedSubgroupScheme

universe u

variable {S : Scheme.{u}} {G₀ : Grp (Over S)} [IsCommMonObj G₀.X]

/-- A closed subgroup scheme `P` of a commutative group scheme `G₀` over `S` whose structure
morphism to `S` is finite, flat, and locally of finite presentation bundles into a
`FiniteFlatCommGroupScheme S`. -/
noncomputable def toFiniteFlatCommGroupScheme (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.val : Grp (Over S)).X.hom] [Flat (P.val : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.val : Grp (Over S)).X.hom] :
    TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S where
  carrier := (P.val : Grp (Over S)).X.left
  structureMap := (P.val : Grp (Over S)).X.hom
  grp := (P.val : Grp (Over S)).grp
  comm := isCommMonObj_underlying P
  finite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance

/-- The underlying scheme of `P.toFiniteFlatCommGroupScheme` is
`(P.val : Grp (Over S)).X.left`. -/
@[simp]
theorem toFiniteFlatCommGroupScheme_carrier (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.val : Grp (Over S)).X.hom] [Flat (P.val : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.val : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.carrier = (P.val : Grp (Over S)).X.left :=
  (rfl)

/-- The `S`-scheme underlying `P.toFiniteFlatCommGroupScheme` is
`Over.mk (P.val : Grp (Over S)).X.hom`. -/
@[simp]
theorem toFiniteFlatCommGroupScheme_toOver (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.val : Grp (Over S)).X.hom] [Flat (P.val : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.val : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.toOver = Over.mk (P.val : Grp (Over S)).X.hom :=
  (rfl)

/-- The rank function of `P.toFiniteFlatCommGroupScheme` is that of
`(P.val : Grp (Over S)).X.hom`. -/
@[simp]
theorem finrank_toFiniteFlatCommGroupScheme_structureMap (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.val : Grp (Over S)).X.hom] [Flat (P.val : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.val : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.structureMap.finrank =
      (P.val : Grp (Over S)).X.hom.finrank :=
  (rfl)

end TauCeti.ClosedSubgroupScheme
