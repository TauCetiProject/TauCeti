/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Group Object Laws for Representable Functors

This file defines the group object structure on a representable functor from a
Cartesian monoidal category to the category of commutative additive groups.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md.
-/

public section

universe v w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Opposite

namespace TauCeti.Jacobian

/--
Constructs a group object from a functor to `AddCommGrpCat` that is representable
after composing with the forgetful functor.
-/
@[reducible]
noncomputable def representable_AddCommGrp_GrpObj {C_ : Type v} [Category C_]
    [CartesianMonoidalCategory C_] (F : C_ᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : (F ⋙ forget AddCommGrpCat).IsRepresentable) :
    GrpObj (Functor.reprX (F ⋙ forget AddCommGrpCat)) :=
  GrpObj.ofRepresentableBy (Functor.reprX (F ⋙ forget AddCommGrpCat))
    (F ⋙ AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat)
    (Functor.representableBy (F ⋙ forget AddCommGrpCat))

end TauCeti.Jacobian
