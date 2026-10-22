/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Categorical fundamental-group maps

This file relates maps and isomorphisms of fundamental groups to their counterparts in the
category of groups.
-/

public section

open CategoryTheory

namespace TauCeti.FundamentalGroup

universe u

variable {X Y Z W : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
variable {x : X} {y : Y} {z : Z} {w : W}

/-- A commutative square of based continuous maps induces a commutative square in `GrpCat`. -/
theorem mapOfEq_square
    (f : C(X, Y)) (g : C(Y, W)) (j : C(X, Z)) (k : C(Z, W))
    (hf : f x = y) (hg : g y = w) (hj : j x = z) (hk : k z = w)
    (h : g.comp f = k.comp j) :
    GrpCat.ofHom (_root_.FundamentalGroup.mapOfEq f hf) ≫
        GrpCat.ofHom (_root_.FundamentalGroup.mapOfEq g hg) =
      GrpCat.ofHom (_root_.FundamentalGroup.mapOfEq j hj) ≫
        GrpCat.ofHom (_root_.FundamentalGroup.mapOfEq k hk) := by
  rw [← GrpCat.ofHom_comp, ← GrpCat.ofHom_comp]
  congr 1
  ext p
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, mapOfEq_comp, mapOfEq_comp]
  exact mapOfEq_congr h _ _ p

/-- The morphism of groups underlying the isomorphism induced by a homeomorphism is the usual
map on fundamental groups. -/
theorem homeomorphMulEquivOfEq_toGrpIso_hom (e : X ≃ₜ Y) (h : e x = y) :
    (homeomorphMulEquivOfEq e h).toGrpIso.hom =
      GrpCat.ofHom (_root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h) := by
  apply GrpCat.hom_ext
  ext p
  exact homeomorphMulEquivOfEq_apply e h p

end TauCeti.FundamentalGroup
