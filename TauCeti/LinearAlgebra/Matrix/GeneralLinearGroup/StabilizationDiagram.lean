/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# The general linear group stabilization diagram

Package the finite general linear groups and their block-diagonal inclusions as a diagram
of groups. The inclusions into the stable general linear group form the associated cocone;
this allows functorial constructions on the stages to use the actual stabilization maps.
-/

public section

open CategoryTheory CategoryTheory.Limits Matrix

namespace TauCeti.StableGeneralLinearGroup

variable (R : Type*) [Ring R]

/-- The diagram of finite general linear groups under block-diagonal stabilization. -/
@[expose] def stabilizationDiagram : ℕ ⥤ GrpCat where
  obj n := GrpCat.of (GL (Fin n) R)
  map f := GrpCat.ofHom (stabilizeGL R f.le)
  map_id n := by rw [stabilizeGL_refl, GrpCat.ofHom_id]
  map_comp f g := GrpCat.ext fun x ↦ (stabilizeGL_stabilizeGL f.le g.le x).symm

/-- The group in stage `n` of stabilization is `GLₙ(R)`. -/
@[simp] theorem stabilizationDiagram_obj (n : ℕ) :
    (stabilizationDiagram R).obj n = GrpCat.of (GL (Fin n) R) := (rfl)

/-- The transition from rank `i` to rank `j` appends an identity block. -/
@[simp] theorem stabilizationDiagram_map {i j : ℕ} (f : i ⟶ j) :
    (stabilizationDiagram R).map f = GrpCat.ofHom (stabilizeGL R f.le) := (rfl)

/-- The cocone of inclusions into the stable general linear group. -/
@[expose] noncomputable def stabilizationCocone : Cocone (stabilizationDiagram R) where
  pt := GrpCat.of (StableGeneralLinearGroup R)
  ι :=
    { app := fun n ↦ GrpCat.ofHom (of R n)
      naturality := fun _ _ f ↦ GrpCat.ext fun x ↦ of_stabilizeGL f.le x }

/-- The vertex of the stabilization cocone is the stable general linear group. -/
@[simp] theorem stabilizationCocone_pt :
    (stabilizationCocone R).pt = GrpCat.of (StableGeneralLinearGroup R) := (rfl)

/-- The leg of the stabilization cocone is the inclusion of the finite group. -/
@[simp] theorem stabilizationCocone_ι_app (n : ℕ) :
    (stabilizationCocone R).ι.app n = GrpCat.ofHom (of R n) := (rfl)

end TauCeti.StableGeneralLinearGroup

end
