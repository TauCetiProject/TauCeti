/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback of local sections

The unit of pullback and pushforward gives a semilinear map on sections over every open.
These maps commute with coefficient maps, restriction, and composition of scheme morphisms.
The composition equation identifies direct and iterated pullback through the canonical
pullback-composition isomorphism, so sections can be compared across successive morphisms.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (U : X.Opens)
/-- Pulling back sections along `g`, as a semilinear map over pullback of local functions. -/
def pullbackSections : Γ(M, U) →ₛₗ[(g.app U).hom]
    Γ((pullback g).obj M, g ⁻¹ᵁ U) where
  toFun := ((pullbackPushforwardAdjunction g).unit.app M).app U
  map_add' := map_add _
  map_smul' r s := ((pullbackPushforwardAdjunction g).unit.app M).app_smul r s
/-- Pullback of sections is the component of the pullback--pushforward adjunction unit. -/
lemma pullbackSections_apply (s : Γ(M, U)) :
    pullbackSections g M U s = ((pullbackPushforwardAdjunction g).unit.app M).app U s := (rfl)
/-- Pullback of sections is natural in the coefficient sheaf. -/
lemma pullbackSections_naturality {N : X.Modules} (f : M ⟶ N) (s : Γ(M, U)) :
    ((pullback g).map f).app (g ⁻¹ᵁ U) (pullbackSections g M U s) =
      pullbackSections g N U (f.app U s) := by
  exact congr($((pullbackPushforwardAdjunction g).unit.naturality f).app U s).symm
/-- Pullback of sections commutes with restriction to smaller opens. -/
lemma pullbackSections_restrict {V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    ((pullback g).obj M).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
      (pullbackSections g M U s) = pullbackSections g M V (M.presheaf.map i.op s) := by
  exact (PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction g).unit.app M).val i.op s).symm
variable {Z : Scheme.{u}} (f : Z ⟶ Y)
/-- The composition comparison carries the pullback of a section to its iterated pullback. -/
lemma pullbackSections_comp (s : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (pullbackSections (f ≫ g) M U s) =
    pullbackSections f ((pullback g).obj M) (g ⁻¹ᵁ U)
      (pullbackSections g M U s) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun a ↦ a.app U s) h).symm

end AlgebraicGeometry.Scheme.Hom
