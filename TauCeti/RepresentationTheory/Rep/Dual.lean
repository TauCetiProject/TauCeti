/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Intertwining

/-!
# Contragredient duality for representations

Dualizing an equivariant linear map gives an equivariant map in the reverse direction.
These maps supply contragredient functors on categories of representations. For a representation
on a reflexive module, evaluation identifies the representation with its double dual, naturally
in the representation; for example, this applies to representations on finite projective
modules.
-/

/- The constructions below use Mathlib's `Representation.dual`, `LinearMap.dualMap`,
and `Module.evalEquiv` for the contragredient action, transpose, and double-dual evaluation. -/

public section

open CategoryTheory

namespace Rep

universe u v w

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The contragredient representation on the linear dual of the underlying module. -/
abbrev dual (V : Rep.{w} R G) : Rep.{max u w} R G := Rep.of V.ρ.dual

/-- The transpose of an equivariant map, with the contragredient actions on both duals. -/
def dualMap {V W : Rep.{w} R G} (f : V ⟶ W) :
    W.dual ⟶ V.dual :=
  Rep.ofHom {
    toLinearMap := f.hom.toLinearMap.dualMap
    isIntertwining' g := LinearMap.ext <|
      (Representation.IsIntertwiningMap.dualMap ⟨f.hom.isIntertwining⟩).isIntertwining g }

@[simp]
theorem dualMap_hom_apply {V W : Rep.{w} R G} (f : V ⟶ W)
    (φ : Module.Dual R W) (x : V) :
    (dualMap f).hom φ x = φ (f.hom x) := by rfl

/-- Transposing the identity representation morphism gives the identity. -/
@[simp]
theorem dualMap_id (V : Rep.{w} R G) : dualMap (𝟙 V) = 𝟙 V.dual :=
  (rfl)

/-- Transposing a composite reverses the order of its factors. -/
@[simp]
theorem dualMap_comp {U V W : Rep.{w} R G} (f : U ⟶ V) (g : V ⟶ W) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  (rfl)

/-- Transposing a transport morphism reverses the transport on dual representations. -/
@[simp]
theorem dualMap_eqToHom {V W : Rep.{w} R G} (h : V = W) :
    dualMap (eqToHom h) = eqToHom (congrArg dual h.symm) := by
  subst h
  simp

/-- Evaluation identifies a representation on a reflexive module with its double dual. -/
noncomputable def doubleDualIso (V : Rep.{max u w} R G) [Module.IsReflexive R V] :
    V ≅ V.dual.dual :=
  Rep.mkIso (Representation.Equiv.mk (Module.evalEquiv R V) fun g ↦ by
    ext x φ
    simp [Representation.dual_apply, Module.Dual.transpose_apply])

@[simp]
theorem doubleDualIso_hom_apply (V : Rep.{max u w} R G) [Module.IsReflexive R V]
    (x : V) (φ : Module.Dual R V) :
    (doubleDualIso V).hom.hom x φ = φ x := by rfl

/-- Evaluation into the double dual is natural on reflexive representations. -/
@[reassoc]
theorem doubleDualIso_naturality {V W : Rep.{max u w} R G}
    [Module.IsReflexive R V] [Module.IsReflexive R W] (f : V ⟶ W) :
    f ≫ (doubleDualIso W).hom = (doubleDualIso V).hom ≫ dualMap (dualMap f) :=
  (rfl)

end Rep
