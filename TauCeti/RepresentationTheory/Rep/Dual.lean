/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Contragredient duality for representations

Dualizing an equivariant linear map gives an equivariant map in the reverse direction.
These maps supply contragredient functors on categories of representations. For a representation
on a reflexive module, evaluation identifies the representation with its double dual, naturally
in the representation. In particular this applies to finite free integral representations.

The constructions reuse Mathlib's `Representation.dual`, `LinearMap.dualMap`, and
`Module.evalEquiv`.
-/

public section

open CategoryTheory

namespace Rep

universe u v w

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The contragredient representation on the linear dual of the stored module. -/
abbrev dual (V : Rep.{w} R G) : Rep.{max u w} R G := Rep.of V.ρ.dual

/-- The transpose of an equivariant map, with the contragredient actions on both duals. -/
def dualMap {V W : Rep.{w} R G} (f : V ⟶ W) :
    W.dual ⟶ V.dual :=
  Rep.ofHom {
    toLinearMap := f.hom.toLinearMap.dualMap
    isIntertwining' := fun g ↦ by
      ext φ x
      exact congrArg φ (Representation.IntertwiningMap.isIntertwining _ _ f.hom g⁻¹ x).symm
  }

@[simp]
theorem dualMap_hom_apply {V W : Rep.{w} R G} (f : V ⟶ W)
    (φ : Module.Dual R W) (x : V) :
    (dualMap f).hom φ x = φ (f.hom x) := by rfl

/-- Transposing the identity representation morphism gives the identity. -/
@[simp]
theorem dualMap_id (V : Rep.{w} R G) : dualMap (𝟙 V) = 𝟙 V.dual := by
  ext φ x
  rfl

/-- Transposing a composite reverses the order of its factors. -/
@[simp]
theorem dualMap_comp {U V W : Rep.{w} R G} (f : U ⟶ V) (g : V ⟶ W) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  ext φ x
  rfl

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
    f ≫ (doubleDualIso W).hom = (doubleDualIso V).hom ≫ dualMap (dualMap f) := by
  ext x φ
  rfl

end Rep
