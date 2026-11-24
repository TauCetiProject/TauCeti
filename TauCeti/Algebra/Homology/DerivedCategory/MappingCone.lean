/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Mapping cones of squares of quasi-isomorphisms

A square of quasi-isomorphisms of cochain complexes in an abelian category, commuting up to a
homotopy, induces a quasi-isomorphism of mapping cones
(`CochainComplex.mappingCone.quasiIso_mapOfHomotopy`); in particular so does a commutative square
(`CochainComplex.mappingCone.quasiIso_map`). This is the five lemma for the morphism of
distinguished triangles in the derived category induced by the square.
-/

public section

open CategoryTheory CategoryTheory.Pretriangulated

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Abelian C]

/-- **Five lemma for mapping cones.** The map of mapping cones induced by a square of
quasi-isomorphisms that commutes up to a homotopy `H` is a quasi-isomorphism: in the derived
category it is the third component of a morphism of distinguished triangles whose first two
components are isomorphisms. -/
instance quasiIso_mapOfHomotopy {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁}
    {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
    [QuasiIso a] [QuasiIso b] : QuasiIso (mapOfHomotopy H) := by
  let _ := HasDerivedCategory.standard C
  have e := DerivedCategory.quotientCompQhIso C
  have h₁ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map a)) :=
    (NatIso.isIso_map_iff e a).2 inferInstance
  have h₂ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map b)) :=
    (NatIso.isIso_map_iff e b).2 inferInstance
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, ← NatIso.isIso_map_iff e]
  exact Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Qh.mapTriangle.map (trianglehMapOfHomotopy H))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₁))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₂))
    h₁ h₂

/-- The map of mapping cones induced by a commutative square of quasi-isomorphisms is a
quasi-isomorphism. -/
instance quasiIso_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (map φ₁ φ₂ a b comm) :=
  map_eq_mapOfHomotopy φ₁ φ₂ a b comm ▸ inferInstance

end CochainComplex.mappingCone
