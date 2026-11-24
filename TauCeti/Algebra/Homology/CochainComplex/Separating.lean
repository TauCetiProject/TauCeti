/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Separating
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Detecting acyclicity and quasi-isomorphisms with a separating family

Let `P` be a separating family of objects of an abelian category `C`. A complex `X` in `C` is
acyclic as soon as the complexes of abelian groups `Hom(G, X)` are acyclic for all `G` in `P`
(`HomologicalComplex.acyclic_of_isSeparating`): a cycle `G ⟶ Zⁿ(X)` is then a boundary, so its
class in `Hⁿ(X)` vanishes, and a morphism out of `Zⁿ(X)` vanishing on all such cycles is zero.
The functors `Hom(G, -)` are not exact, so the converse fails in general.

Since `Hom(G, -)` commutes with mapping cones, a morphism `φ` of cochain complexes is a
quasi-isomorphism as soon as all the maps `Hom(G, φ)` are
(`CochainComplex.quasiIso_of_isSeparating`).

For the category of sheaves of modules and the family of the extensions by zero `j_! 𝒪_U` of
the structure sheaves of opens, `Hom(j_! 𝒪_U, -)` is the sections over `U`, and this is the
usual statement that a complex of sheaves whose sections over every open are acyclic is acyclic.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

namespace CochainComplex

/-- A morphism of cochain complexes is a quasi-isomorphism if its images under the functors
`Hom(G, -)`, for `G` in a separating family, are quasi-isomorphisms. -/
theorem quasiIso_of_isSeparating (hP : P.IsSeparating) {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (hφ : ∀ G, P G → QuasiIso ((((linearCoyoneda ℤ C).obj (op G)).mapHomologicalComplex _).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff_acyclic_mappingCone]
  refine HomologicalComplex.acyclic_of_isSeparating hP _ fun G hG n ↦ ?_
  have := hφ G hG
  exact ((quasiIso_iff_acyclic_mappingCone _).1 inferInstance n).of_iso
    (mappingCone.mapHomologicalComplexIso φ _).symm

end CochainComplex
