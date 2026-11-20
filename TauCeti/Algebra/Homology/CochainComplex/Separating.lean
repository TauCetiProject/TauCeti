/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda
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

namespace HomologicalComplex

/-- A complex is acyclic if its images under the functors `Hom(G, -)`, for `G` in a separating
family, are acyclic. -/
theorem acyclic_of_isSeparating (hP : P.IsSeparating) {ι : Type*} {c : ComplexShape ι}
    (X : HomologicalComplex C c)
    (hX : ∀ G, P G → ((((linearCoyoneda ℤ C).obj (op G)).mapHomologicalComplex c).obj X).Acyclic) :
    X.Acyclic := by
  intro i
  rw [exactAt_iff_isZero_homology]
  refine IsZero.of_epi_eq_zero (X.homologyπ i) (hP _ _ fun G hG h ↦ ?_)
  have hx : (h ≫ X.iCycles i) ≫ X.d i (c.next i) = 0 := by simp
  have hexact := hX G hG i
  rw [exactAt_iff' _ (c.prev i) i (c.next i) rfl rfl, ShortComplex.moduleCat_exact_iff] at hexact
  obtain ⟨y, hy⟩ := hexact (h ≫ X.iCycles i) hx
  have hh : h = X.liftCycles (h ≫ X.iCycles i) (c.next i) rfl hx := by
    simp [← cancel_mono (X.iCycles i)]
  rw [comp_zero, hh]
  exact X.liftCycles_homologyπ_eq_zero_of_boundary _ _ rfl y hy.symm

end HomologicalComplex

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
