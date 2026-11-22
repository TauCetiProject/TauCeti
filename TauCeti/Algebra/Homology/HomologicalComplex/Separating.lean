/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Detecting acyclicity with a separating family

A complex in an abelian category is acyclic if all its complexes of abelian groups
`Hom(G, -)` are acyclic for `G` in a separating family. A cycle from `G` is then a boundary,
so its class in homology vanishes; separation makes the homology projection zero.
This criterion applies to any complex shape and needs no exactness of the functors `Hom(G, -)`.
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
