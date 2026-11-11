/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Cycles of a complex under a corepresented additive functor

Let `G : C ⥤ Ab` be an additive functor corepresented by `P`, for instance `Hom(P, -)`. For a
homological complex `K` in `C`, a cycle of the complex of abelian groups `G(K)` corresponds under
the corepresentation to a morphism `P ⟶ Kᵢ` killed by the differentials of `K`.

## Main results

* `HomologicalComplex.homEquiv_symm_iCycles_comp_d`: the morphism `P ⟶ Kᵢ` corresponding to a
  cycle of `G(K)` is a cocycle of `Hom(P, K)`.
-/

public section

open CategoryTheory

universe t v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c) {G : C ⥤ AddCommGrpCat.{t}} [G.Additive] {P : C}
  (R : (G ⋙ CategoryTheory.forget AddCommGrpCat).CorepresentableBy P)

/-- A cycle of `G(K)` corresponds under the corepresentation of `G` to a cocycle of `Hom(P, K)`. -/
lemma homEquiv_symm_iCycles_comp_d (i j : ι) (x : ((G.mapHomologicalComplex c).obj K).cycles i) :
    R.homEquiv.symm (((G.mapHomologicalComplex c).obj K).iCycles i x) ≫ K.d i j = 0 := by
  apply R.homEquiv.injective
  rw [R.homEquiv_comp, Equiv.apply_symm_apply, R.homEquiv_zero]
  simpa using ConcreteCategory.congr_hom (((G.mapHomologicalComplex c).obj K).iCycles_d i j) x

end HomologicalComplex
