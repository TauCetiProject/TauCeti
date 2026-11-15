/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Complexes with zero differentials as coproducts of single complexes

A homological complex whose differentials all vanish is the coproduct of its terms, each placed
in its own degree as a single complex (`HomologicalComplex.isColimitCofanSingleOfDEqZero`). The
legs of the coproduct are the morphisms from the single complexes given by the identity in each
degree. Properties of complexes which are stable under coproducts, such as K-flatness when
coproducts are exact, therefore pass from single complexes to complexes with zero differentials.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}

/-- A homological complex with zero differentials is the coproduct of its terms, each placed in
its own degree. -/
noncomputable def isColimitCofanSingleOfDEqZero (K : HomologicalComplex C c)
    (hK : ∀ i j, K.d i j = 0) :
    IsColimit (Cofan.mk K fun i ↦
      mkHomFromSingle (K := K) (j := i) (𝟙 (K.X i)) (fun _ _ ↦ by simp [hK])) := by
  refine isColimitOfEval _ _ fun p ↦
    (isColimitMapCoconeCofanMkEquiv (eval C c p) _ _).symm ?_
  refine Cofan.IsColimit.mk _ (fun t ↦ (singleObjXSelf c p (K.X p)).inv ≫ t.inj p) ?_ ?_
  · intro t i
    by_cases h : p = i
    · subst h
      simp
    · exact (isZero_single_obj_X c i (K.X i) p h).eq_of_src _ _
  · intro t m hm
    rw [← cancel_epi (singleObjXSelf c p (K.X p)).hom]
    simpa using hm p

end HomologicalComplex
