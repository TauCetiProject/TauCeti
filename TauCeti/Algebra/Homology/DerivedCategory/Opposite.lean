/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Opposite

import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import TauCeti.Algebra.Homology.CochainComplex.Opposite

/-!
# The derived category of the opposite abelian category

Reversing the direction of morphisms and the degrees of cochain complexes descends to an
equivalence from the opposite derived category to the derived category of the opposite category.
A single complex supported in degree `n` goes to a single complex supported in degree `-n`.
-/

public section

open CategoryTheory Opposite HomologicalComplex

namespace DerivedCategory

universe u v w₁ w₂

variable (C : Type u) [Category.{v} C] [Abelian C]

private theorem op_quasiIso_eq_inverseImage :
    (quasiIso C (ComplexShape.up ℤ)).op =
      (quasiIso Cᵒᵖ (ComplexShape.up ℤ)).inverseImage (CochainComplex.opEquivalence C).functor := by
  ext K L f
  exact (CochainComplex.quasiIso_opEquivalence_map_iff f.unop).symm

private noncomputable def opLocalizerMorphism :
    LocalizerMorphism (quasiIso C (ComplexShape.up ℤ)).op (quasiIso Cᵒᵖ (ComplexShape.up ℤ)) :=
  LocalizerMorphism.ofEq (op_quasiIso_eq_inverseImage C)

private instance : (opLocalizerMorphism C).functor.IsEquivalence :=
  inferInstanceAs (CochainComplex.opEquivalence C).functor.IsEquivalence

private instance : (opLocalizerMorphism C).IsLocalizedEquivalence := by
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  simp only [opLocalizerMorphism, LocalizerMorphism.ofEq_functor]
  rw [op_quasiIso_eq_inverseImage C]
  exact (MorphismProperty.map_inverseImage_eq_of_isEquivalence _ _).ge

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} Cᵒᵖ]

/-- The derived equivalence induced by reversing arrows and degrees of cochain complexes. -/
noncomputable def opEquivalence : (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ :=
  ((opLocalizerMorphism C).localizedFunctor Q.op Q).asEquivalence

/-- The opposite derived equivalence agrees with reversal of cochain complexes before
localization. -/
noncomputable def opEquivalenceCompQIso :
    (Q (C := C)).op ⋙ (opEquivalence C).functor ≅
      (CochainComplex.opEquivalence C).functor ⋙ Q :=
  (opLocalizerMorphism C).catCommSq _ _ |>.iso.symm

/-- The opposite derived equivalence sends a single complex in degree `n` to a single complex
in degree `-n`. -/
noncomputable def opEquivalenceSingleIso (n : ℤ) (X : C) :
    (opEquivalence C).functor.obj (op ((singleFunctor C n).obj X)) ≅
      (singleFunctor Cᵒᵖ (-n)).obj (op X) :=
  (opEquivalenceCompQIso C).app _ ≪≫ Q.mapIso (CochainComplex.opEquivalenceSingleIso n X)

end DerivedCategory
