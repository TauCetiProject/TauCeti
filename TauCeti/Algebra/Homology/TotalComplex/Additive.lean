/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Additivity of totalization

Maps of native direct-sum total complexes preserve zero and addition whenever the source
and target totals exist. Consequently, totalization is an additive functor when all totals exist.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- The zero bicomplex morphism induces the zero morphism on total complexes. -/
@[simp]
lemma total.map_zero (K L : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [K.HasTotal c₁₂] [L.HasTotal c₁₂] : total.map (0 : K ⟶ L) c₁₂ = 0 := by
  ext n : 1
  apply total.hom_ext
  intro p q hpq
  simp

/-- Totalization preserves addition of bicomplex morphisms. -/
@[simp]
lemma total.map_add {K L : HomologicalComplex₂ C c₁ c₂} (f g : K ⟶ L)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [K.HasTotal c₁₂] [L.HasTotal c₁₂] :
    total.map (f + g) c₁₂ = total.map f c₁₂ + total.map g c₁₂ := by
  ext n : 1
  apply total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add,
    ιTotal_map, Preadditive.add_comp]

variable (C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

instance : (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add := total.map_add _ _ c₁₂

end HomologicalComplex₂
