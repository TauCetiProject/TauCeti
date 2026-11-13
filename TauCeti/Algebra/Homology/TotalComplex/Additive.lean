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

The native direct-sum totalization functor is additive for any compatible complex shapes,
assuming the coproducts defining all the total complexes exist.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

instance : (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add {K L f g} := by
    -- Normalize the functor's object types so summandwise simplification can match.
    change total.map (f + g) c₁₂ = total.map f c₁₂ + total.map g c₁₂
    ext n : 1
    apply total.hom_ext
    intro p q hpq
    simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add,
      ιTotal_map, Preadditive.add_comp]

end HomologicalComplex₂
