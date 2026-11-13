/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.Double
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Mk

/-!
# The triangle of a two-term complex in the bounded homotopy category

For a morphism `g : X₀ ⟶ X₁`, the two-term complex `X₀ ⟶ X₁` in degrees `0` and `1` is degreewise
split by its top term. The resulting triangle `X₁[-1] ⟶ (X₀ ⟶ X₁) ⟶ X₀[0] ⟶ X₁[-1]⟦1⟧`, whose third
morphism is `g` up to `X₁[0] ≅ X₁[-1]⟦1⟧`, is distinguished in the bounded homotopy category `Kᵇ(C)`
(`TauCeti.HomotopyCategory.Bounded.double_distinguished`). It is the triangle of a degreewise split
sequence of complexes (`CochainComplex.trianglehOfDegreewiseSplit_distinguished`), read through the
classes `TauCeti.HomotopyCategory.Bounded.mk` and `TauCeti.HomotopyCategory.Bounded.mkMap` of
explicit complexes and chain maps.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace TauCeti.HomotopyCategory.Bounded

/-- **Splitting off the top term of a two-term complex is a distinguished triangle of `Kᵇ(C)`**:
the triangle `X₁[-1] ⟶ (X₀ ⟶ X₁) ⟶ X₀[0] ⟶ X₁[-1]⟦1⟧`, whose third morphism is `g` up to
`X₁[0] ≅ X₁[-1]⟦1⟧`. -/
theorem double_distinguished {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    Triangle.mk
      (mkMap (HomologicalComplex.doubleι₁ g ComplexShape.up_rel_zero_one zero_ne_one) :
        mk _ (CochainComplex.bounded_single 1 X₁) ⟶
          mk _ (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one))
      (mkMap (HomologicalComplex.doubleπ₀ g ComplexShape.up_rel_zero_one zero_ne_one) :
        mk _ (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one) ⟶
          mk _ (CochainComplex.bounded_single 0 X₀))
      ((mkMap ((HomologicalComplex.single C (.up ℤ) 0).map g) :
          mk _ (CochainComplex.bounded_single 0 X₀) ⟶
            mk _ (CochainComplex.bounded_single 0 X₁)) ≫
        (mkSingleIsoShift 1 0 1 (by simp) X₁).hom) ∈ distTriang _ := by
  -- The third morphism, mapped to the homotopy category, is the one of the split sequence.
  have h₃ : (ι C).map
      ((mkMap ((HomologicalComplex.single C (.up ℤ) 0).map g) :
          mk _ (CochainComplex.bounded_single 0 X₀) ⟶
            mk _ (CochainComplex.bounded_single 0 X₁)) ≫
        (mkSingleIsoShift 1 0 1 (by simp) X₁).hom) ≫
          ((ι C).commShiftIso (1 : ℤ)).hom.app (mk _ (CochainComplex.bounded_single 1 X₁)) =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map (CochainComplex.homOfDegreewiseSplit _
        (HomologicalComplex.doubleSplitting g ComplexShape.up_rel_zero_one zero_ne_one)) ≫
        ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ := by
    rw [Functor.map_comp, ι_map_mkMap, ι_map_mkSingleIsoShift_hom,
      ← HomologicalComplex.homOfDegreewiseSplit_doubleSplitting_comp_shiftIso g
        ComplexShape.up_rel_zero_one,
      ← Iso.app_hom ((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)) X₁]
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc, Iso.inv_hom_id_app]
    -- The identity sits on `(ι ⋙ shift).obj _`, which `Category.comp_id` matches only up to
    -- unfolding the composite functor.
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  rw [← (ι C).map_distinguished_iff]
  convert CochainComplex.trianglehOfDegreewiseSplit_distinguished _
    (HomologicalComplex.doubleSplitting g ComplexShape.up_rel_zero_one zero_ne_one) using 1
  -- Both triangles have the same objects and first two morphisms by definition.
  exact congrArg (Triangle.mk _ _) h₃

end TauCeti.HomotopyCategory.Bounded
