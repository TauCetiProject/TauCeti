/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Balanced

/-!
# Pivotal structures from balanced structures

On a braided rigid category, balanced structures and pivotal structures determine each other.
If `u_X : X ≅ Xᘁᘁ` is the Drinfeld isomorphism, a twist `θ` gives the pivotal isomorphism
`φ_X = θ_X ≫ u_X`. The balancing axiom cancels the failure of `u` to be monoidal.
Conversely, the twist associated to a pivotal structure is `θ_X = φ_X ≫ u_X⁻¹`.

This file constructs the inverse of `balancedOfBraidedPivotal`, proves both round trips as
equalities of structures, and packages them as `pivotalBalancedEquiv`. No semisimplicity,
sphericity, or compatibility of the twist with duals is required.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1,
  equation (3) and Appendix A.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory Functor.LaxMonoidal

universe v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C]

/-- The pivotal structure associated to a balanced rigid category: its pivotal isomorphism is
its twist followed by the Drinfeld isomorphism. This is not an instance, since it depends on
the chosen twist. -/
@[instance_reducible]
noncomputable def pivotalOfBalanced [BalancedCategory C] : PivotalCategory C where
  -- Explicit components keep the comparison with `Xᘁᘁ` available without unfolding the
  -- double-dual functor. Compose equalities at default transparency: rewriting and `simp`
  -- cannot in general identify that object with the functor's wrapped object.
  pivotalIso := NatIso.ofComponents
    (fun X => BalancedCategory.twist.app X ≪≫ drinfeldIso X) fun f =>
      (BalancedCategory.twist.hom.naturality_assoc f _).trans
        ((congrArg (fun g => BalancedCategory.twist.hom.app _ ≫ g)
          (drinfeldIso_hom_naturality f)).trans (Category.assoc _ _ _).symm)
  pivotalIso_isMonoidal :=
    { unit := (Category.id_comp _).trans
        ((congrArg (· ≫ _) BalancedCategory.twist_hom_app_unit).trans
          ((Category.id_comp _).trans drinfeldIso_unit_hom))
      tensor X Y := by
        -- The identity functor's tensor comparison is the identity. The Drinfeld tensor
        -- identity uses explicit double duals, so compose it before simplifying the wrappers.
        calc
          _ = (BalancedCategory.twist.hom.app X ⊗ₘ BalancedCategory.twist.hom.app Y) ≫
              (β_ X Y).hom ≫ (β_ Y X).hom ≫ (drinfeldIso (X ⊗ Y)).hom :=
            (Category.id_comp _).trans
              ((congrArg (· ≫ _) (BalancedCategory.twist_tensor X Y)).trans
                ((Category.assoc _ _ _).trans
                  (congrArg (fun f =>
                    (BalancedCategory.twist.hom.app X ⊗ₘ BalancedCategory.twist.hom.app Y) ≫ f)
                    (Category.assoc _ _ _))))
          _ = _ := by
            rw [braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom]
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ μ (doubleRightDualFunctor C) X Y)
                (tensorHom_comp_tensorHom _ _ _ _)) }

variable {C}

/-- The pivotal isomorphism obtained from a twist is `θ_X ≫ u_X`. -/
@[simp]
theorem pivotalOfBalanced_pivotalIsoApp_hom [BalancedCategory C] (X : C) :
    (@pivotalIsoApp C _ _ _ (pivotalOfBalanced C) X).hom =
      BalancedCategory.twist.hom.app X ≫ (drinfeldIso X).hom :=
  (@pivotalIso_hom_app C _ _ _ (pivotalOfBalanced C) X).symm.trans (by rfl)

/-- The inverse pivotal isomorphism obtained from a twist is `u_X⁻¹ ≫ θ_X⁻¹`. -/
@[simp]
theorem pivotalOfBalanced_pivotalIsoApp_inv [BalancedCategory C] (X : C) :
    (@pivotalIsoApp C _ _ _ (pivotalOfBalanced C) X).inv =
      (drinfeldIso X).inv ≫ BalancedCategory.twist.inv.app X :=
  (@pivotalIso_inv_app C _ _ _ (pivotalOfBalanced C) X).symm.trans (by rfl)

/-- Passing from a pivotal structure to its twist and back recovers the pivotal structure. -/
@[simp]
theorem pivotalOfBalanced_balancedOfBraidedPivotal (P : PivotalCategory C) :
    @pivotalOfBalanced C _ _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ P) = P := by
  apply PivotalCategory.ext
  ext X
  simp only [pivotalIso_hom_app, pivotalOfBalanced_pivotalIsoApp_hom,
    balancedOfBraidedPivotal_twist_hom_app, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Passing from a twist to its pivotal structure and back recovers the balanced structure. -/
@[simp]
theorem balancedOfBraidedPivotal_pivotalOfBalanced (B : BalancedCategory C) :
    @balancedOfBraidedPivotal C _ _ _ _ (@pivotalOfBalanced C _ _ _ _ B) = B := by
  let := B
  apply BalancedCategory.ext
  ext X
  -- Keep the new pivotal instance explicit, and bridge its functor-valued component to the
  -- explicit double dual before cancelling the Drinfeld isomorphism.
  exact (@balancedOfBraidedPivotal_twist_hom_app C _ _ _ _ (pivotalOfBalanced C) X).trans
    ((congrArg (· ≫ (drinfeldIso X).inv)
      (pivotalOfBalanced_pivotalIsoApp_hom X)).trans (by simp))

/-- Pivotal structures on a braided rigid category correspond to balanced structures via
`θ_X = φ_X ≫ u_X⁻¹`, with inverse `φ_X = θ_X ≫ u_X`. -/
noncomputable def pivotalBalancedEquiv (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RigidCategory C] : PivotalCategory C ≃ BalancedCategory C where
  toFun P := @balancedOfBraidedPivotal C _ _ _ _ P
  invFun B := @pivotalOfBalanced C _ _ _ _ B
  left_inv := pivotalOfBalanced_balancedOfBraidedPivotal
  right_inv := balancedOfBraidedPivotal_pivotalOfBalanced

/-- The forward map of the correspondence constructs the twist of a pivotal structure. -/
@[simp]
theorem pivotalBalancedEquiv_apply (P : PivotalCategory C) :
    pivotalBalancedEquiv C P = @balancedOfBraidedPivotal C _ _ _ _ P :=
  (rfl)

/-- The inverse correspondence constructs the pivotal structure of a twist. -/
@[simp]
theorem pivotalBalancedEquiv_symm_apply (B : BalancedCategory C) :
    (pivotalBalancedEquiv C).symm B = @pivotalOfBalanced C _ _ _ _ B :=
  (rfl)

end TauCeti
