/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Balanced
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric

/-!
# The twist of a braided pivotal category

A braided rigid category with a pivotal structure `φ : 𝟭 C ≅ (-)ᘁᘁ` is balanced. Its twist
compares the pivotal isomorphism with the Drinfeld isomorphism `u_X : X ≅ Xᘁᘁ` built from the
braiding: `θ_X = φ_X ≫ u_X⁻¹`. Unfolding `u_X⁻¹` (`TauCeti.drinfeldIso_inv_eq`) gives the explicit
formula
`θ_X = φ_X ≫ (𝟙_{Xᘁᘁ} ⊗ η_X) ≫ (β_{Xᘁᘁ, X} ⊗ 𝟙_{Xᘁ}) ≫ (𝟙_X ⊗ ε_{Xᘁ})`
of Henriques–Penneys–Tener, eq. (3), up to associators and unitors.

The balancing axiom holds because the pivotal isomorphism is monoidal, while the Drinfeld
isomorphism of `X ⊗ Y` differs from the tensor product of those of `X` and `Y` exactly by the
double braiding (`TauCeti.braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom`).

In a symmetric rigid category with its canonical pivotal structure, whose components are the
Drinfeld isomorphisms, the twist is trivial.

## Main declarations

* `TauCeti.balancedOfBraidedPivotal`: the balanced structure of a braided pivotal category;
* `TauCeti.balancedOfBraidedPivotal_twist_hom_app`: its twist is `φ_X ≫ u_X⁻¹`;
* `TauCeti.balancedOfBraidedPivotal_twist_eq_refl`: in a symmetric rigid category with its
  canonical pivotal structure, the twist is the identity.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1, eq. (3)
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section Braided

variable [BraidedCategory C] [RigidCategory C] [PivotalCategory C]

/-- The balanced structure of a braided pivotal category. Its twist `θ_X = φ_X ≫ u_X⁻¹` compares
the pivotal isomorphism `φ_X : X ≅ Xᘁᘁ` with the Drinfeld isomorphism `u_X : X ≅ Xᘁᘁ`. This is not
an instance: the twist depends on the chosen pivotal structure. -/
@[instance_reducible]
noncomputable def balancedOfBraidedPivotal : BalancedCategory C where
  twist := NatIso.ofComponents (fun X => pivotalIsoApp X ≪≫ (drinfeldIso X).symm) fun f => by
    simp [pivotalIsoApp_hom_naturality_assoc, drinfeldIso_inv_naturality]
  twist_tensor X Y := by
    -- The Drinfeld isomorphism of `X ⊗ Y` is that of `X` tensored with that of `Y`, after the
    -- inverse double braiding, while the pivotal isomorphism is monoidal.
    have h : (pivotalIsoApp (X ⊗ Y)).hom ≫ (drinfeldIso (X ⊗ Y)).inv =
        ((pivotalIsoApp X).hom ≫ (drinfeldIso X).inv ⊗ₘ (pivotalIsoApp Y).hom ≫
          (drinfeldIso Y).inv) ≫ (β_ X Y).hom ≫ (β_ Y X).hom := by
      -- The comparisons below are chained by `Eq.trans` rather than by rewriting, because they
      -- mix `Xᘁᘁ` with `(doubleRightDualFunctor C).obj X`, which agree only up to unfolding.
      rw [Iso.comp_inv_eq, Category.assoc, Category.assoc]
      refine (pivotalIsoApp_tensor_hom X Y).trans (Eq.trans ?_
        (congrArg (_ ≫ ·)
          (braiding_hom_comp_braiding_hom_comp_drinfeldIso_tensor_hom X Y)).symm)
      refine Eq.trans ?_ (Category.assoc _ _ _)
      congr 1
      simp
    simpa using h

variable {C}

/-- The twist of a braided pivotal category is the pivotal isomorphism followed by the inverse
Drinfeld isomorphism. -/
@[simp]
theorem balancedOfBraidedPivotal_twist_hom_app (X : C) :
    (balancedOfBraidedPivotal C).twist.hom.app X = (pivotalIsoApp X).hom ≫ (drinfeldIso X).inv :=
  (rfl)

/-- The inverse twist of a braided pivotal category is the Drinfeld isomorphism followed by the
inverse pivotal isomorphism. -/
@[simp]
theorem balancedOfBraidedPivotal_twist_inv_app (X : C) :
    (balancedOfBraidedPivotal C).twist.inv.app X = (drinfeldIso X).hom ≫ (pivotalIsoApp X).inv :=
  (rfl)

end Braided

/-- In a symmetric rigid category with its canonical pivotal structure, the twist is the
identity. -/
theorem balancedOfBraidedPivotal_twist_eq_refl [SymmetricCategory C] [RigidCategory C] :
    (balancedOfBraidedPivotal C).twist = Iso.refl (𝟭 C) := by
  ext X
  simp

end TauCeti
