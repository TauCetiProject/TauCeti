/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Balanced.Functor
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.OfBalanced

/-!
# Balanced and pivotal preservation

For a strong braided monoidal functor between braided pivotal categories, preserving the
associated twists is equivalent to preserving the pivotal isomorphisms. The same assertion
holds in the reverse direction, for the pivotal structures induced by chosen twists.
Together these give the functor-level preservation criterion for `pivotalBalancedEquiv`.

Writing `δ_X = F.mapRightDualIso X : F.obj Xᘁ ≅ (F.obj X)ᘁ`, the pivotal preservation equation
is `F.map j_X ≫ δ_{Xᘁ} = j_{F X} ≫ (δ_X)ᘁ`, where `j` denotes the pivotal isomorphisms.
This retains the chosen duals without identifying double duals with the original objects or
assuming ribbon compatibility. Preservation also transports along natural isomorphisms of
braided functors, with no monoidality assumption on the isomorphism.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1,
  equation (3)
-/

public section

open CategoryTheory MonoidalCategory TauCeti

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [RigidCategory D]

section Pivotal

variable [PivotalCategory C] [PivotalCategory D]
variable (F : C ⥤ D) [F.Braided]

/-- At an object, preserving the twist induced by the pivotal structure is equivalent to
preserving its pivotal isomorphism through the canonical chosen-dual comparisons. -/
theorem map_balancedOfBraidedPivotal_twist_iff (X : C) :
    F.map ((balancedOfBraidedPivotal C).twist.hom.app X) =
        (balancedOfBraidedPivotal D).twist.hom.app (F.obj X) ↔
      F.map (pivotalIsoApp X).hom ≫ (F.mapRightDualIso Xᘁ).hom =
        (pivotalIsoApp (F.obj X)).hom ≫ ((F.mapRightDualIso X).hom)ᘁ := by
  -- Use mapRightDualIso and map_drinfeldIso_hom_comp_mapRightDualIso_hom.
  -- Postcompose with the image Drinfeld isomorphism and the dual comparison, so that
  -- inverse Drinfeld factors cancel on both sides of the twist equation.
  rw [← cancel_mono (F.map (drinfeldIso X).hom ≫ (F.mapRightDualIso Xᘁ).hom)]
  simp only [balancedOfBraidedPivotal_twist_hom_app, F.map_comp, Category.assoc]
  have h := (F.mapIso (drinfeldIso X)).inv_hom_id
  simp only [Functor.mapIso_inv, Functor.mapIso_hom] at h
  rw [reassoc_of% h, F.map_drinfeldIso_hom_comp_mapRightDualIso_hom]
  simp only [Iso.inv_hom_id_assoc]

/-- For the twists corresponding to the chosen pivotal structures, a strong braided functor
is balanced if and only if it is pivotal. The balanced structures are explicit local choices. -/
theorem isBalanced_iff_isPivotal :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    F.IsBalanced ↔ F.IsPivotal := by
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  constructor
  · intro h
    exact IsPivotal.mk' fun X =>
      (F.map_balancedOfBraidedPivotal_twist_iff X).mp (h.map_twist_hom_app X)
  · intro h
    exact ⟨fun X => (F.map_balancedOfBraidedPivotal_twist_iff X).mpr
      (F.map_pivotalIsoApp_hom_comp_mapRightDualIso_hom X)⟩

variable {F} {G : C ⥤ D} [G.Braided]

/-- Naturally isomorphic braided functors preserve the pivotal structures simultaneously.
No monoidality assumption on the natural isomorphism is required. -/
theorem isPivotal_iff_of_iso (e : F ≅ G) : F.IsPivotal ↔ G.IsPivotal := by
  -- Transport twist preservation, then apply the pivotal preservation criterion.
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  exact (F.isBalanced_iff_isPivotal).symm.trans
    ((isBalanced_iff_of_iso e).trans G.isBalanced_iff_isPivotal)

end Pivotal

/-- For the pivotal structures induced by chosen twists, pivotal preservation is equivalent
to twist preservation. No compatibility of either twist with duals is required. -/
theorem isPivotal_pivotalOfBalanced_iff [BalancedCategory C] [BalancedCategory D]
    (F : C ⥤ D) [F.Braided] :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    F.IsPivotal ↔ F.IsBalanced := by
  let := pivotalOfBalanced C
  let := pivotalOfBalanced D
  have h := F.isBalanced_iff_isPivotal
  rw [balancedOfBraidedPivotal_pivotalOfBalanced,
    balancedOfBraidedPivotal_pivotalOfBalanced] at h
  exact h.symm

end CategoryTheory.Functor
