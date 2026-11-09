/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Ribbon.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Nondegenerate

/-!
# Spherical semisimple categories are ribbon

In a finite semisimple braided pivotal category over an algebraically closed field, with
simple unit, sphericity forces the associated twist to commute with duality. The key identity
compares the two traces after inserting the twist on the object or on its dual. Nondegeneracy
of the trace pairing then turns this scalar identity into equality of morphisms.

The semisimplicity hypothesis is essential: without it a spherical pivotal structure need
not induce a ribbon twist. Only finite-dimensional endomorphism spaces of simple objects
are needed, not finitely many simple classes or characteristic zero.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937),
  Appendix A.2, Proposition A.4
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

section Balanced

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [BalancedCategory C]

-- These traces refer to the pivotal structure associated to the specified twist.
attribute [local instance] pivotalOfBalanced

section Semisimple

variable (k : Type*) [Field k] [IsAlgClosed k]
  [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

/-- A twist on a split finite semisimple category with simple unit is ribbon if and only if
its associated pivotal structure is spherical. -/
theorem sphericalCategory_pivotalOfBalanced_iff_ribbonCategory :
    SphericalCategory C ↔ RibbonCategory C := by
  refine ⟨fun hs => ?_, fun _ => sphericalCategory_pivotalOfBalanced⟩
  let := hs
  constructor
  intro X
  have h : BalancedCategory.twist.hom.app X =
      ExactPairing.leftMate (inferInstance : ExactPairing X Xᘁ)
        (inferInstance : ExactPairing X Xᘁ) (BalancedCategory.twist.hom.app (Xᘁ : C)) := by
    apply sub_eq_zero.mp
    apply (forall_rightTrace_comp_eq_zero_iff (hfin := hfin) k _).mp
    intro f
    rw [Preadditive.sub_comp, rightTrace_sub, sub_eq_zero, ← leftTrace_twist_comp (X := X),
      SphericalCategory.leftTrace_eq_rightTrace]
  apply ExactPairing.rightHom_ext (X := X) (Y := Xᘁ)
  rw [rightAdjointMate_comp_evaluation (X := X) (Y := X)
    (BalancedCategory.twist.hom.app X), h, ExactPairing.leftMate_comp_evaluation]

end Semisimple

end Balanced

section Spherical

variable (k : Type*) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C]
  [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

/-- In a split finite semisimple braided pivotal category with simple unit, the twist
associated to the pivotal structure is ribbon exactly when that structure is spherical. -/
theorem sphericalCategory_iff_ribbonCategory :
    SphericalCategory C ↔ (letI := balancedOfBraidedPivotal C; RibbonCategory C) := by
  let := balancedOfBraidedPivotal C
  have h := sphericalCategory_pivotalOfBalanced_iff_ribbonCategory (C := C) (hfin := hfin) k
  rwa [pivotalOfBalanced_balancedOfBraidedPivotal] at h

/-- The twist induced by a spherical structure on a split finite semisimple braided category
with simple unit is ribbon. The balanced structure here is the induced one, not an arbitrary
choice of twist. -/
theorem ribbonCategory_of_sphericalCategory [SphericalCategory C] :
    letI := balancedOfBraidedPivotal C
    RibbonCategory C :=
  (sphericalCategory_iff_ribbonCategory (hfin := hfin) k).mp inferInstance

end Spherical

end TauCeti
