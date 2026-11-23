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

In a finite semisimple braided pivotal category, linear over a commutative semiring `R`, in which
every simple object has scalar endomorphisms over `R`, sphericity forces the associated twist to
commute with duality. The key identity compares the two traces after inserting the twist on the
object or on its dual. Nondegeneracy of the trace pairing then turns this scalar identity into
equality of morphisms.

The semisimplicity hypothesis is essential: without it a spherical pivotal structure need
not induce a ribbon twist. Neither a simple unit, nor finitely many simple classes, nor a
characteristic assumption is needed. Over an algebraically closed field, simple objects with
finite-dimensional endomorphisms have scalar endomorphisms by Schur's lemma
(`TauCeti.bijective_algebraMap_end_of_simple`).

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

variable {R : Type*} [CommSemiring R]
  [Abelian C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C]
  (hR : ∀ (S : C) [Simple S], Function.Surjective (algebraMap R (End S)))

include hR

/-- A twist on a finite semisimple category whose simple objects have scalar endomorphisms is
ribbon if and only if its associated pivotal structure is spherical. -/
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
    apply (forall_rightTrace_comp_eq_zero_iff hR _).mp
    intro f
    rw [Preadditive.sub_comp, rightTrace_sub, sub_eq_zero, ← leftTrace_twist_comp (X := X),
      SphericalCategory.leftTrace_eq_rightTrace]
  apply ExactPairing.rightHom_ext (X := X) (Y := Xᘁ)
  rw [rightAdjointMate_comp_evaluation (X := X) (Y := X)
    (BalancedCategory.twist.hom.app X), h, ExactPairing.leftMate_comp_evaluation]

end Semisimple

end Balanced

section Spherical

variable {R : Type*} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C]
  [Abelian C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C]
  (hR : ∀ (S : C) [Simple S], Function.Surjective (algebraMap R (End S)))

include hR

/-- In a finite semisimple braided pivotal category whose simple objects have scalar
endomorphisms, the twist associated to the pivotal structure is ribbon exactly when that
structure is spherical. -/
theorem sphericalCategory_iff_ribbonCategory :
    SphericalCategory C ↔ (letI := balancedOfBraidedPivotal C; RibbonCategory C) := by
  let := balancedOfBraidedPivotal C
  have h := sphericalCategory_pivotalOfBalanced_iff_ribbonCategory (C := C) hR
  rwa [pivotalOfBalanced_balancedOfBraidedPivotal] at h

/-- **Spherical implies ribbon.** The twist induced by a spherical structure on a finite
semisimple braided category whose simple objects have scalar endomorphisms is ribbon. The balanced
structure here is the induced one, not an arbitrary choice of twist. -/
theorem ribbonCategory_of_sphericalCategory [SphericalCategory C] :
    letI := balancedOfBraidedPivotal C
    RibbonCategory C :=
  (sphericalCategory_iff_ribbonCategory hR).mp inferInstance

end Spherical

end TauCeti
