/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# The quotient by the augmentation ideal

A Hopf ideal in the coordinate Hopf algebra of an affine group cuts out a closed subgroup, and
the augmentation ideal cuts out the identity subgroup. This file records the corresponding
identification of coordinate rings: the quotient of a commutative Hopf algebra by its augmentation
ideal is isomorphic to the base ring, which is the coordinate ring of the trivial affine group.
In particular, over any commutative ring `R` the quotient is a finite `R`-module, and when `R`
satisfies `[StrongRankCondition R]` it has rank `1`; for finite-type Hopf algebras this packages
into the categorical isomorphism `quotientAugmentationIso`.

The identification is the first isomorphism theorem for Hopf ideals. The augmentation ideal is
by definition the kernel Hopf ideal of the counit, and the counit is surjective because the unit
splits it, so the kernel quotient equivalence applies verbatim.

## Main declarations

* `TauCeti.HopfIdeal.quotientAugmentationIso`: the quotient by the augmentation ideal is the
  trivial finite-type Hopf algebra.
* `TauCeti.HopfIdeal.moduleFinite_quotient_augmentation`: over any commutative ring, the quotient
  of a commutative Hopf algebra by its augmentation ideal is a finite module.
* `TauCeti.HopfIdeal.finrank_quotient_augmentation`: over any commutative ring satisfying
  `StrongRankCondition`, the quotient of a commutative Hopf algebra by its augmentation ideal has
  rank `1`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), around Proposition 4.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

noncomputable section

namespace HopfIdeal

variable {k : Type u} [CommRing k]

/-- The quotient by the augmentation ideal is the trivial finite-type Hopf algebra. -/
def quotientAugmentationIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.quotient H (augmentation k H) ≅
      FiniteTypeCommHopfAlgCat.of k k := by
  rw [augmentation_def]
  exact ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    kerLiftBialgEquiv (Bialgebra.counitBialgHom k H) Bialgebra.counit_surjective

/-- The quotient map followed by the quotient-augmentation isomorphism is the counit. -/
@[simp]
theorem mkQuotient_comp_quotientAugmentationIso_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.mkQuotient H (augmentation k H) ≫
        (quotientAugmentationIso H).hom =
      FiniteTypeCommHopfAlgCat.ofHom (Bialgebra.counitBialgHom k H) := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  ext

/-- Over any commutative ring, the quotient of a commutative Hopf algebra by its augmentation
ideal is a finite module (isomorphic to the base ring). -/
theorem moduleFinite_quotient_augmentation {R : Type u} [CommRing R]
    (A : _root_.CommHopfAlgCat.{v} R) :
    Module.Finite R (_root_.CommHopfAlgCat.quotient A (augmentation R A)) := by
  rw [augmentation_def]
  exact Module.Finite.equiv (kerLiftBialgEquiv (Bialgebra.counitBialgHom R A)
    Bialgebra.counit_surjective).symm.toAlgEquiv.toLinearEquiv

/-- Over any commutative ring satisfying the strong rank condition, the quotient of a commutative
Hopf algebra by its augmentation ideal has rank `1`. -/
@[simp] theorem finrank_quotient_augmentation {R : Type u} [CommRing R] [StrongRankCondition R]
    (A : _root_.CommHopfAlgCat.{v} R) :
    Module.finrank R (_root_.CommHopfAlgCat.quotient A (augmentation R A)) = 1 := by
  rw [augmentation_def]
  exact (kerLiftBialgEquiv (Bialgebra.counitBialgHom R A)
    Bialgebra.counit_surjective).toAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self R)

end HopfIdeal

end

end TauCeti
