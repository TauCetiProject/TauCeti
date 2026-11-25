/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# The quotient by the augmentation ideal

A Hopf ideal in the coordinate Hopf algebra of an affine group cuts out a closed subgroup, and
the augmentation ideal cuts out the identity subgroup. This file records the corresponding
identification of coordinate rings: the quotient of a finite-type commutative Hopf algebra by
its augmentation ideal is the base field, which is the coordinate ring of the trivial affine
group.

The identification is the first isomorphism theorem for Hopf ideals. The augmentation ideal is
by definition the kernel Hopf ideal of the counit, and the counit is surjective because the unit
splits it, so the kernel quotient equivalence applies verbatim.

## Main declarations

* `TauCeti.HopfIdeal.quotientAugmentationIso`: the quotient by the augmentation ideal is the
  trivial finite-type Hopf algebra.
* `TauCeti.HopfIdeal.augmentation_quotient_eq_bot_iff`: the closed subgroup cut out by a Hopf
  ideal is trivial exactly when the Hopf ideal is the augmentation ideal.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), around Proposition 4.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

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

/-- The coordinate Hopf algebra `H ⧸ I` of the closed subgroup cut out by a Hopf ideal `I` has
zero augmentation ideal, so that the subgroup is trivial, exactly when `I` is the augmentation
ideal of `H`. -/
theorem augmentation_quotient_eq_bot_iff {H : Type*} [CommRing H] [HopfAlgebra k H]
    (I : HopfIdeal k H) : augmentation k (H ⧸ I.toIdeal) = ⊥ ↔ I = augmentation k H := by
  constructor
  · intro h
    refine le_antisymm (le_augmentation k H I) fun x hx ↦ ?_
    have hmk : Ideal.Quotient.mk I.toIdeal x ∈ augmentation k (H ⧸ I.toIdeal) := by
      rw [mem_augmentation, Bialgebra.Quotient.counit_mk]
      exact (mem_augmentation k H).mp hx
    rw [h, mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact mem_toIdeal.mp hmk
  · rintro rfl
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mem_augmentation, Bialgebra.Quotient.counit_mk, mem_bot, Ideal.Quotient.eq_zero_iff_mem,
      mem_toIdeal, mem_augmentation]

end HopfIdeal

end

end TauCeti
