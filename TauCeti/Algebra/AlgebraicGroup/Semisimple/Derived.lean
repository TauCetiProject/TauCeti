/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.CommutativeImage
public import TauCeti.Algebra.AlgebraicGroup.Derived.Perfect

/-!
# Semisimple groups equal their derived subgroup in characteristic zero

A semisimple affine group over a characteristic-zero field is scheme-theoretically perfect:
its derived defining ideal is zero, and the canonical inclusion of its derived group scheme
is an isomorphism. No algebraic-closure or splitness assumption on the ground field is needed.
This does not assert that its group of rational points is perfect.

The input is the vanishing of commutative images from `Semisimple.CommutativeImage`.
The criterion in `Derived.Perfect` then applies to the affine abelianization.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.
-/

public section

open CategoryTheory

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A semisimple affine group over a characteristic-zero field equals its scheme-theoretic
derived subgroup. Zero is the defining ideal of the whole group. -/
theorem derivedDefiningIdeal_eq_bot (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.derivedDefiningIdeal (R := k) H.obj = ⊥ := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact (_root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_iff_forall_hom_eq_unit_comp_counit
    H.obj).mpr fun _ _ f ↦ hH.hom_eq_unit_comp_counit f

/-- The canonical closed inclusion of the derived group scheme of a semisimple affine group
is an isomorphism in characteristic zero. -/
theorem isIso_derivedGroupSchemeι (hH : semisimpleCommHopfAlgProperty k H) :
    IsIso (CommHopfAlgCat.derivedGroupSchemeι H.obj) := by
  have hquot (I : HopfIdeal k H) (hI : I = ⊥) :
      IsIso (CommHopfAlgCat.mkQuotient H.obj I) := by
    subst I
    rw [← _root_.CommHopfAlgCat.quotientBotIso_inv]
    infer_instance
  let _ := hquot _ hH.derivedDefiningIdeal_eq_bot
  dsimp only [CommHopfAlgCat.derivedGroupSchemeι]
  rw [CommHopfAlgCat.quotientSpecι_def]
  infer_instance

end TauCeti.semisimpleCommHopfAlgProperty
