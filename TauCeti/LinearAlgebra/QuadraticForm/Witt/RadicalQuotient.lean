/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Isometries of the regular quotient of a quadratic form

An isometry carries the radical of a quadratic form onto the radical of its target. It therefore
induces an isometry on the quotients by the radicals. Over a field in which two is invertible,
these quotient forms are regular, even if the original forms are degenerate.

This gives the intrinsic regular part used to compare Witt decompositions of degenerate forms:
isometric forms have isometric regular quotients, and hence the same regular-form class.

## Main results

* `QuadraticMap.IsometryEquiv.quotientRadical`: the induced isometry on the radical quotients.
* `QuadraticMap.Equivalent.lift_radical`: equivalent forms have equivalent regular quotients.
* `TauCeti.formClass_lift_radical_eq_of_equivalent`: their regular quotients have equal classes.
-/

public section

namespace QuadraticMap

universe u v w

variable {K : Type u} [Field K] {V : Type v} {W : Type w}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {R : QuadraticForm K W}

/-- An isometry of quadratic forms descends to an isometry of their quotients by the radical. -/
noncomputable def IsometryEquiv.quotientRadical (e : Q.IsometryEquiv R) :
    (Q.lift Q.radical le_rfl).IsometryEquiv (R.lift R.radical le_rfl) where
  __ := Submodule.Quotient.equiv Q.radical R.radical e.toLinearEquiv e.map_radical
  map_app' x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [Submodule.Quotient.equiv_apply, QuadraticMap.lift_mk]

/-- The quotient isometry sends the class of a vector to the class of its image. -/
@[simp]
theorem IsometryEquiv.quotientRadical_mk (e : Q.IsometryEquiv R) (x : V) :
    e.quotientRadical (Submodule.Quotient.mk x : V ⧸ Q.radical) =
      (Submodule.Quotient.mk (e x) : W ⧸ R.radical) := by
  dsimp [IsometryEquiv.quotientRadical]
  rfl

/-- Equivalent quadratic forms have equivalent quotients by their radicals. -/
theorem Equivalent.lift_radical (h : Q.Equivalent R) :
    (Q.lift Q.radical le_rfl).Equivalent (R.lift R.radical le_rfl) := by
  obtain ⟨e⟩ := h
  exact ⟨e.quotientRadical⟩

end QuadraticMap

namespace TauCeti

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} {W : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K V} {R : QuadraticForm K W}

/-- Isometric forms, including degenerate ones, have the same isometry class after quotienting
by their radicals. -/
theorem formClass_lift_radical_eq_of_equivalent (h : Q.Equivalent R) :
    formClass (Q.lift Q.radical le_rfl) Q.nondegenerate_lift_radical =
      formClass (R.lift R.radical le_rfl) R.nondegenerate_lift_radical :=
  (formClass_eq_iff _ _ _ _).2 h.lift_radical

end TauCeti
