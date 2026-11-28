/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.RingTheory.Morita.Basic

/-!
# Morita classes of algebras

Quotient a family of algebras over a fixed commutative ring by Morita equivalence. The family is
specified by a predicate on bundled algebras.
-/

public section

namespace TauCeti

universe u

variable (R : Type*) [CommRing R] (P : AlgCat.{u} R → Prop)

/-- Morita equivalence over `R` as a setoid on the algebras satisfying `P`. -/
def moritaSetoid : Setoid {A : AlgCat.{u} R // P A} where
  r A B := IsMoritaEquivalent R A.val B.val
  iseqv := ⟨fun A ↦ .refl R A.val, .symm R, .trans R⟩

/-- The relation in `moritaSetoid` is Morita equivalence of the underlying algebras. -/
@[simp]
theorem moritaSetoid_rel_iff (A B : {A : AlgCat.{u} R // P A}) :
    (moritaSetoid R P).r A B ↔ IsMoritaEquivalent R A.val B.val :=
  Iff.rfl

end TauCeti
