/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Finitely generated modules over an Artinian ring have finite length

A finitely generated module over a left Artinian ring has finite length, which is one implication of
Mathlib's `IsArtinianRing.tfae`. The ring need not be commutative. The same holds over the base of
any finite extension, in particular for a finitely generated module over an Artin algebra.
-/

public section

universe u v w

namespace TauCeti

/-- A finitely generated module over an Artinian ring has finite length. -/
theorem isFiniteLength_of_finite (R : Type u) [Ring R] [IsArtinianRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsFiniteLength R M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- A module that is finitely generated over a finite extension `B` of an Artinian ring `R`, such as
an Artin `R`-algebra, has finite length over `R`. -/
theorem isFiniteLength_of_finite_trans (R : Type u) [Ring R] [IsArtinianRing R] (B : Type v)
    [Semiring B] [Module R B] [Module.Finite R B] (M : Type w) [AddCommGroup M] [Module R M]
    [Module B M] [IsScalarTower R B M] [Module.Finite B M] : IsFiniteLength R M :=
  have : Module.Finite R M := Module.Finite.trans B M
  isFiniteLength_of_finite R M

end TauCeti
