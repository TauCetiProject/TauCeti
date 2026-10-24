/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import TauCeti.RingTheory.Jacobson.Basic
public import TauCeti.RingTheory.LocalRing.Basic

/-!
# The residue division ring of a local ring

The Jacobson radical of a local ring `R` — not assumed commutative — is its set of non-units
(`TauCeti.IsLocalRing.mem_jacobson_iff_not_isUnit`), so the quotient `R ⧸ Ring.jacobson R` is a
**division ring**. This file proves that and installs the division-ring structure on the quotient,
the noncommutative counterpart of Mathlib's `IsLocalRing.ResidueField`, which is a `Field` but is
available only over a commutative base.

The residue division ring is the coefficient ring the irreducible morphisms of a category are
counted over: the space of irreducible morphisms `rad(X, Y) / rad²(X, Y)` between two objects with
local endomorphism rings is a bimodule over `End X ⧸ rad(End X)` and `End Y ⧸ rad(End Y)`, and the
textbook convention recalled in the references below counts the arrows of a *valued*
Auslander-Reiten quiver by the rank over one of those division rings, the target's, rather than by
a rank over an ambient base ring. The two ranks are different invariants in general, and neither
this file nor the bimodule file computes either of them. The bimodule is built in
`TauCeti/CategoryTheory/Preadditive/Radical/Bimodule.lean`.

## Main results

* `TauCeti.IsLocalRing.mem_jacobson_iff_not_isUnit`: **the Jacobson radical of a local ring is its
  set of non-units.**
* `TauCeti.IsLocalRing.instDivisionRingQuotientJacobson`: **the quotient of a local ring by its
  Jacobson radical is a division ring.**
* `TauCeti.IsLocalRing.mk_jacobson_eq_zero_iff` and `TauCeti.IsLocalRing.isUnit_mk_jacobson_iff`: a
  residue class vanishes exactly on the non-units and is a unit exactly on the units.

## Implementation notes

A local ring is Dedekind-finite (`TauCeti.IsLocalRing.isDedekindFiniteMonoid`), so an element
with a one-sided inverse is already a unit by Mathlib's `IsUnit.of_mul_eq_one_right`; that is the
step the proof below needs, and it is why the only thing membership in the radical has to supply
is a one-sided inverse.

`TauCeti.IsLocalRing.isUnit_mk_jacobson_iff` carries no `simp` attribute: the quotient is a
division ring, so `simp` already rewrites its left-hand side through `isUnit_iff_ne_zero` and
`TauCeti.IsLocalRing.mk_jacobson_eq_zero_iff`.

## References

* N. Jacobson, *Structure of Rings*, AMS Colloquium Publications 37 (1956), Chapter I.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections I.4 and V.7, where the residue division ring of a local
  endomorphism ring is the coefficient ring the irreducible morphisms are counted over.
-/

public section

namespace TauCeti

namespace IsLocalRing

variable {R : Type*} [Ring R] [IsLocalRing R]

/-- **The Jacobson radical of a local ring is its set of non-units.** -/
theorem mem_jacobson_iff_not_isUnit {x : R} : x ∈ Ring.jacobson R ↔ ¬ IsUnit x := by
  constructor
  · rintro hx ⟨u, rfl⟩
    have hz := Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mp hx (-(↑u⁻¹ : R))
    rw [neg_mul, u.inv_mul, add_neg_cancel] at hz
    exact not_isUnit_zero hz
  · intro hx
    refine Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mpr fun y => ?_
    have hsum : IsUnit ((1 + y * x) + -(y * x)) := by simp
    rcases _root_.IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
    · exact hu
    · obtain ⟨u, hu⟩ := hu
      refine absurd (IsUnit.of_mul_eq_one_right (-((↑u⁻¹ : R) * y)) ?_) hx
      have hstep : -((↑u⁻¹ : R) * y) * x = (↑u⁻¹ : R) * -(y * x) := by noncomm_ring
      rw [hstep, ← hu, u.inv_mul]

/-- **A residue class modulo the Jacobson radical vanishes exactly on the non-units.** -/
@[simp]
theorem mk_jacobson_eq_zero_iff {x : R} :
    Ideal.Quotient.mk (Ring.jacobson R) x = 0 ↔ ¬ IsUnit x :=
  Ideal.Quotient.eq_zero_iff_mem.trans mem_jacobson_iff_not_isUnit

/-- **A residue class modulo the Jacobson radical is a unit exactly on the units.** -/
theorem isUnit_mk_jacobson_iff {x : R} :
    IsUnit (Ideal.Quotient.mk (Ring.jacobson R) x) ↔ IsUnit x := by
  refine ⟨fun hu => not_not.mp fun hx => ?_, fun hx => hx.map _⟩
  exact not_isUnit_zero (mk_jacobson_eq_zero_iff.mpr hx ▸ hu)

variable (R) in
/-- **The quotient of a local ring by its Jacobson radical is a division ring**: every class is
either the class of a unit, hence a unit, or the class of a non-unit, hence zero. This is the
noncommutative form of Mathlib's `IsLocalRing.ResidueField` being a field. -/
noncomputable instance instDivisionRingQuotientJacobson :
    DivisionRing (R ⧸ Ring.jacobson R) :=
  DivisionRing.ofIsUnitOrEqZero fun a => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ring.jacobson R) a
    by_cases hx : IsUnit x
    · exact Or.inl (isUnit_mk_jacobson_iff.mpr hx)
    · exact Or.inr (mk_jacobson_eq_zero_iff.mpr hx)

end IsLocalRing

end TauCeti
