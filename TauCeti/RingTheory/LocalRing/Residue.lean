/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import TauCeti.RingTheory.Jacobson.MulOpposite
public import TauCeti.RingTheory.LocalRing.Basic

/-!
# The residue division ring of a local ring

The Jacobson radical of a local ring `R` — not assumed commutative — is its set of non-units
(`TauCeti.IsLocalRing.mem_jacobson_iff_not_isUnit`), so the quotient `R ⧸ Ring.jacobson R` is a
**division ring**: a class is either the class of a unit, hence a unit, or the class of a non-unit,
hence zero. This file proves that and installs the division-ring structure on the quotient, the
noncommutative counterpart of Mathlib's `IsLocalRing.ResidueField`, which is a `Field` but is
available only over a commutative base.

Everything rests on one observation: in a local ring an element with a one-sided inverse is a unit
(`TauCeti.IsLocalRing.isUnit_of_mul_eq_one_left`), because the composite in the other order is an
idempotent and a local ring has no idempotent besides `0` and `1`. That makes the non-units closed
under multiplication on either side, which is what puts each of them in the Jacobson radical.

The residue division ring is what counts the arrows of an Auslander-Reiten quiver: the space of
irreducible morphisms `rad(X, Y) / rad²(X, Y)` between two objects with local endomorphism rings is
a bimodule over `End X ⧸ rad(End X)` and `End Y ⧸ rad(End Y)`, and it is the dimensions over those
division rings, not over an ambient base ring, that are the arrow multiplicities. The bimodule is
built in `TauCeti/CategoryTheory/Preadditive/Radical/Bimodule.lean`.

## Main results

* `TauCeti.IsLocalRing.isUnit_of_mul_eq_one_left` and
  `TauCeti.IsLocalRing.isUnit_of_mul_eq_one_right`: a one-sided inverse in a local ring is a
  two-sided one.
* `TauCeti.IsLocalRing.mem_jacobson_iff_not_isUnit`: **the Jacobson radical of a local ring is its
  set of non-units.**
* `TauCeti.IsLocalRing.instDivisionRingQuotientJacobson`: **the quotient of a local ring by its
  Jacobson radical is a division ring.**
* `TauCeti.IsLocalRing.mk_jacobson_eq_zero_iff` and `TauCeti.IsLocalRing.isUnit_mk_jacobson_iff`: a
  residue class vanishes exactly on the non-units and is a unit exactly on the units.

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

/-- **An element of a local ring with a left inverse is a unit.** The product `x * a` of the two
factors in the other order is idempotent, hence `0` or `1` by
`TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`; it cannot be `0`, since that would
force `x`, and with it `1 = a * x`, to vanish. -/
theorem isUnit_of_mul_eq_one_left {a x : R} (h : a * x = 1) : IsUnit x := by
  have hidem : IsIdempotentElem (x * a) := by
    change x * a * (x * a) = x * a
    rw [mul_assoc, ← mul_assoc a x a, h, one_mul]
  rcases eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · refine absurd h ?_
    have hx : x = 0 :=
      calc x = x * (a * x) := by rw [h, mul_one]
        _ = x * a * x := by rw [mul_assoc]
        _ = 0 := by rw [h0, zero_mul]
    rw [hx, mul_zero]
    exact zero_ne_one
  · exact ⟨⟨x, a, h1, h⟩, rfl⟩

/-- **An element of a local ring with a right inverse is a unit**, the mirror image of
`TauCeti.IsLocalRing.isUnit_of_mul_eq_one_left`: the right factor is a unit by that theorem, and
the left factor is then its inverse. -/
theorem isUnit_of_mul_eq_one_right {x a : R} (h : x * a = 1) : IsUnit x := by
  obtain ⟨u, rfl⟩ := isUnit_of_mul_eq_one_left h
  have hx : x = (↑u⁻¹ : R) :=
    calc x = x * ((u : R) * (↑u⁻¹ : R)) := by rw [u.mul_inv, mul_one]
      _ = x * (u : R) * (↑u⁻¹ : R) := by rw [mul_assoc]
      _ = (↑u⁻¹ : R) := by rw [h, one_mul]
  exact hx ▸ u⁻¹.isUnit

/-- **The Jacobson radical of a local ring is its set of non-units.**

A unit is never radical, since `1 + (-x⁻¹) * x = 0` is not a unit. Conversely, if `x` is not a unit
then neither is `y * x` for any `y`, because a unit `y * x` would give `x` a left inverse and hence,
by `TauCeti.IsLocalRing.isUnit_of_mul_eq_one_left`, make it a unit; so in the splitting
`1 = (1 + y * x) + (-(y * x))` of the unit `1` it is the first summand that is a unit. -/
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
      refine absurd (isUnit_of_mul_eq_one_left (a := -((↑u⁻¹ : R) * y)) ?_) hx
      have hstep : -((↑u⁻¹ : R) * y) * x = (↑u⁻¹ : R) * -(y * x) := by noncomm_ring
      rw [hstep, ← hu, u.inv_mul]

variable (R) in
/-- The residue ring of a local ring is nontrivial, the Jacobson radical of a nontrivial ring
being proper by `Ring.jacobson_lt_top`. -/
instance instNontrivialQuotientJacobson : Nontrivial (R ⧸ Ring.jacobson R) :=
  Ideal.Quotient.nontrivial_iff.mpr (Ring.jacobson_lt_top R).ne

/-- **A residue class modulo the Jacobson radical vanishes exactly on the non-units.** -/
@[simp]
theorem mk_jacobson_eq_zero_iff {x : R} :
    Ideal.Quotient.mk (Ring.jacobson R) x = 0 ↔ ¬ IsUnit x :=
  Ideal.Quotient.eq_zero_iff_mem.trans mem_jacobson_iff_not_isUnit

/-- **A residue class modulo the Jacobson radical is a unit exactly on the units.**

Not a `simp` lemma: the quotient is a division ring, so `simp` already rewrites the left-hand
side through `isUnit_iff_ne_zero` and `mk_jacobson_eq_zero_iff`. -/
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
