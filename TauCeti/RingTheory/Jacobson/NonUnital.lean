/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Radical

import TauCeti.RingTheory.Jacobson.Basic

/-!
# The Jacobson radical of a nonunital algebra

The radical is the inverse image of the Jacobson radical of the external unitization.
We provide both its two-sided ring ideal and its scalar submodule, so scalar closure is
retained even without an identity. Quasiregularity characterizes membership and shows
that this construction agrees with `Ring.jacobson` when the algebra already has a unit.

These constructions are algebraic; no completeness or norm is required.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The unitization and quasiregularity interfaces are Mathlib's `Unitization` and
  `isQuasiregular_iff_isUnit'`. Radical membership uses
  `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left`.
-/

public section

namespace TauCeti

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The Jacobson radical of a nonunital algebra, defined through its external unitization. -/
def nonUnitalJacobson : TwoSidedIdeal A :=
  (Ring.jacobson (Unitization R A)).toTwoSided.comap (Unitization.inrNonUnitalAlgHom R A)

@[simp]
theorem mem_nonUnitalJacobson {a : A} :
    a ∈ nonUnitalJacobson R A ↔
      (a : Unitization R A) ∈ Ring.jacobson (Unitization R A) := by
  simp [nonUnitalJacobson, TwoSidedIdeal.mem_comap]

/-- The scalar submodule underlying the nonunital Jacobson radical. -/
def nonUnitalJacobsonSubmodule : Submodule R A :=
  ((Ring.jacobson (Unitization R A)).restrictScalars R).comap (Unitization.inrHom R R A)

@[simp]
theorem mem_nonUnitalJacobsonSubmodule {a : A} :
    a ∈ nonUnitalJacobsonSubmodule R A ↔ a ∈ nonUnitalJacobson R A := by
  simp [nonUnitalJacobsonSubmodule, Submodule.mem_comap]

/-- The two carriers of the radical have exactly the same elements. -/
@[simp]
theorem coe_nonUnitalJacobsonSubmodule :
    (nonUnitalJacobsonSubmodule R A : Set A) = nonUnitalJacobson R A := by
  ext a
  exact mem_nonUnitalJacobsonSubmodule R A

/-- The nonunital Jacobson radical is closed under scalar multiplication. -/
theorem smul_mem_nonUnitalJacobson (r : R) {a : A} (ha : a ∈ nonUnitalJacobson R A) :
    r • a ∈ nonUnitalJacobson R A := by
  exact (mem_nonUnitalJacobsonSubmodule R A).mp <|
    (nonUnitalJacobsonSubmodule R A).smul_mem r <|
      (mem_nonUnitalJacobsonSubmodule R A).mpr ha

/-- Membership in the nonunital radical is equivalent to quasiregularity of all
scalar-plus-left multiples. The scalar term comes from reading left multiplication
in the external unitization. -/
theorem mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul {a : A} :
    a ∈ nonUnitalJacobson R A ↔ ∀ (r : R) (b : A), IsQuasiregular (r • a + b * a) := by
  rw [mem_nonUnitalJacobson, Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
  constructor
  · intro h r b
    rw [isQuasiregular_iff_isUnit' R]
    convert h (Unitization.inl r + (b : Unitization R A)) using 1
    ext <;> simp [Unitization.snd_mul]
  · intro h x
    have hx := (h x.fst x.snd).isUnit' R
    convert hx using 1
    ext <;> simp [Unitization.snd_mul]

section Unital

variable (B : Type*) [Ring B] [Algebra R B]

/-- For an algebra that already has an identity, the external-unitization definition
recovers its ordinary Jacobson radical. The external unitization itself is not identified
with the original algebra. -/
@[simp]
theorem nonUnitalJacobson_eq_toTwoSided_jacobson :
    nonUnitalJacobson R B = (Ring.jacobson B).toTwoSided := by
  ext a
  rw [Ideal.mem_toTwoSided, mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul,
    Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
  constructor
  · intro h b
    simpa only [zero_smul, zero_add] using (h 0 b).isUnit_one_add
  · intro h r b
    rw [isQuasiregular_iff_isUnit]
    simpa only [add_mul, Algebra.smul_def] using h (algebraMap R B r + b)

end Unital

end TauCeti
