/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit

/-!
# Cohomological units for `A∞` algebras

A cohomological unit is a degree-zero cycle whose left and right binary products act as the
identity modulo boundaries.  Unlike a strict unit, its unit equations therefore hold only after
passing to the cohomology of the unary operation, and it places no restriction on higher
operations containing its chosen representative.

This file constructs the total cohomology module of the unary operation as cycles modulo
boundaries.  The characteristic API for a cohomological unit is stated both in terms of explicit
boundaries and as equality of cohomology classes.  In particular, any two representatives of a
cohomological unit determine the same class, while every strict unit supplies a cohomological one.

## Main definitions

* `TauCeti.AInfinityAlgebra.differential`: the unary operation as a linear endomorphism.
* `TauCeti.AInfinityAlgebra.cycles` and `TauCeti.AInfinityAlgebra.boundaries`: the cycles and
  boundaries of the unary operation.
* `TauCeti.AInfinityAlgebra.Cohomology`: the total cohomology module.
* `TauCeti.AInfinityAlgebra.CohomologicalUnit`: a representative of a two-sided unit in
  cohomology.
* `TauCeti.AInfinityAlgebra.CohomologicallyUnital`: existence of such a representative.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Cohomology of the unary operation -/

/-- The unary `A∞` operation, regarded as a linear differential on the total module. -/
def differential (𝒜 : AInfinityAlgebra R A) : A →ₗ[R] A :=
  (𝒜.m 1).curryRight ![]

/-- Evaluating the differential is evaluating the unary operation. -/
@[simp]
theorem differential_apply (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x = 𝒜.m 1 ![x] := by
  simp [differential, MultilinearMap.curryRight_apply]

/-- The unary operation squares to zero. -/
@[simp]
theorem differential_sq (𝒜 : AInfinityAlgebra R A) :
    𝒜.differential ∘ₗ 𝒜.differential = 0 := by
  ext x
  simp only [LinearMap.comp_apply, differential_apply, LinearMap.zero_apply,
    𝒜.stasheff_arity_one]

/-- The cycles of an `A∞` algebra are the kernel of its unary operation. -/
def cycles (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.ker 𝒜.differential

/-- An element is a cycle exactly when its unary operation vanishes. -/
@[simp]
theorem mem_cycles (𝒜 : AInfinityAlgebra R A) {x : A} :
    x ∈ 𝒜.cycles ↔ 𝒜.m 1 ![x] = 0 := by
  rw [cycles, LinearMap.mem_ker, differential_apply]

/-- The boundaries of an `A∞` algebra are the range of its unary operation. -/
def boundaries (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.range 𝒜.differential

/-- An element is a boundary exactly when it is the unary operation of some element. -/
@[simp]
theorem mem_boundaries (𝒜 : AInfinityAlgebra R A) {x : A} :
    x ∈ 𝒜.boundaries ↔ ∃ y : A, 𝒜.m 1 ![y] = x := by
  simp only [boundaries, LinearMap.mem_range, differential_apply]

/-- Every boundary is a cycle. -/
theorem boundaries_le_cycles (𝒜 : AInfinityAlgebra R A) : 𝒜.boundaries ≤ 𝒜.cycles := by
  rintro _ ⟨y, rfl⟩
  rw [mem_cycles, differential_apply]
  exact 𝒜.stasheff_arity_one y

/-- The differential of every element is a boundary. -/
theorem differential_mem_boundaries (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x ∈ 𝒜.boundaries :=
  ⟨x, rfl⟩

/-- The differential of every element is a cycle. -/
theorem differential_mem_cycles (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x ∈ 𝒜.cycles :=
  𝒜.boundaries_le_cycles (𝒜.differential_mem_boundaries x)

/-- The boundaries, viewed as a submodule of the cycles. -/
def boundariesInCycles (𝒜 : AInfinityAlgebra R A) : Submodule R 𝒜.cycles :=
  𝒜.boundaries.submoduleOf 𝒜.cycles

/-- A cycle belongs to `boundariesInCycles` exactly when its underlying element is a boundary. -/
@[simp]
theorem mem_boundariesInCycles (𝒜 : AInfinityAlgebra R A) {x : 𝒜.cycles} :
    x ∈ 𝒜.boundariesInCycles ↔ (x : A) ∈ 𝒜.boundaries := by
  rw [boundariesInCycles, Submodule.submoduleOf, Submodule.mem_comap]
  rfl

/-- The total cohomology module of an `A∞` algebra: unary cycles modulo unary boundaries.

This total quotient is the natural home for the class represented by a cohomological unit; its
degree-zero condition is stated separately using `AInfinityAlgebra.grading`. -/
abbrev Cohomology (𝒜 : AInfinityAlgebra R A) := 𝒜.cycles ⧸ 𝒜.boundariesInCycles

/-- The cohomology class represented by a cycle. -/
def cohomologyClass (𝒜 : AInfinityAlgebra R A) {x : A} (hx : x ∈ 𝒜.cycles) : 𝒜.Cohomology :=
  Submodule.Quotient.mk ⟨x, hx⟩

/-- Two cycles represent the same cohomology class exactly when their difference is a boundary. -/
theorem cohomologyClass_eq_iff (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) :
    𝒜.cohomologyClass hx = 𝒜.cohomologyClass hy ↔ x - y ∈ 𝒜.boundaries := by
  rw [cohomologyClass, cohomologyClass, Submodule.Quotient.eq,
    mem_boundariesInCycles]
  rfl

/-- A cycle represents zero in cohomology exactly when it is a boundary. -/
@[simp]
theorem cohomologyClass_eq_zero_iff (𝒜 : AInfinityAlgebra R A) {x : A}
    (hx : x ∈ 𝒜.cycles) : 𝒜.cohomologyClass hx = 0 ↔ x ∈ 𝒜.boundaries := by
  rw [cohomologyClass, Submodule.Quotient.mk_eq_zero, mem_boundariesInCycles]

/-- The cohomology class of a boundary is zero. -/
@[simp]
theorem cohomologyClass_m_one_eq_zero (𝒜 : AInfinityAlgebra R A) {x : A}
    (hx : 𝒜.m 1 ![x] ∈ 𝒜.cycles) : 𝒜.cohomologyClass hx = 0 :=
  (𝒜.cohomologyClass_eq_zero_iff _).mpr (𝒜.mem_boundaries.mpr ⟨x, rfl⟩)

/-! ### Cohomological units -/

/-- A chain representative of a unit on the cohomology of an `A∞` algebra.

The representative is a degree-zero cycle.  Its binary products with every cycle differ from that
cycle by an explicit unary boundary, on both the left and the right.  These equations neither
select a strict chain-level unit nor constrain higher operations on tuples containing `e`. -/
structure CohomologicalUnit (𝒜 : AInfinityAlgebra R A) (e : A) : Prop where
  /-- The representative has cohomological degree zero. -/
  degree_zero : e ∈ 𝒜.grading.piece 0
  /-- The representative is a unary cycle. -/
  cycle : e ∈ 𝒜.cycles
  /-- Left multiplication by the representative is the identity modulo boundaries. -/
  left_unit : ∀ x : A, x ∈ 𝒜.cycles → 𝒜.m 2 ![e, x] - x ∈ 𝒜.boundaries
  /-- Right multiplication by the representative is the identity modulo boundaries. -/
  right_unit : ∀ x : A, x ∈ 𝒜.cycles → 𝒜.m 2 ![x, e] - x ∈ 𝒜.boundaries

/-- An `A∞` algebra is cohomologically unital when it admits a cohomological-unit
representative. -/
def CohomologicallyUnital (𝒜 : AInfinityAlgebra R A) : Prop :=
  ∃ e : A, 𝒜.CohomologicalUnit e

namespace CohomologicalUnit

variable {𝒜 : AInfinityAlgebra R A} {e e' : A}

/-- The explicit-boundary form of the left unit equation. -/
theorem exists_differential_eq_left_sub (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) : ∃ y : A, 𝒜.m 1 ![y] = 𝒜.m 2 ![e, x] - x :=
  (𝒜.mem_boundaries).mp (h.left_unit x hx)

/-- The explicit-boundary form of the right unit equation. -/
theorem exists_differential_eq_right_sub (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) : ∃ y : A, 𝒜.m 1 ![y] = 𝒜.m 2 ![x, e] - x :=
  (𝒜.mem_boundaries).mp (h.right_unit x hx)

/-- Multiplying a cycle on the left by a cohomological-unit representative gives a cycle. -/
theorem left_mul_mem_cycles (h : 𝒜.CohomologicalUnit e) {x : A} (hx : x ∈ 𝒜.cycles) :
    𝒜.m 2 ![e, x] ∈ 𝒜.cycles := by
  rw [← sub_add_cancel (𝒜.m 2 ![e, x]) x]
  exact 𝒜.cycles.add_mem (𝒜.boundaries_le_cycles (h.left_unit x hx)) hx

/-- Multiplying a cycle on the right by a cohomological-unit representative gives a cycle. -/
theorem right_mul_mem_cycles (h : 𝒜.CohomologicalUnit e) {x : A} (hx : x ∈ 𝒜.cycles) :
    𝒜.m 2 ![x, e] ∈ 𝒜.cycles := by
  rw [← sub_add_cancel (𝒜.m 2 ![x, e]) x]
  exact 𝒜.cycles.add_mem (𝒜.boundaries_le_cycles (h.right_unit x hx)) hx

/-- The left unit equation as an equality of cohomology classes. -/
theorem cohomologyClass_left_mul (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) :
    𝒜.cohomologyClass (h.left_mul_mem_cycles hx) = 𝒜.cohomologyClass hx :=
  (𝒜.cohomologyClass_eq_iff _ _).mpr (h.left_unit x hx)

/-- The right unit equation as an equality of cohomology classes. -/
theorem cohomologyClass_right_mul (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) :
    𝒜.cohomologyClass (h.right_mul_mem_cycles hx) = 𝒜.cohomologyClass hx :=
  (𝒜.cohomologyClass_eq_iff _ _).mpr (h.right_unit x hx)

/-- Any two cohomological-unit representatives differ by a boundary. -/
theorem sub_mem_boundaries (h : 𝒜.CohomologicalUnit e) (h' : 𝒜.CohomologicalUnit e') :
    e - e' ∈ 𝒜.boundaries := by
  have hleft := h.left_unit e' h'.cycle
  have hright := h'.right_unit e h.cycle
  simpa only [sub_sub_sub_cancel_left] using 𝒜.boundaries.sub_mem hleft hright

/-- Any two cohomological-unit representatives determine the same cohomology class. -/
theorem cohomologyClass_eq (h : 𝒜.CohomologicalUnit e) (h' : 𝒜.CohomologicalUnit e') :
    𝒜.cohomologyClass h.cycle = 𝒜.cohomologyClass h'.cycle :=
  (𝒜.cohomologyClass_eq_iff _ _).mpr (h.sub_mem_boundaries h')

end CohomologicalUnit

namespace StrictUnit

variable {𝒜 : AInfinityAlgebra R A} {e : A}

/-- A strict unit is a cohomological unit, represented by the same element. -/
theorem cohomologicalUnit (h : 𝒜.StrictUnit e) : 𝒜.CohomologicalUnit e where
  degree_zero := h.degree_zero
  cycle := 𝒜.mem_cycles.mpr h.unary_eq_zero
  left_unit x _ := by simp only [h.binary_left, sub_self, Submodule.zero_mem]
  right_unit x _ := by simp only [h.binary_right, sub_self, Submodule.zero_mem]

/-- An `A∞` algebra with a strict unit is cohomologically unital. -/
theorem cohomologicallyUnital (h : 𝒜.StrictUnit e) : 𝒜.CohomologicallyUnital :=
  ⟨e, h.cohomologicalUnit⟩

end StrictUnit

end AInfinityAlgebra

end TauCeti
