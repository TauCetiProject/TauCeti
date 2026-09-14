/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit

/-!
# Cohomological units for `A∞` algebras

A cohomological unit is a degree-zero cycle whose left and right binary products act as the
identity modulo boundaries.  Unlike a strict unit, its unit equations therefore hold only after
passing to the cohomology of the unary operation, and it places no restriction on higher
operations containing its chosen representative.

The characteristic API for a cohomological unit is stated both in terms of explicit boundaries and
as the two unit laws for the product `AInfinityAlgebra.cohomologyMul` on the total cohomology
module.  In particular, any two representatives of a cohomological unit determine the same class,
while every strict unit supplies a cohomological one.

## Main definitions

* `TauCeti.AInfinityAlgebra.CohomologicalUnit`: a representative of a two-sided unit in
  cohomology.
* `TauCeti.AInfinityAlgebra.CohomologicallyUnital`: existence of such a representative.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.

The signature of `CohomologicalUnit` is adapted from the `CohomologicalUnit` scaffold of the
roadmap's formal companion
[`DGAInfinity/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/DGAInfinity/Suggested.lean),
whose cycle and boundary conditions are restated here against the submodules of
`TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology`.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

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

/-- The class of a cohomological unit is a left unit for the product on cohomology. -/
@[simp]
theorem cohomologyMul_cohomologyClass_left (h : 𝒜.CohomologicalUnit e) (c : 𝒜.Cohomology) :
    𝒜.cohomologyMul (𝒜.cohomologyClass h.cycle) c = c := by
  obtain ⟨x, hx, rfl⟩ := 𝒜.exists_cohomologyClass_eq c
  simpa using h.left_unit x hx

/-- The class of a cohomological unit is a right unit for the product on cohomology. -/
@[simp]
theorem cohomologyMul_cohomologyClass_right (h : 𝒜.CohomologicalUnit e) (c : 𝒜.Cohomology) :
    𝒜.cohomologyMul c (𝒜.cohomologyClass h.cycle) = c := by
  obtain ⟨x, hx, rfl⟩ := 𝒜.exists_cohomologyClass_eq c
  simpa using h.right_unit x hx

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
