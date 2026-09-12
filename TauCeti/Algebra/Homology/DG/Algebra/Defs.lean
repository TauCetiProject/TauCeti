/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Differential graded algebras

A differential graded algebra over a commutative ring `R` is a `ℤ`-graded `R`-algebra `A` together
with an `R`-linear differential `d` of degree `+1` which squares to zero and satisfies the graded
Leibniz rule

`d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.

This file fixes that structure and proves the consequences of the degree and Leibniz axioms which
need nothing but the unit: the differential annihilates the unit, and hence the image of the ground
ring.  The consequences which decompose a factor into homogeneous components, namely that the
differential commutes with the homogeneous projections of the grading, that the Leibniz rule
extends from a homogeneous left factor to an arbitrary one against a cycle, and that a cycle times
a boundary is a boundary, are specializations of the corresponding statements about a differential
graded left module, and are proved as such in
`TauCeti.Algebra.Homology.DG.Algebra.SelfModule`.

The grading is stored *internally*, as a family `𝒜 : ℤ → Submodule R A` of submodules of a single
carrier `A` with Mathlib's `GradedAlgebra 𝒜`.  This is the presentation the `DGAInfinity` roadmap
prescribes when "multiplication is easier on a total module": the product is the product of `A`, so
no signed totalization is needed to state the Leibniz rule, and `Int.negOnePow` carries the only
sign.  The cochain-complex presentation, in which the same data is a monoid object in
`CochainComplex (ModuleCat R) ℤ`, is a separate spelling; the comparison between the two is not part
of this file.

Only a homogeneous *left* factor is constrained by the Leibniz axiom, because the sign depends on
its degree alone.

## Main definitions

* `TauCeti.IsDGAlgebra`: the differential graded algebra axioms on an internally `ℤ`-graded
  `R`-algebra and an `R`-linear endomorphism of its carrier.

## Main results

* `TauCeti.IsDGAlgebra.map_one_eq_zero` and `TauCeti.IsDGAlgebra.map_algebraMap`: the differential
  annihilates the unit and, more generally, the image of the ground ring.
* `TauCeti.isDGAlgebra_zero`: a graded algebra with zero differential is a differential graded
  algebra.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 1, item "DG algebras, categories,
modules, and bimodules", specifically its first request to "define nonunital, unital, and augmented
DG algebras on graded `k`-modules ... cycles, boundaries, and the induced graded cohomology
algebra".  The homogeneous consequences of the axioms are in
`TauCeti.Algebra.Homology.DG.Algebra.SelfModule`, and cycles, boundaries and the cohomology
algebra are built on them in `TauCeti.Algebra.Homology.DG.Algebra.Cohomology`.  No formalization
is vendored: the internal grading, its decomposition and its projections are Mathlib's
`GradedAlgebra` API.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A **differential graded algebra**: an internally `ℤ`-graded `R`-algebra `𝒜` on a carrier `A`
together with an `R`-linear map `d` which raises degree by one, squares to zero, and satisfies the
graded Leibniz rule on a homogeneous left factor.  The sign `(-1) ^ p` is `Int.negOnePow p`, acting
through the units of `ℤ`. -/
structure IsDGAlgebra (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) : Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (a : A) : d (d a) = 0
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

attribute [grind =>] IsDGAlgebra.map_mem

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace IsDGAlgebra

/-- The differential of a differential graded algebra annihilates the unit: the Leibniz rule for
`1 * 1` reads `d 1 = d 1 + d 1`. -/
theorem map_one_eq_zero (h : IsDGAlgebra 𝒜 d) : d 1 = 0 := by
  have key := h.leibniz (SetLike.one_mem_graded 𝒜) 1
  simp only [mul_one, one_mul, Int.negOnePow_zero, one_smul] at key
  exact left_eq_add.mp key

/-- The differential of a differential graded algebra annihilates the image of the ground ring. -/
theorem map_algebraMap (h : IsDGAlgebra 𝒜 d) (r : R) : d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h.map_one_eq_zero, smul_zero]

end IsDGAlgebra

/-- A `ℤ`-graded algebra with zero differential is a differential graded algebra. -/
theorem isDGAlgebra_zero (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    IsDGAlgebra 𝒜 (0 : A →ₗ[R] A) where
  map_mem := fun _ => zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ => by simp

end TauCeti
