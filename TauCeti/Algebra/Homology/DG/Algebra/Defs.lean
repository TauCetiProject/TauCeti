/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Nonunital and unital differential graded algebras

A nonunital differential graded algebra over a commutative ring `R` is an internally
`ℤ`-graded nonunital `R`-algebra `A` together with an `R`-linear differential `d` of degree
`+1` which squares to zero and satisfies the graded Leibniz rule

`d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.

This file fixes the nonunital structure as `TauCeti.IsNonUnitalDGAlgebra`.  Every unital
`TauCeti.IsDGAlgebra` has a canonical underlying nonunital DG algebra, while consequences that
genuinely use the unit remain in the unital namespace.  In particular, the differential of a
unital DG algebra annihilates the unit and hence the image of the ground ring.

The grading is stored *internally*, as a family `𝒜 : ℤ → Submodule R A` of submodules of a
single carrier.  In the nonunital case it consists of a direct-sum decomposition together with
degree-additive multiplication; the unital case uses Mathlib's `GradedAlgebra 𝒜`.  The product is
therefore the product of `A`, so no signed totalization is needed to state the Leibniz rule, and
`Int.negOnePow` carries the only sign.

Only a homogeneous *left* factor is constrained by the Leibniz axiom, because the sign depends on
its degree alone.

## Main definitions

* `TauCeti.IsNonUnitalDGAlgebra`: the nonunital differential graded algebra axioms.
* `TauCeti.IsDGAlgebra`: the differential graded algebra axioms on an internally `ℤ`-graded
  unital `R`-algebra and an `R`-linear endomorphism of its carrier.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.map_decompose` computes the differential on homogeneous
  components.
* `TauCeti.IsNonUnitalDGAlgebra.leibniz_of_map_eq_zero` and
  `TauCeti.IsNonUnitalDGAlgebra.map_mul_eq_zero_of_map_eq_zero` specialize the Leibniz rule
  when the right factor is a cycle.
* `TauCeti.IsDGAlgebra.map_one_eq_zero` and `TauCeti.IsDGAlgebra.map_algebraMap`: the differential
  annihilates the unit and, more generally, the image of the ground ring.
* `TauCeti.isNonUnitalDGAlgebra_zero` and `TauCeti.isDGAlgebra_zero`: a graded algebra with zero
  differential is a differential graded algebra.

For a unital DG algebra, the homogeneous consequences of the axioms are also available through
its regular differential graded left module.  Cycles, boundaries, and the cohomology algebra are
built from that module structure in `TauCeti.Algebra.Homology.DG.Algebra.Cohomology`.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

open DirectSum

namespace TauCeti

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A}

/-- A **nonunital differential graded algebra**: an internally `ℤ`-graded nonunital
`R`-algebra `𝒜` on a carrier `A`, together with an `R`-linear map `d` which raises degree by
one, squares to zero, and satisfies the graded Leibniz rule on a homogeneous left factor. -/
structure IsNonUnitalDGAlgebra (𝒜 : ℤ → Submodule R A) [IsScalarTower R A A]
    [SMulCommClass R A A] [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
    (d : A →ₗ[R] A) : Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (a : A) : d (d a) = 0
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

attribute [grind =>] IsNonUnitalDGAlgebra.map_mem

namespace IsNonUnitalDGAlgebra

/-- The differential commutes with homogeneous projections, up to the degree shift by one. -/
theorem map_decompose (h : IsNonUnitalDGAlgebra 𝒜 d) (p : ℤ) (a : A) :
    d (DirectSum.decompose 𝒜 a p : A) =
      (DirectSum.decompose 𝒜 (d a) (p + 1) : A) :=
  DirectSum.map_decompose_shift 𝒜 𝒜 d (· + 1) (add_left_injective 1)
    (fun _ _ ha ↦ h.map_mem ha) p a

/-- The Leibniz rule against a cycle in the right factor.  The vanishing signed term permits an
arbitrary left factor, without a homogeneity hypothesis. -/
theorem leibniz_of_map_eq_zero (h : IsNonUnitalDGAlgebra 𝒜 d) (a : A) {b : A}
    (hb : d b = 0) : d (a * b) = d a * b := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_mul, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [h.leibniz (SetLike.coe_mem _) b, hb, mul_zero, smul_zero, add_zero]

/-- The product of two cycles in a nonunital DG algebra is a cycle. -/
theorem map_mul_eq_zero_of_map_eq_zero (h : IsNonUnitalDGAlgebra 𝒜 d) {a b : A}
    (ha : d a = 0) (hb : d b = 0) : d (a * b) = 0 := by
  rw [h.leibniz_of_map_eq_zero a hb, ha, zero_mul]

end IsNonUnitalDGAlgebra

/-- An internally graded nonunital algebra with zero differential is a nonunital differential
graded algebra. -/
theorem isNonUnitalDGAlgebra_zero (𝒜 : ℤ → Submodule R A) [SetLike.GradedMul 𝒜]
    [DirectSum.Decomposition 𝒜] :
    IsNonUnitalDGAlgebra 𝒜 (0 : A →ₗ[R] A) where
  map_mem := fun _ ↦ zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ ↦ by simp

end NonUnital

section Unital

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

/-- Forget the unit of a differential graded algebra. -/
theorem toIsNonUnitalDGAlgebra (h : IsDGAlgebra 𝒜 d) : IsNonUnitalDGAlgebra 𝒜 d where
  map_mem := h.map_mem
  sq_zero := h.sq_zero
  leibniz := h.leibniz

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
  map_mem := fun _ ↦ zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ ↦ by simp

end Unital

end TauCeti
