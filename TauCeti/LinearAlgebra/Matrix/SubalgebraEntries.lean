/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Matrix and vector entries lying in a subsemiring or a subalgebra

A subsemiring `s` of `R` contains every entry of a product `M * N` or `M *ᵥ v` of matrices and
vectors with entries in `s`, the products being rectangular. For a subalgebra `S` of a commutative
`R`-algebra `A`, a matrix with entries in `S` is the image of a matrix over `S`; the vector form
is `Subalgebra.mem_range_compLeft_algebraLinearMap_iff` in `TauCeti.LinearAlgebra.Pi`. These are
the integrality computations for matrices over a ring of integral elements, such as the integral
finite adeles inside the finite adeles. For entries in an ideal see
`TauCeti.LinearAlgebra.Matrix.IdealEntries`.

## Main results

* `Matrix.mul_apply_mem`, `Matrix.mulVec_apply_mem`: products of matrices and vectors with
  entries in a subsemiring have entries in it.
* `Subalgebra.exists_map_algebraMap_eq`: a matrix with entries in `S` comes from a matrix over `S`.
-/

public section

namespace Matrix

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R] [NonUnitalSubsemiringClass S R]
  {s : S} {p q r : Type*} [Fintype q]

/-- A product of matrices with entries in a subsemiring `s` has entries in `s`. -/
theorem mul_apply_mem {M : Matrix p q R} {N : Matrix q r R} (hM : ∀ i j, M i j ∈ s)
    (hN : ∀ i j, N i j ∈ s) (i : p) (j : r) : (M * N) i j ∈ s :=
  sum_mem fun k _ ↦ mul_mem (hM i k) (hN k j)

/-- A matrix with entries in a subsemiring `s` maps vectors with entries in `s` to vectors with
entries in `s`. -/
theorem mulVec_apply_mem {M : Matrix p q R} {v : q → R} (hM : ∀ i j, M i j ∈ s)
    (hv : ∀ i, v i ∈ s) (i : p) : (M *ᵥ v) i ∈ s := by
  -- the matrix form for the single column `v`
  simpa [← replicateCol_mulVec] using
    mul_apply_mem hM (N := replicateCol Unit v) (fun k _ ↦ hv k) i ()

end Matrix

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {S : Subalgebra R A}

/-- A matrix over `A` with entries in a subalgebra `S` is the image of a matrix over `S`. -/
theorem exists_map_algebraMap_eq {p q : Type*} {M : Matrix p q A} (hM : ∀ i j, M i j ∈ S) :
    ∃ N : Matrix p q S, N.map (algebraMap S A) = M :=
  ⟨.of fun i j ↦ ⟨M i j, hM i j⟩, Matrix.ext fun _ _ ↦ algebraMap_apply S _⟩

end Subalgebra
