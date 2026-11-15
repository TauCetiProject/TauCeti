/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Cokernel length of a diagonal matrix

Over any commutative ring, the cokernel of a diagonal matrix `diagonal d` acting on `Rⁿ` is the
product of the quotients `R ⧸ (d i)`, so its length is the sum of the orders `Ring.ord R (d i)`.
Zero entries are allowed, with length and order valued in `ℕ∞`.
-/

public section

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The cokernel of a diagonal matrix has length equal to the sum of the orders of its
entries. Zero entries are allowed, with length and order valued in `ℕ∞`. -/
theorem length_quotient_range_diagonal_mulVecLin (d : ι → R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (diagonal d).mulVecLin) =
      ∑ i, Ring.ord R (d i) := by
  have hrange : LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i ↦ (Ideal.span {d i} : Submodule R R)) := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_const,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by simp [mulVec_diagonal]⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, by ext i; simpa [mulVecLin_apply, mulVec_diagonal] using (hy i).symm⟩
  rw [hrange, (Submodule.quotientPi (fun i ↦ (Ideal.span {d i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype]
  rfl

end Matrix
