/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space

/-!
# Matrix coefficients of weight vectors

If `m` is a vector of weight `c` in a comodule over a coalgebra, with coaction `m ↦ m ⊗ c` for a
group-like element `c`, then each matrix coefficient of `m` is the multiple `φ(m) c` of `c`.

## Main results

* `GroupLike.matrixCoefficient_of_mem_weightSpace`: matrix coefficients of a weight vector.
-/

public section

open TauCeti.Comodule

namespace GroupLike

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [TauCeti.Comodule R C M]

/-- A matrix coefficient of a weight vector `m` of weight `c` is the multiple `φ(m) c` of `c`. -/
theorem matrixCoefficient_of_mem_weightSpace {c : GroupLike R C} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (φ : Module.Dual R M) :
    matrixCoefficient (C := C) φ m = φ m • c.val := by
  rw [matrixCoefficient_def, GroupLike.mem_weightSpace.mp hc]
  simp

end GroupLike
