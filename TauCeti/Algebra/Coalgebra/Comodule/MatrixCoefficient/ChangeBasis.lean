/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner

/-!
# Change of basis for comodule coefficient matrices

The coefficient matrices of a finite free comodule intertwine with the scalar extension of
the change-of-basis matrix. This turns a triangular comodule basis into a conjugation of
the corresponding matrix-valued point.
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace Module.Basis

variable {R C M ι κ : Type*} [CommSemiring R] [Semiring C] [Algebra R C]
variable [Coalgebra R C] [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [Fintype ι] [Fintype κ]

/-- Coefficient matrices intertwine with the change-of-basis matrix, extended to the
coefficient algebra. The bases may have different finite index types. -/
theorem coefficientMatrix_mul_toMatrix (b : Basis ι R M) (c : Basis κ R M) :
    coefficientMatrix (C := C) b * (b.toMatrix c).map (algebraMap R C) =
      (b.toMatrix c).map (algebraMap R C) * coefficientMatrix (C := C) c := by
  classical
  simpa [← LinearMap.toMatrix_id_eq_basis_toMatrix] using
    (Hom.id R C M).coefficientMatrix_mul_toMatrix c b

end Module.Basis
