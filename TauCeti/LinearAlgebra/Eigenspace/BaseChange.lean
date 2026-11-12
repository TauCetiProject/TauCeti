/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Eigenspaces after flat extension of scalars

An eigenspace is the kernel of a scalar translate of an endomorphism. Flat extension of scalars
therefore carries it to the eigenspace at the image of its eigenvalue. This allows a spanning
family of eigenspaces over a larger field to descend when its eigenvalues lie in the ground field.
-/

public section

namespace Module.End

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module.Flat R A]

/-- Flat extension of scalars commutes with the eigenspace at a specified eigenvalue. -/
theorem eigenspace_baseChange_of_flat (f : End R M) (μ : R) :
    eigenspace (f.baseChange A) (algebraMap R A μ) = (f.eigenspace μ).baseChange A := by
  rw [eigenspace_def, eigenspace_def, ← LinearMap.ker_baseChange_of_flat]
  simp

end Module.End
