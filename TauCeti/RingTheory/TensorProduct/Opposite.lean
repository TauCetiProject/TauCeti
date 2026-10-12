/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Double-opposite maps on a tensor factor

Apply `AlgEquiv.opOp` to the right tensor factor while leaving the left factor unchanged.
-/

public section

open scoped TensorProduct

/-- The tensor-product homomorphism identifying the right factor with its double opposite. -/
abbrev Algebra.TensorProduct.mapOpOpRight (K L A : Type*) [CommSemiring K] [Semiring L]
    [Semiring A] [Algebra K L] [Algebra K A] : L ⊗[K] A →ₐ[K] L ⊗[K] Aᵐᵒᵖᵐᵒᵖ :=
  Algebra.TensorProduct.map (AlgHom.id K L) (AlgEquiv.opOp K A).toAlgHom
