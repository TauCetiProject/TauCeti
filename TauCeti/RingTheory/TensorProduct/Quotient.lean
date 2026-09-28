/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Tensoring with a quotient map

For an `R`-algebra `A` and an ideal `I` of an `R`-algebra `C`, the map
`A ⊗[R] C → A ⊗[R] (C ⧸ I)` induced by the quotient map is surjective, and its kernel is the
extension of `I` along `C → A ⊗[R] C`. This is Mathlib's `Algebra.TensorProduct.lTensor_ker`
specialised to the quotient map `Ideal.Quotient.mkₐ R I`.

## Main results

* `Algebra.TensorProduct.ker_map_id_mkₐ`: the kernel of `A ⊗[R] C → A ⊗[R] (C ⧸ I)` is the
  extension of `I`.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]
  {C : Type*} [CommRing C] [Algebra R C]

/-- The kernel of `A ⊗[R] C → A ⊗[R] (C ⧸ I)` is the extension of `I` along
`C → A ⊗[R] C`. -/
@[simp]
theorem ker_map_id_mkₐ (I : Ideal C) :
    RingHom.ker (map (AlgHom.id R A) (Ideal.Quotient.mkₐ R I)) =
      I.map (includeRight : C →ₐ[R] A ⊗[R] C) := by
  rw [lTensor_ker _ (Ideal.Quotient.mkₐ_surjective R I), ← RingHom.ker_coe_toRingHom,
    Ideal.Quotient.mkₐ_ker]

end Algebra.TensorProduct
