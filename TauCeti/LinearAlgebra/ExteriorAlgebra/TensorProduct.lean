/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor naturality of exterior-algebra generators

The inclusion of generators into an exterior algebra commutes with algebra homomorphisms
on the right tensor factor. This lets tensor constructions on generators pass through
changes of the coefficient algebra, in particular the comultiplication and counit of a bialgebra.
-/

public section

open scoped TensorProduct

namespace TauCeti.ExteriorAlgebra

variable {R M H : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Semiring H] [Algebra R H]

/-- An algebra homomorphism on the right tensor factor commutes with the inclusion of
exterior-algebra generators. -/
theorem map_id_rTensor_ι {K : Type*} [Semiring K] [Algebra R K] (φ : H →ₐ[R] K)
    (z : M ⊗[R] H) :
    Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M)) φ
        ((ExteriorAlgebra.ι R).rTensor H z) =
      (ExteriorAlgebra.ι R).rTensor K (φ.toLinearMap.lTensor M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m h => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TauCeti.ExteriorAlgebra
