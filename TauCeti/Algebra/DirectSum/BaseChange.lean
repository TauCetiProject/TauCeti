/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Homogeneous components after extension of scalars

Mathlib's `DirectSum.Decomposition.baseChange` extends an internal decomposition
without flatness assumptions. Homogeneous projection of a pure tensor is the
tensor of its homogeneous projection. This formula computes homogeneous components
after scalar extension from the original components.

Adapted from `Mei/Algebra/DirectSum/BaseChange.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

open TensorProduct

namespace DirectSum

variable {R S M ι : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [Decomposition ℳ]

/-- Homogeneous projection commutes with tensoring a vector by a scalar. -/
@[simp]
theorem coe_decompose_baseChange_tmul (s : S) (x : M) (i : ι) :
    (decompose (fun i => (ℳ i).baseChange S) (s ⊗ₜ[R] x) i : S ⊗[R] M) =
      s ⊗ₜ[R] (decompose ℳ x i : M) :=
  (map_decompose_shift ℳ (fun i => (ℳ i).baseChange S)
    (TensorProduct.mk R S M s).toAddMonoidHom id Function.injective_id
    (fun _ _ h => Submodule.tmul_mem_baseChange_of_mem s h) i x).symm

end DirectSum
