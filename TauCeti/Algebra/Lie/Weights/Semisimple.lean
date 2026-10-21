/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Weight spaces for finitely semisimple actions

Generalized and honest weight spaces of a nilpotent Lie algebra agree whenever every acting
endomorphism is finitely semisimple: its restriction to every finitely generated invariant
submodule is semisimple. This uses Mathlib's equality for generalized eigenspaces over a
commutative ring and needs neither a splitting field nor finite-dimensionality.
-/

public section

namespace TauCeti

open LieModule

universe u v w

variable {R : Type u} {L : Type v} {M : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Generalized and honest weight spaces of a nilpotent Lie algebra agree when every acting
endomorphism is finitely semisimple. The scalars may form any commutative ring. -/
theorem genWeightSpace_eq_weightSpace_of_isFinitelySemisimple
    (h : ∀ x : L, (toEnd R L M x).IsFinitelySemisimple) (χ : L → R) :
    genWeightSpace M χ = weightSpace M χ := by
  ext m
  rw [mem_genWeightSpace, mem_weightSpace]
  refine forall_congr' fun x ↦ ?_
  rw [← Module.End.mem_maxGenEigenspace,
    (h x).maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff, toEnd_apply_apply]

end TauCeti
