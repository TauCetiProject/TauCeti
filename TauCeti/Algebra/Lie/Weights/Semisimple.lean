/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Weight spaces for semisimple actions

Generalized and honest weight spaces of a nilpotent Lie algebra agree whenever every acting
endomorphism is semisimple. This uses the corresponding equality for generalized eigenspaces
from Mathlib and needs neither a splitting field nor finite-dimensionality.
-/

public section

namespace TauCeti

open LieModule

universe u v w

/-! ### Honest weight spaces for semisimple actions -/

section Semisimple

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Generalized and honest weight spaces of a nilpotent Lie algebra agree when every acting
endomorphism is semisimple. No splitting or finite-dimensionality hypothesis is needed. -/
theorem genWeightSpace_eq_weightSpace_of_isSemisimple
    (h : ∀ x : L, (toEnd K L M x).IsSemisimple) (χ : L → K) :
    genWeightSpace M χ = weightSpace M χ := by
  ext m
  rw [mem_genWeightSpace, mem_weightSpace]
  refine forall_congr' fun x ↦ ?_
  rw [← Module.End.mem_maxGenEigenspace,
    (h x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff, toEnd_apply_apply]

end Semisimple

end TauCeti
