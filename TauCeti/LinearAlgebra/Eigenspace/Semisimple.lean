/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Diagonalizable endomorphisms are semisimple

Mathlib records that a semisimple endomorphism of a finite-dimensional vector space over an
algebraically closed field is diagonalizable
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top`). This file proves the converse, which needs
neither of those hypotheses: over a commutative ring `R`, an endomorphism of a semisimple
`R`-module whose eigenspaces span is semisimple. As an `R[X]`-module the space is the sum of the
eigenspaces, and on the `μ`-eigenspace `X` acts by the scalar `μ`, so that eigenspace is
semisimple over `R[X]` because it is semisimple over `R`. Over a field every module is
semisimple, so there the eigenspaces spanning is the only hypothesis.

## Main results

* `TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`: an endomorphism of a semisimple module whose
  eigenspaces span the module is semisimple.
-/

public section

namespace TauCeti

open Module Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  {f : End R M}

/-- **A diagonalizable endomorphism is semisimple.** An endomorphism of a semisimple module whose
eigenspaces span the module is semisimple. Over a field the semisimplicity of the module is
automatic, and neither algebraic closure nor finite dimension is needed; the converse
`Module.End.IsSemisimple.iSup_eigenspace_eq_top` is where both enter. -/
theorem isSemisimple_of_iSup_eigenspace_eq_top (hf : ⨆ μ : R, f.eigenspace μ = ⊤) :
    f.IsSemisimple := by
  -- `AEval.mapSubmodule` indexes invariant submodules of `Algebra.lsmul R R M f`, defeq to `f`
  have hinv (μ : R) : f.eigenspace μ ∈ (Algebra.lsmul R R M f).invtSubmodule :=
    f.eigenspace_mem_invtSubmodule μ
  set e := AEval.mapSubmodule R M f
  have hss (μ : R) : IsSemisimpleModule R[X] (e ⟨f.eigenspace μ, hinv μ⟩) := by
    refine (AEval.restrict_equiv_mapSubmodule f _ (hinv μ)).isSemisimpleModule_iff.mp ?_
    -- `f` restricts to the scalar `μ` on its `μ`-eigenspace
    have : End.IsSemisimple (f.restrict (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
        (f.eigenspace_mem_invtSubmodule μ))) := by
      rw [End.restrict_eigenspace, ← Module.algebraMap_end_eq_smul_id,
        ← End.isSemisimple_sub_algebraMap_iff (μ := μ), sub_self]
      exact End.isSemisimple_zero
    -- the restriction of `Algebra.lsmul R R M f` is defeq to the restriction of `f`
    exact this
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hss ?_
  rw [eq_top_iff, ← e.map_top, ← e.le_symm_apply, ← Subtype.coe_le_coe]
  exact hf.ge.trans <| iSup_le fun μ ↦ Subtype.coe_le_coe.2 <| e.le_symm_apply.2 <|
    le_iSup (fun μ ↦ e ⟨_, hinv μ⟩) μ

end TauCeti
