/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Separable

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

For a semisimple endomorphism of a finite-dimensional space, each generalized eigenspace is the
eigenspace, so the multiplicity of `μ` as a root of the characteristic polynomial is the dimension
of the `μ`-eigenspace.

## Main results

* `TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`: an endomorphism of a semisimple module whose
  eigenspaces span the module is semisimple.
* `TauCeti.isSemisimple_lmul`: multiplication by a fixed vector on `ι → K`, a diagonal operator,
  is semisimple.
* `TauCeti.isSemisimple_of_pow_three_eq_smul`: an endomorphism with `f³ = c f`, `c ≠ 0`, is
  semisimple away from characteristic two.
* `Module.End.IsFinitelySemisimple.rootMultiplicity_charpoly`: for a semisimple endomorphism, the
  multiplicity of a root `μ` of the characteristic polynomial is the dimension of the
  `μ`-eigenspace.
* `Module.End.IsSemisimple.aeval_apply_eq_zero_of_mem_maxGenEigenspace`: for a semisimple
  endomorphism `f` and a polynomial `p`, a vector killed by a power of `p(f)` is killed by `p(f)`.
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

open Polynomial in
/-- Multiplication by a fixed vector `c : ι → K`, the diagonal operator with entries `c i`, is
semisimple: it is killed by the squarefree polynomial `∏ (X - c i)` over the distinct values. -/
theorem isSemisimple_lmul {K ι : Type*} [Field K] [Finite ι] (c : ι → K) :
    (Algebra.lmul K (ι → K) c).IsSemisimple := by
  classical
  cases nonempty_fintype ι
  refine End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ∏ x ∈ Finset.univ.image c, (X - C x)) ?_ ?_
  · exact (separable_prod_X_sub_C_iff' (f := id).mpr fun _ _ _ _ h ↦ h).squarefree
  · rw [aeval_algHom_apply, map_prod]
    convert map_zero (Algebra.lmul K (ι → K))
    funext j
    rw [Finset.prod_apply, Pi.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem c (Finset.mem_univ j)) (by simp)

open Polynomial in
/-- An endomorphism `f` with `f³ = c f` for a nonzero scalar `c` is semisimple when `2 ≠ 0`: it is
killed by the squarefree polynomial `X (X² - c)`. Both hypotheses are needed: `f³ = 0` holds for
nilpotent `f`, and in characteristic two the matrix `[[a, 1], [0, a]]` satisfies `f² = a²` but is
not semisimple. -/
theorem isSemisimple_of_pow_three_eq_smul {K M : Type*} [Field K] [NeZero (2 : K)]
    [AddCommGroup M] [Module K M] {f : End K M} {c : K} (hc : c ≠ 0) (h : f ^ 3 = c • f) :
    f.IsSemisimple := by
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X * (X ^ 2 - C c)) ?_ ?_
  · refine (separable_X.mul (separable_X_pow_sub_C c two_ne_zero hc) ?_).squarefree
    refine ⟨C c⁻¹ * X, -C c⁻¹, ?_⟩
    have hc' : C c⁻¹ * C c = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
    linear_combination hc'
  · simp [mul_sub, ← pow_succ', h, Algebra.algebraMap_eq_smul_one]

end TauCeti

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For a semisimple endomorphism, the multiplicity of `μ` as a root of the characteristic
polynomial is the dimension of the `μ`-eigenspace. -/
theorem IsFinitelySemisimple.rootMultiplicity_charpoly {f : End K V}
    (hf : f.IsFinitelySemisimple) (μ : K) :
    f.charpoly.rootMultiplicity μ = finrank K (f.eigenspace μ) := by
  rw [← LinearMap.finrank_maxGenEigenspace_eq, hf.maxGenEigenspace_eq_eigenspace]

open Polynomial in
/-- For a semisimple endomorphism `f` and a polynomial `p`, the endomorphism `p(f)` is semisimple,
so every vector killed by a power of `p(f)` is killed by `p(f)`. -/
theorem IsSemisimple.aeval_apply_eq_zero_of_mem_maxGenEigenspace {f : End K V}
    (hf : f.IsSemisimple) {p : K[X]} {v : V} (hv : v ∈ (aeval f p).maxGenEigenspace 0) :
    aeval f p v = 0 := by
  rw [(hf.aeval p).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, mem_eigenspace_iff] at hv
  simpa using hv

end Module.End
