/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Geometry.Symplectic.Complex.Module.Hom
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Joint eigenvectors of commuting complex-linear maps

An almost complex structure `J` on a finite-dimensional real space `V` makes `V` a complex vector
space (`TauCeti.AlmostComplexStructure.complexModule`), and real-linear maps commuting with `J`
are then `ℂ`-linear. Since `ℂ` is algebraically closed, a pairwise commuting family of such maps
on a nonzero `V` has a joint eigenvector. This file states the result in real terms, without the
induced complex module: the eigenvalue `c` acts as `c.re + c.im J`.

## Main results

* `TauCeti.AlmostComplexStructure.exists_jointEigenvector_of_pairwise_commute`: commuting
  complex-linear maps have a joint eigenvector in the induced complex structure.
-/

public section

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Joint eigenvectors of commuting complex-linear maps.** A pairwise commuting family of
real-linear maps, complex linear for an almost complex structure `J` on a nonzero
finite-dimensional space, has a joint eigenvector for the induced complex scalars: a nonzero `v`
with `f i v = (c i) v = (c i).re v + (c i).im J v` for every `i`. -/
theorem exists_jointEigenvector_of_pairwise_commute [FiniteDimensional ℝ V] [Nontrivial V]
    (J : AlmostComplexStructure V) {ι : Type*} (f : ι → V →ₗ[ℝ] V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hJ : ∀ i, IsComplexLinearMap J J (f i)) :
    ∃ (c : ι → ℂ) (v : V), v ≠ 0 ∧ ∀ i, f i v = (c i).re • v + (c i).im • J v := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  obtain ⟨c, v, hv, hmem⟩ := exists_jointEigenvector_of_pairwise_commute_of_isAlgClosed
    (fun i ↦ (hJ i).toComplexLinearMap) fun i j hij ↦
      LinearMap.ext fun x ↦ LinearMap.congr_fun (hcomm hij).eq x
  refine ⟨c, v, hv, fun i ↦ ?_⟩
  have h := Module.End.mem_eigenspace_iff.1 (hmem i)
  rw [IsComplexLinearMap.toComplexLinearMap_apply] at h
  rw [h, J.complexModule_smul_def]

end AlmostComplexStructure

end TauCeti
