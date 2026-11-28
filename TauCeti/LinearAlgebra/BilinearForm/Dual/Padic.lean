/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Dual.PerfectPairing
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Self-duality of completed integral pairings

The completion at a prime is self-dual exactly when the prime is absent from the
relative index of the integral lattice in its rational dual.
-/

public section

open scoped TensorProduct Padic

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]

/-- For a nondegenerate integral form on a finite module, the completed unit-tensor lattice
is self-dual exactly when its pairing is perfect. -/
theorem baseChange_padic_dualSubmodule_eq_self_iff_isPerfPair (B : LinearMap.BilinForm ℤ M)
    (hB : B.Nondegenerate) (p : ℕ) [Fact p.Prime] :
    let Mₚ := ℤ_[p] ⊗[ℤ] M
    let N := LinearMap.range (TensorProduct.mk ℤ_[p] ℚ_[p] Mₚ 1)
    ((B.baseChange ℤ_[p]).baseChange ℚ_[p]).dualSubmodule N = N ↔
      (B.baseChange ℤ_[p]).IsPerfPair := by
  classical
  have := hB.1.isTorsionFree
  let b := Module.Free.chooseBasis ℤ M
  have hC : (B.baseChange ℤ_[p]).Nondegenerate :=
    (B.nondegenerate_baseChange_iff b).2 hB
  exact (B.baseChange ℤ_[p]).dualSubmodule_range_mk_eq_self_iff_isPerfPair
    (hC.baseChange_of_isLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]))

/-- For a nondegenerate integral form on a finite module, the completion at `p` is self-dual
exactly when `p` does not divide the index of the original lattice in its rational dual. -/
theorem baseChange_padic_dualSubmodule_eq_self_iff_not_dvd_relIndex (B : LinearMap.BilinForm ℤ M)
    (hB : B.Nondegenerate) (p : ℕ) [Fact p.Prime] :
    let Mₚ := ℤ_[p] ⊗[ℤ] M
    let Nₚ := LinearMap.range (TensorProduct.mk ℤ_[p] ℚ_[p] Mₚ 1)
    let N := LinearMap.range (TensorProduct.mk ℤ ℚ M 1)
    ((B.baseChange ℤ_[p]).baseChange ℚ_[p]).dualSubmodule Nₚ = Nₚ ↔
      ¬p ∣ N.toAddSubgroup.relIndex ((B.baseChange ℚ).dualSubmodule N).toAddSubgroup := by
  classical
  have := hB.1.isTorsionFree
  let b := Module.Free.chooseBasis ℤ M
  let bP := b.baseChange ℤ_[p]
  let C := B.baseChange ℤ_[p]
  have hdet : C.IsPerfPair ↔ IsUnit (C.toMatrix bP).det :=
    ⟨bP.isUnit_det_of_isPerfPair bP C, bP.isPerfPair_of_isUnit_det bP C⟩
  dsimp only
  refine (B.baseChange_padic_dualSubmodule_eq_self_iff_isPerfPair hB p).trans ?_
  rw [hdet, det_toMatrix_baseChange,
    B.relIndex_dualSubmodule_range_mk_one_eq_natAbs_det
      (hB.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)) b,
    ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  exact PadicInt.isUnit_intCast_iff

end LinearMap.BilinForm
