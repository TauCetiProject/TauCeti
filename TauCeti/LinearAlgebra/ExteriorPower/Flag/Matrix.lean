/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.ExteriorPower.Flag.Basic
import Mathlib.LinearAlgebra.Basis.Flag
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.TensorProduct.Segre
import TauCeti.LinearAlgebra.Unimodular

/-!
# Flag stabilizers and upper-triangular matrices

This file connects the stabilizer of an exterior flag line in `FlagSpace k M d` with upper
triangularity in the underlying basis `b : Module.Basis (Fin d) k M`.

## Main results

* `TauCeti.exteriorPower.isUpperTriangular_toMatrix_of_exteriorFlagMap_mem_span`: a linear
  automorphism preserving the line spanned by `exteriorFlagVector k d b` has an upper-triangular
  matrix in `b`.
-/

public section

namespace TauCeti.exteriorPower

universe u v

variable {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

private theorem mem_span_prefix_of_exteriorFlagVector_eq_smul {d : ℕ} {u v : Fin d → M} {c : k}
    (hv : LinearIndependent k v) (hc : c ≠ 0)
    (h : exteriorFlagVector k d u = c • exteriorFlagVector k d v) (j : Fin d) :
    u j ∈ Submodule.span k (Set.range (v ∘ Fin.castLE j.isLt)) := by
  induction d generalizing c with
  | zero => exact j.elim0
  | succ r ih =>
    have h' :
        exteriorFlagVector k r (u ∘ Fin.castSucc) ⊗ₜ[k]
            _root_.exteriorPower.ιMulti k (r + 1) u =
          (c • exteriorFlagVector k r (v ∘ Fin.castSucc)) ⊗ₜ[k]
            _root_.exteriorPower.ιMulti k (r + 1) v := by
      simpa [TensorProduct.smul_tmul'] using congrArg (flagSpaceSuccEquiv k M r) h
    have hne : (c • exteriorFlagVector k r (v ∘ Fin.castSucc)) ⊗ₜ[k]
        _root_.exteriorPower.ιMulti k (r + 1) v ≠ 0 := by
      rw [← TensorProduct.smul_tmul', ← flagSpaceSuccEquiv_exteriorFlagVector, ← map_smul,
        LinearEquiv.map_ne_zero_iff]
      exact smul_ne_zero hc (exteriorFlagVector_ne_zero_iff.mpr hv)
    obtain ⟨a, ha₁, ha₂⟩ := TensorProduct.exists_units_smul_of_tmul_eq_tmul h'.symm hne
    refine j.lastCases ?_ fun i ↦ ?_
    · have hspan := (_root_.exteriorPower.span_range_eq_of_ιMulti_eq_smul hv a.ne_zero
        (by rw [ha₂, Units.smul_def])).2
      have hrange : Set.range (v ∘ Fin.castLE (Fin.last r).isLt) = Set.range v :=
        Set.ext fun x ↦ by simp
      rw [hrange, ← hspan]
      exact Submodule.subset_span ⟨Fin.last r, rfl⟩
    · have ha_smul : exteriorFlagVector k r (u ∘ Fin.castSucc) =
          (a⁻¹.val * c) • exteriorFlagVector k r (v ∘ Fin.castSucc) := by
        rw [mul_smul, ← Units.smul_def, ha₁, inv_smul_smul]
      have hi := ih (hv.comp Fin.castSucc (Fin.castSucc_injective r))
        (mul_ne_zero a⁻¹.ne_zero hc) ha_smul i
      have hcomp : (v ∘ Fin.castSucc) ∘ Fin.castLE i.isLt =
          v ∘ Fin.castLE i.castSucc.isLt := rfl
      rwa [hcomp] at hi

/-- A linear automorphism `f : M ≃ₗ[k] M` whose induced map on `FlagSpace k M d` preserves the
line spanned by `exteriorFlagVector k d b` has upper-triangular matrix in `b`. -/
theorem isUpperTriangular_toMatrix_of_exteriorFlagMap_mem_span {d : ℕ}
    (b : Module.Basis (Fin d) k M) (f : M ≃ₗ[k] M)
    (hf : exteriorFlagMap d f.toLinearMap (exteriorFlagVector k d b) ∈
      k ∙ exteriorFlagVector k d b) :
    (LinearMap.toMatrix b b f.toLinearMap).IsUpperTriangular := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  rw [exteriorFlagMap_exteriorFlagVector] at hc
  have hfb : LinearIndependent k (f.toLinearMap ∘ b) :=
    b.linearIndependent.map' f.toLinearMap f.ker
  have hc0 : c ≠ 0 :=
    fun h0 ↦ (exteriorFlagVector_ne_zero_iff.mpr hfb) (by rw [← hc, h0, zero_smul])
  intro i j hji
  rw [LinearMap.toMatrix_apply]
  have hmem := mem_span_prefix_of_exteriorFlagVector_eq_smul b.linearIndependent hc0 hc.symm j
  have hset : Set.range (b ∘ Fin.castLE j.isLt) = b '' {t : Fin d | t.castSucc < j.succ} := by
    rw [Set.range_comp, Fin.range_castLE]
    rfl
  rw [hset, ← Module.Basis.flag] at hmem
  exact b.flag_le_ker_coord (Fin.le_def.mpr (Nat.succ_le_of_lt hji)) hmem

end TauCeti.exteriorPower
