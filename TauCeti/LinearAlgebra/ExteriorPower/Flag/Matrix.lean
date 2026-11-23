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
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.Unimodular

/-!
# Flag stabilizers and upper-triangular matrices

This file connects the stabilizer of an exterior flag line in `FlagSpace k M d` with upper
triangularity in the underlying basis `b : Module.Basis (Fin d) k M`.

## Main results

* `TauCeti.exteriorPower.exteriorFlagMap_mem_span_iff_isUpperTriangular_toMatrix`: a linear
  automorphism preserves the line spanned by `exteriorFlagVector k d b` if and only if its
  matrix in `b` is upper triangular.
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

private theorem exteriorFlagVector_mem_span_of_mem_prefix {d : ℕ} {v : Fin d → M}
    (hv : LinearIndependent k v) (f : M ≃ₗ[k] M)
    (hf : ∀ j : Fin d, f (v j) ∈ Submodule.span k (Set.range (v ∘ Fin.castLE j.isLt))) :
    exteriorFlagVector k d (f.toLinearMap ∘ v) ∈ k ∙ exteriorFlagVector k d v := by
  induction d with
  | zero =>
    have h0 : f.toLinearMap ∘ v = v := Subsingleton.elim _ _
    rw [h0]
    exact Submodule.mem_span_singleton_self _
  | succ r ih =>
    have hv' : LinearIndependent k (v ∘ Fin.castSucc) := hv.comp _ (Fin.castSucc_injective r)
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (ih hv' fun j ↦ by
      have hcomp : (v ∘ Fin.castSucc) ∘ Fin.castLE j.isLt =
          v ∘ Fin.castLE j.castSucc.isLt := rfl
      simpa [hcomp] using hf j.castSucc)
    have hfu : LinearIndependent k (f.toLinearMap ∘ v) := hv.map' f.toLinearMap f.ker
    have hle : Submodule.span k (Set.range (f.toLinearMap ∘ v)) ≤
        Submodule.span k (Set.range v) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.span_mono ?_ (hf j)
      rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castLE j.isLt i, rfl⟩
    have : Module.Finite k (Submodule.span k (Set.range v)) :=
      Module.Finite.span_of_finite k (Set.finite_range v)
    have hfin : Module.finrank k (Submodule.span k (Set.range (f.toLinearMap ∘ v))) =
        Module.finrank k (Submodule.span k (Set.range v)) := by
      rw [finrank_span_eq_card hfu, finrank_span_eq_card hv]
    obtain ⟨c₂, hc₂⟩ := _root_.exteriorPower.exists_units_smul_ιMulti_of_span_eq hfu hv
      (Submodule.eq_of_le_of_finrank_eq hle hfin)
    refine Submodule.mem_span_singleton.mpr ⟨c₁ * (c₂ : k), ?_⟩
    apply (flagSpaceSuccEquiv k M r).injective
    rw [flagSpaceSuccEquiv_exteriorFlagVector, map_smul, flagSpaceSuccEquiv_exteriorFlagVector,
      Function.comp_assoc, ← hc₁, hc₂, Units.smul_def, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul]

/-- A linear automorphism `f : M ≃ₗ[k] M` whose induced map on `FlagSpace k M d` preserves the
line spanned by `exteriorFlagVector k d b` has upper-triangular matrix in `b`, and conversely. -/
theorem exteriorFlagMap_mem_span_iff_isUpperTriangular_toMatrix {d : ℕ}
    (b : Module.Basis (Fin d) k M) (f : M ≃ₗ[k] M) :
    exteriorFlagMap d f.toLinearMap (exteriorFlagVector k d b) ∈ k ∙ exteriorFlagVector k d b ↔
      (LinearMap.toMatrix b b f.toLinearMap).IsUpperTriangular := by
  constructor
  · intro hf
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
  · intro htri
    rw [exteriorFlagMap_exteriorFlagVector]
    refine exteriorFlagVector_mem_span_of_mem_prefix b.linearIndependent f fun j ↦ ?_
    rw [← b.sum_repr (f (b j))]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hij : j < i
    · have hzero : b.repr (f (b j)) i = 0 := by
        simpa [LinearMap.toMatrix_apply] using htri hij
      simp [hzero]
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le (not_lt.mp hij)⟩, rfl⟩)

end TauCeti.exteriorPower
