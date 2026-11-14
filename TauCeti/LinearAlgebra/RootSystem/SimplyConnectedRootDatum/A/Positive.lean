/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SimplyLaced

/-!
# Simple-root coefficients and the highest root of type A

Type `Aₙ` is simply laced, so the simple-root coefficients of a root of the pinned datum are the
simple-coroot coordinates of its coroot. For the root `e_a - e_b` these are `[a ≤ k] - [b ≤ k]`
at the Bourbaki node `k`: the indicator of the interval from `a` through `b - 1` when `a < b`, and
minus the indicator of the interval from `b` through `a - 1` when `b < a`. In particular a root is
positive exactly when `a < b`, and no coefficient exceeds `1`.

These formulas identify the actual index of the highest root as that of `e₀ - eₙ`, with all
coefficients equal to `1` and height `n`. Every root lies below it in the positive root cone. The
datum is not irreducible over `ℤ` in the sense of `RootPairing.IsIrreducible`, so these statements
are proved from the coefficients rather than from the general highest-root theory.

## Main results

* `TauCeti.DynkinType.rootCoefficients_typeASimplyConnectedBase`: the coefficients of a root are
  the coordinates of its coroot.
* `TauCeti.DynkinType.isPos_typeAIndexEquiv_iff`: `e_a - e_b` is positive exactly when `a < b`.
* `TauCeti.DynkinType.highestRoot_typeASimplyConnectedBase`: the highest root is `e₀ - eₙ`.
* `TauCeti.DynkinType.rootCoefficients_highestRoot_typeA`: its coefficients are `(1, …, 1)`.
* `TauCeti.DynkinType.root_highestRoot_sub_mem_posRootCone_typeA`: it lies above every root.
* `TauCeti.DynkinType.height_highestRoot_typeASimplyConnectedBase`: its height is `n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public noncomputable section

namespace TauCeti.DynkinType

open Finset

variable {n : ℕ}

local notation "P" => typeASimplyConnectedRootDatum n
local notation "b" => typeASimplyConnectedBase n

private def simpleEquiv (n : ℕ) : Fin n ≃ (typeASimplyConnectedBase n).support where
  toFun i := ⟨typeASimpleIndex n i, by simp⟩
  invFun j := ⟨j, mem_typeASimplyConnectedBase_support.mp j.2⟩
  left_inv _ := Fin.ext (by simp)
  right_inv _ := Subtype.ext (Fin.ext (by simp))

/-- The type `Aₙ` instance of `TauCeti.DynkinType.root_eq_sum_coroot_smul_root_simpleIndex`, read
on the family datum rather than through the dispatcher. -/
private lemma root_eq_sum_coroot_smul_root_typeASimpleIndex (j : Fin (n * (n + 1))) :
    (P).root j = ∑ i, (P).coroot j i • (P).root (typeASimpleIndex n i) := by
  obtain _ | m := n
  · exact j.elim0
  have ht : (A (m + 1)).Valid := valid_A.mpr (Nat.succ_pos m)
  have hs (i : Fin (m + 1)) : (A (m + 1)).simpleIndex ht i = typeASimpleIndex (m + 1) i :=
    Fin.ext ((simpleIndex_val _ ht i).trans (typeASimpleIndex_val i).symm)
  have h := root_eq_sum_coroot_smul_root_simpleIndex (A (m + 1)) ht (isSimplyLaced_A _) j
  simp only [simplyConnectedRootDatum_A] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact congrArg (fun k ↦ _ • (typeASimplyConnectedRootDatum (m + 1)).root k) (hs i)

/-- **The simple-root coefficients of a type `Aₙ` root are the coordinates of its coroot**, in the
Bourbaki numbering of the simple roots. For the root `e_a - e_b` they are `[a ≤ k] - [b ≤ k]`
(`TauCeti.DynkinType.coroot_typeAIndexEquiv`). -/
@[simp]
theorem rootCoefficients_typeASimplyConnectedBase (j : Fin (n * (n + 1))) (k : Fin n) :
    (b).rootCoefficients j ⟨typeASimpleIndex n k, by simp⟩ = (P).coroot j k := by
  have h : (b).rootCoefficients j = fun l ↦ (P).coroot j ((simpleEquiv n).symm l) := by
    rw [RootPairing.Base.rootCoefficients_eq_iff, ← (simpleEquiv n).sum_comp]
    simpa [simpleEquiv] using (root_eq_sum_coroot_smul_root_typeASimpleIndex j).symm
  rw [h]
  exact congrArg _ ((simpleEquiv n).symm_apply_eq.mpr rfl)

/-- In Bourbaki numbering, no root of type `Aₙ` has a simple-root coefficient greater than `1`. -/
theorem rootCoefficients_typeA_le_one (j : Fin (n * (n + 1))) (k : Fin n) :
    (b).rootCoefficients j ⟨typeASimpleIndex n k, by simp⟩ ≤ 1 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective j
  rw [rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv]
  split_ifs <;> norm_num

/-- **The root `e_a - e_b` of type `Aₙ` is positive exactly when `a < b`.** -/
@[simp]
theorem isPos_typeAIndexEquiv_iff (p : TypeAIndex n) :
    (b).IsPos (typeAIndexEquiv n p) ↔ p.val.1 < p.val.2 := by
  rw [← (b).zero_le_rootCoefficients_iff]
  constructor
  · intro h
    by_contra! hle
    -- At the node `p.2 < p.1 ≤ n` the coefficient is `0 - 1`.
    have hlt : p.val.2 < p.val.1 := lt_of_le_of_ne hle (Ne.symm p.2)
    have hk : (p.val.2 : ℕ) < n := by
      have := p.val.1.isLt
      have : (p.val.2 : ℕ) < p.val.1 := hlt
      omega
    have h₀ := h ⟨typeASimpleIndex n ⟨p.val.2, hk⟩, by simpa using hk⟩
    rw [Pi.zero_apply, rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv] at h₀
    simp only [Fin.le_def, Fin.val_castSucc] at h₀ hlt
    split_ifs at h₀ <;> omega
  · intro hlt k
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    simp only [simpleEquiv, Equiv.coe_fn_mk, Pi.zero_apply,
      rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv]
    simp only [Fin.lt_def] at hlt
    split_ifs <;> simp_all only [Fin.le_def] <;> omega

/-- The highest root of the pinned integral type `Aₙ` datum is `e₀ - eₙ`. This specifies its actual
enumerated root index. -/
theorem highestRoot_typeASimplyConnectedBase [NeZero n] :
    (b).highestRoot = typeAIndexEquiv n ⟨(0, Fin.last n), Fin.last_pos'.ne⟩ := by
  let θ := typeAIndexEquiv n ⟨(0, Fin.last n), Fin.last_pos'.ne⟩
  have hθ (k : (b).support) : (b).rootCoefficients θ k = 1 := by
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    simp [simpleEquiv, θ, Fin.le_def]
  have hle (k : (b).support) : (b).rootCoefficients (b).highestRoot k ≤
      (b).rootCoefficients θ k := by
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    rw [hθ]
    exact rootCoefficients_typeA_le_one (b).highestRoot i
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, (b).rootCoefficients (b).highestRoot k ≠
      (b).rootCoefficients θ k := by
    by_contra! heq
    exact hne ((b).rootCoefficients_injective (funext heq))
  have hlt := Finset.sum_lt_sum (fun k (_ : k ∈ univ) ↦ hle k)
    ⟨k, mem_univ k, (hle k).lt_of_ne hk⟩
  rw [(b).sum_rootCoefficients_eq_height, (b).sum_rootCoefficients_eq_height] at hlt
  exact hlt.not_ge ((b).height_le_height_highestRoot θ)

/-- The simple-root coefficients of the highest root of type `Aₙ` are all `1`. -/
theorem rootCoefficients_highestRoot_typeA [NeZero n] (k : Fin n) :
    (b).rootCoefficients (b).highestRoot ⟨typeASimpleIndex n k, by simp⟩ = 1 := by
  rw [highestRoot_typeASimplyConnectedBase]
  simp [Fin.le_def]

/-- The highest root of the integral type `Aₙ` datum lies above every root in the positive root
cone. No integral spanning or irreducibility assumption is needed. -/
theorem root_highestRoot_sub_mem_posRootCone_typeA [NeZero n] (j : Fin (n * (n + 1))) :
    (P).root (b).highestRoot - (P).root j ∈ posRootCone P b := by
  rw [← (b).sum_rootCoefficients_smul_root (b).highestRoot,
    ← (b).sum_rootCoefficients_smul_root j, ← Finset.sum_sub_distrib]
  apply AddSubmonoid.sum_mem
  intro k _
  rw [← sub_smul]
  have hle : (b).rootCoefficients j k ≤ (b).rootCoefficients (b).highestRoot k := by
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    exact (rootCoefficients_typeA_le_one j i).trans_eq (rootCoefficients_highestRoot_typeA i).symm
  rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hle), natCast_zsmul]
  exact (posRootCone P b).nsmul_mem (root_mem_posRootCone_of_mem_posRoots P b
    ((mem_posRoots P b _).mpr (RootPairing.Base.isPos_of_mem_support k.2))) _

/-- The height of the highest root of type `Aₙ` is `n`. -/
@[simp]
theorem height_highestRoot_typeASimplyConnectedBase [NeZero n] :
    (b).height (b).highestRoot = n := by
  rw [← (b).sum_rootCoefficients_eq_height, ← (simpleEquiv n).sum_comp]
  simp only [simpleEquiv, Equiv.coe_fn_mk, rootCoefficients_highestRoot_typeA]
  simp

end TauCeti.DynkinType

end
