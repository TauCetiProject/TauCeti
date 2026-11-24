/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Basic
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Basic

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
are proved from the coefficients rather than from the general highest-root theory, through the
coefficient-dominance criteria of `TauCeti.LinearAlgebra.RootSystem.CoefficientReflection`.
The arguments follow the type `C` file
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Positive`.

## Main results

* `TauCeti.DynkinType.rootCoefficients_typeASimplyConnectedBase`: the coefficients of a root are
  the coordinates of its coroot.
* `TauCeti.DynkinType.isPos_typeAIndexEquiv_iff`: `e_a - e_b` is positive exactly when `a < b`.
* `TauCeti.DynkinType.highestRoot_typeASimplyConnectedBase`: the highest root is `e₀ - eₙ`.
* `TauCeti.DynkinType.rootCoefficients_highestRoot_typeA` and
  `TauCeti.DynkinType.coroot_highestRoot_typeASimplyConnectedBase`: its coefficients and the
  coordinates of its coroot are `(1, …, 1)`.
* `TauCeti.DynkinType.root_highestRoot_sub_mem_posRootCone_typeA`: it lies above every root.
* `TauCeti.DynkinType.height_highestRoot_typeASimplyConnectedBase`: its height is `n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public noncomputable section

namespace TauCeti.DynkinType

open Finset
open scoped _root_.Matrix

variable {n : ℕ}

local notation "P" => typeASimplyConnectedRootDatum n
local notation "b" => typeASimplyConnectedBase n

private def simpleEquiv (n : ℕ) : Fin n ≃ (typeASimplyConnectedBase n).support where
  toFun i := ⟨typeASimpleIndex n i, by simp⟩
  invFun j := ⟨j, mem_typeASimplyConnectedBase_support.mp j.property⟩
  left_inv _ := Fin.ext (by simp)
  right_inv _ := Subtype.ext (Fin.ext (by simp))

/-- The coroot potential `[a ≤ k]` of `e_a` maps under the Cartan matrix to `e_a - e_n`, by
telescoping along the simple coroots `Pi.single i 1`, whose Cartan images are the simple roots. -/
private lemma typeACoweight_vecMul_cartanMatrix {a : ℕ} (ha : a ≤ n) :
    typeACoweight n a ᵥ* CartanMatrix.A n = typeAWeight n a - typeAWeight n n := by
  induction hd : n - a generalizing a with
  | zero =>
    obtain rfl : a = n := by omega
    have h : typeACoweight a a = 0 := by
      funext k
      simp only [typeACoweight, Pi.zero_apply]
      split_ifs <;> omega
    rw [h, Matrix.zero_vecMul, sub_self]
  | succ d ih =>
    have hrow : (CartanMatrix.A n).row ⟨a, by omega⟩ =
        typeAWeight n a - typeAWeight n (a + 1) := by
      rw [Matrix.row_apply', ← root_typeASimpleIndex_eq ⟨a, by omega⟩, root_typeASimpleIndex]
    rw [eq_add_of_sub_eq' (typeACoweight_sub_succ ⟨a, by omega⟩), Matrix.add_vecMul,
      Matrix.single_one_vecMul, hrow, ih (a := a + 1) (by omega) (by omega)]
    abel

/-- In type `Aₙ` a root is the combination of the simple roots whose coefficients are the
coordinates of its coroot: telescoping the coroot coordinates `[a ≤ k] - [b ≤ k]` of `e_a - e_b`
along the simple roots. -/
private lemma root_eq_sum_coroot_smul_root_typeASimpleIndex (j : Fin (n * (n + 1))) :
    (P).root j = ∑ i, (P).coroot j i • (P).root (typeASimpleIndex n i) := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective j
  have h : (P).root (typeAIndexEquiv n p) =
      (P).coroot (typeAIndexEquiv n p) ᵥ* CartanMatrix.A n := by
    rw [root_typeASimplyConnectedRootDatum, coroot_typeASimplyConnectedRootDatum,
      Equiv.symm_apply_apply, typeAPairRoot, typeAPairCoroot, Matrix.sub_vecMul,
      typeACoweight_vecMul_cartanMatrix (by omega), typeACoweight_vecMul_cartanMatrix (by omega)]
    abel
  rw [h]
  ext k
  simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    root_typeASimpleIndex]

/-- **The simple-root coefficients of a type `Aₙ` root are the coordinates of its coroot**, in the
Bourbaki numbering of the simple roots. For the root `e_a - e_b` they are `[a ≤ k] - [b ≤ k]`
(`TauCeti.DynkinType.coroot_typeAIndexEquiv`). -/
@[simp]
theorem rootCoefficients_typeASimplyConnectedBase (j : Fin (n * (n + 1))) (k : Fin n) :
    (b).rootCoefficients j ⟨typeASimpleIndex n k, by simp⟩ = (P).coroot j k :=
  (b).rootCoefficients_apply_of_injective typeASimpleIndex_injective (fun _ ↦ by simp)
    (root_eq_sum_coroot_smul_root_typeASimpleIndex j) k

/-- In Bourbaki numbering, no root of type `Aₙ` has a simple-root coefficient greater than `1`. -/
theorem rootCoefficients_typeA_le_one (j : Fin (n * (n + 1))) (k : (b).support) :
    (b).rootCoefficients j k ≤ 1 := by
  obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective j
  obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
  simp only [simpleEquiv, Equiv.coe_fn_mk, rootCoefficients_typeASimplyConnectedBase,
    coroot_typeAIndexEquiv]
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
    have hlt : (p.val.2 : ℕ) < p.val.1 := Fin.lt_def.mp (lt_of_le_of_ne hle (Ne.symm p.property))
    have hk : (p.val.2 : ℕ) < n := by
      have := p.val.1.isLt
      omega
    have h₀ := h ⟨typeASimpleIndex n ⟨p.val.2, hk⟩, by simpa using hk⟩
    rw [Pi.zero_apply, rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv] at h₀
    simp only [Fin.le_def, Fin.val_castSucc] at h₀
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
  refine ((b).eq_highestRoot_of_forall_rootCoefficients_le fun j k ↦ ?_).symm
  refine (rootCoefficients_typeA_le_one j k).trans_eq (Eq.symm ?_)
  obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
  simp [simpleEquiv, Fin.le_def]

/-- The coroot of the highest root of type `Aₙ` has all simple-coroot coordinates equal to `1`. -/
@[simp]
theorem coroot_highestRoot_typeASimplyConnectedBase [NeZero n] :
    (P).coroot (b).highestRoot = 1 := by
  ext k
  rw [highestRoot_typeASimplyConnectedBase, coroot_typeAIndexEquiv]
  simp [Fin.le_def]

/-- The simple-root coefficients of the highest root of type `Aₙ` are all `1`. -/
@[simp]
theorem rootCoefficients_highestRoot_typeA [NeZero n] :
    (b).rootCoefficients (b).highestRoot = 1 := by
  ext k
  obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
  simp [simpleEquiv]

/-- The highest root of the integral type `Aₙ` datum lies above every root in the positive root
cone. No integral spanning or irreducibility assumption is needed. -/
theorem root_highestRoot_sub_mem_posRootCone_typeA [NeZero n] (j : Fin (n * (n + 1))) :
    (P).root (b).highestRoot - (P).root j ∈ posRootCone P b :=
  (b).root_sub_root_mem_posRootCone_iff.mpr fun k ↦ by
    simpa using rootCoefficients_typeA_le_one j k

/-- The height of the highest root of type `Aₙ` is `n`. -/
@[simp]
theorem height_highestRoot_typeASimplyConnectedBase [NeZero n] :
    (b).height (b).highestRoot = n := by
  rw [← (b).sum_rootCoefficients_eq_height, ← (simpleEquiv n).sum_comp]
  simp

end TauCeti.DynkinType

end
