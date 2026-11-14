/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Classical

/-!
# Simple-root coordinates and the highest root of type C

The positive roots in the pinned type `Cₙ` datum are `eₐ - e_b` for `a < b`, and
`eₐ + e_b` for `b ≤ a`, including `2eₐ` on the diagonal. This file computes their
coefficients in the Bourbaki-numbered simple roots. The last simple root is `2eₙ₋₁`,
so its coefficient is half the sum of the classical coordinates; every earlier
coefficient is a partial sum of those coordinates.

These formulas identify the actual index of the highest root as that of `2e₀`,
with coefficients `(2, …, 2, 1)`. The calculations take place in the integral
root lattice and include ranks one and two, independently of conventions for
valid Dynkin classification indices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public noncomputable section

namespace TauCeti.DynkinType

open Finset TypeC

variable {n : ℕ}

local notation "P" => typeCSimplyConnectedRootDatum n
local notation "b" => typeCSimplyConnectedBase n

private def simpleEquiv (n : ℕ) : Fin n ≃ (typeCSimplyConnectedBase n).support where
  toFun i := ⟨typeCSimpleIndex n i, by simp⟩
  invFun j := ⟨j, mem_support_typeCSimplyConnectedBase.mp j.2⟩
  left_inv _ := Fin.ext (by simp)
  right_inv _ := Subtype.ext (Fin.ext (by simp))

private def classicalPrefix (k : Fin n) : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  (∑ j ∈ univ.filter (· ≤ k), LinearMap.proj j).comp
    (classicalWeightEquiv n).toLinearMap

private lemma classicalPrefix_weight (k a : Fin n) :
    classicalPrefix k (weight n a) = if a ≤ k then 1 else 0 := by
  simp [classicalPrefix, Pi.single_apply, Finset.sum_ite_eq']

private lemma classicalWeightEquiv_simple (i : Fin n) :
    classicalWeightEquiv n ((P).root (typeCSimpleIndex n i)) =
      if h : (i : ℕ) + 1 < n then
        Pi.single i 1 - Pi.single ⟨i + 1, h⟩ 1 else Pi.single i 1 + Pi.single i 1 := by
  have hi : typeCIndexEquiv n (i, Order.succ i, false) = typeCSimpleIndex n i := by
    apply (typeCIndexEquiv n).symm.injective
    rw [Equiv.symm_apply_apply, typeCIndexEquiv_symm_typeCSimpleIndex]
  rw [← hi]
  split_ifs with h
  · have hs : Order.succ i = (⟨i + 1, h⟩ : Fin n) := Fin.ext (Fin.val_orderSucc_of_lt h)
    rw [hs, root_typeCIndexEquiv_of_lt (by exact_mod_cast Nat.lt_succ_self (i : ℕ))]
    simp only [signedWeight_false, map_sub, classicalWeightEquiv_weight]
    rw [classicalWeightEquiv_weight (⟨i + 1, h⟩ : Fin n)]
  · rw [Fin.orderSucc_eq_self_of_not_lt (by omega),
      root_typeCIndexEquiv_of_not_lt (lt_irrefl i)]
    simp

private lemma classicalPrefix_simple (k i : Fin n) :
    classicalPrefix k ((P).root (typeCSimpleIndex n i)) =
      if i = k then (if (k : ℕ) + 1 = n then 2 else 1) else 0 := by
  simp only [classicalPrefix, LinearMap.comp_apply, LinearEquiv.coe_coe,
    classicalWeightEquiv_simple, LinearMap.sum_apply, LinearMap.proj_apply]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dite_eq_left hi]
    simp only [Pi.sub_apply, Pi.single_apply, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', mem_filter, mem_univ, true_and]
    split_ifs <;> simp_all only [Fin.ext_iff, Fin.le_def] <;> omega
  · rw [dite_eq_right hi]
    simp only [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib,
      Finset.sum_ite_eq', mem_filter, mem_univ, true_and]
    split_ifs <;> simp_all only [Fin.ext_iff, Fin.le_def] <;> omega

/-- A partial sum of the classical coordinates reads off a simple-root coefficient.
At the last node it is twice that coefficient, because the last simple root is long. -/
private theorem typeC_rootCoefficients_mul (j : Fin (2 * n ^ 2)) (k : Fin n) :
    (b).rootCoefficients j ⟨typeCSimpleIndex n k, by simp⟩ * (if (k : ℕ) + 1 = n then 2 else 1) =
      ∑ a ∈ univ.filter (· ≤ k), classicalWeightEquiv n ((P).root j) a := by
  have h := congrArg (classicalPrefix k) ((b).sum_rootCoefficients_smul_root j)
  rw [map_sum, ← (simpleEquiv n).sum_comp] at h
  simp only [map_zsmul, simpleEquiv, Equiv.coe_fn_mk, classicalPrefix_simple, smul_eq_mul,
    mul_ite, mul_zero,
    Finset.sum_ite_eq', mem_univ, ite_true] at h
  simpa [simpleEquiv, classicalPrefix] using h

/-- The simple-root coefficients of the short root `±(eₐ - e_b)`, for `a < b`,
are `±1` on the interval from `a` through `b - 1` and zero elsewhere. -/
@[simp]
theorem rootCoefficients_typeCIndexEquiv_of_lt {a d : Fin n} (had : a < d)
    (s : Bool) (k : Fin n) :
    (b).rootCoefficients (typeCIndexEquiv n (a, d, s))
        ⟨typeCSimpleIndex n k, by simp⟩ =
      (if s then -1 else 1) * (if a ≤ k ∧ k < d then 1 else 0) := by
  have h := typeC_rootCoefficients_mul (typeCIndexEquiv n (a, d, s)) k
  have hp : classicalPrefix k ((P).root (typeCIndexEquiv n (a, d, s))) =
      (if s then -1 else 1) * ((if a ≤ k then 1 else 0) - (if d ≤ k then 1 else 0)) := by
    rw [root_typeCIndexEquiv_of_lt had]
    cases s <;> simp [classicalPrefix_weight, sub_eq_add_neg, add_comm]
  have h' : (b).rootCoefficients (typeCIndexEquiv n (a, d, s))
      ⟨typeCSimpleIndex n k, by simp⟩ * (if (k : ℕ) + 1 = n then 2 else 1) =
      (if s then -1 else 1) * ((if a ≤ k then 1 else 0) - (if d ≤ k then 1 else 0)) :=
    h.trans (by simpa [classicalPrefix] using hp)
  have ha := a.isLt
  have hd := d.isLt
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at h' ⊢
  all_goals split_ifs at h' ⊢ <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega

/-- The simple-root coefficients of `±(eₐ + e_b)`, for `b ≤ a`.
Before the final node they are the sum of the two interval indicators; the final
coefficient is `±1`. The diagonal includes the long roots `±2eₐ`. -/
@[simp]
theorem rootCoefficients_typeCIndexEquiv_of_not_lt {a d : Fin n} (had : ¬ a < d)
    (s : Bool) (k : Fin n) :
    (b).rootCoefficients (typeCIndexEquiv n (a, d, s))
        ⟨typeCSimpleIndex n k, by simp⟩ =
      (if s then -1 else 1) * (if (k : ℕ) + 1 = n then 1 else
        (if a ≤ k then 1 else 0) + (if d ≤ k then 1 else 0)) := by
  have h := typeC_rootCoefficients_mul (typeCIndexEquiv n (a, d, s)) k
  have hp : classicalPrefix k ((P).root (typeCIndexEquiv n (a, d, s))) =
      (if s then -1 else 1) * ((if a ≤ k then 1 else 0) + (if d ≤ k then 1 else 0)) := by
    rw [root_typeCIndexEquiv_of_not_lt had]
    cases s <;> simp [classicalPrefix_weight, add_comm]
  have h' : (b).rootCoefficients (typeCIndexEquiv n (a, d, s))
      ⟨typeCSimpleIndex n k, by simp⟩ * (if (k : ℕ) + 1 = n then 2 else 1) =
      (if s then -1 else 1) * ((if a ≤ k then 1 else 0) + (if d ≤ k then 1 else 0)) :=
    h.trans (by simpa [classicalPrefix] using hp)
  have ha := a.isLt
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at h' ⊢
  all_goals split_ifs at h' ⊢ <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega

/-- In Bourbaki numbering, no root of type `Cₙ` has a coefficient greater than
`2` at an earlier node or greater than `1` at the final node. -/
theorem rootCoefficients_typeC_le (j : Fin (2 * n ^ 2)) (k : Fin n) :
    (b).rootCoefficients j ⟨typeCSimpleIndex n k, by simp⟩ ≤
      if (k : ℕ) + 1 = n then 1 else 2 := by
  obtain ⟨⟨a, d, s⟩, rfl⟩ := (typeCIndexEquiv n).surjective j
  by_cases had : a < d
  · rw [rootCoefficients_typeCIndexEquiv_of_lt had]
    cases s <;> split_ifs <;> norm_num
  · rw [rootCoefficients_typeCIndexEquiv_of_not_lt had]
    cases s <;> split_ifs <;> norm_num

/-- The highest root of the pinned integral type `Cₙ` datum is the root with
classical coordinates `2e₀`. This specifies its actual enumerated root index. -/
theorem highestRoot_typeCSimplyConnectedBase [NeZero n] :
    (b).highestRoot = typeCIndexEquiv n (0, 0, false) := by
  let θ := typeCIndexEquiv n (0, 0, false)
  have hle (k : (b).support) : (b).rootCoefficients (b).highestRoot k ≤
      (b).rootCoefficients θ k := by
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    simpa [simpleEquiv, θ, Fin.le_def] using rootCoefficients_typeC_le (b).highestRoot i
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, (b).rootCoefficients (b).highestRoot k ≠
      (b).rootCoefficients θ k := by
    by_contra! heq
    exact hne ((b).rootCoefficients_injective (funext heq))
  have hlt := Finset.sum_lt_sum (fun k (_ : k ∈ univ) ↦ hle k)
    ⟨k, mem_univ k, (hle k).lt_of_ne hk⟩
  rw [(b).sum_rootCoefficients_eq_height, (b).sum_rootCoefficients_eq_height] at hlt
  exact hlt.not_ge ((b).height_le_height_highestRoot θ)

/-- The simple-root coefficients of the highest root of type `Cₙ` are
`(2, …, 2, 1)` in the pinned Bourbaki numbering. -/
@[simp]
theorem rootCoefficients_highestRoot_typeC [NeZero n] (k : Fin n) :
    (b).rootCoefficients (b).highestRoot ⟨typeCSimpleIndex n k, by simp⟩ =
      if (k : ℕ) + 1 = n then 1 else 2 := by
  rw [highestRoot_typeCSimplyConnectedBase]
  simp

/-- The highest root of the integral type `Cₙ` datum lies above every root in
the positive root cone. No integral spanning or irreducibility assumption is needed. -/
theorem root_highestRoot_sub_mem_posRootCone_typeC [NeZero n] (j : Fin (2 * n ^ 2)) :
    (P).root (b).highestRoot - (P).root j ∈ posRootCone P b := by
  rw [← (b).sum_rootCoefficients_smul_root (b).highestRoot,
    ← (b).sum_rootCoefficients_smul_root j, ← Finset.sum_sub_distrib]
  apply AddSubmonoid.sum_mem
  intro k _
  rw [← sub_smul]
  have hle : (b).rootCoefficients j k ≤ (b).rootCoefficients (b).highestRoot k := by
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    exact (rootCoefficients_typeC_le j i).trans_eq (rootCoefficients_highestRoot_typeC i).symm
  rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hle), natCast_zsmul]
  exact (posRootCone P b).nsmul_mem (root_mem_posRootCone_of_mem_posRoots P b
    ((mem_posRoots P b _).mpr (RootPairing.Base.isPos_of_mem_support k.2))) _

/-- The height of the highest root of type `Cₙ` is `2n - 1`. -/
@[simp]
theorem height_highestRoot_typeCSimplyConnectedBase [NeZero n] :
    (b).height (b).highestRoot = 2 * (n : ℤ) - 1 := by
  rw [← (b).sum_rootCoefficients_eq_height, ← (simpleEquiv n).sum_comp]
  simp only [simpleEquiv, Equiv.coe_fn_mk, rootCoefficients_highestRoot_typeC]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sum_univ_castSucc]
  have hi (i : Fin m) : (i : ℕ) ≠ m := Nat.ne_of_lt i.isLt
  simp [hi]
  omega

/-- The sign bit of an encoded type `Cₙ` root detects positivity in the pinned base. -/
@[simp]
theorem isPos_typeCIndexEquiv_iff (a d : Fin n) (s : Bool) :
    (b).IsPos (typeCIndexEquiv n (a, d, s)) ↔ s = false := by
  rw [← (b).zero_le_rootCoefficients_iff]
  constructor
  · intro h
    cases s with
    | false => rfl
    | true =>
      by_cases had : a < d
      · have ha := h ⟨typeCSimpleIndex n a, by simp⟩
        rw [rootCoefficients_typeCIndexEquiv_of_lt had] at ha
        simp [had] at ha
      · have hd := h ⟨typeCSimpleIndex n a, by simp⟩
        rw [rootCoefficients_typeCIndexEquiv_of_not_lt had] at hd
        have hda : d ≤ a := le_of_not_gt had
        split_ifs at hd <;> simp_all
  · rintro rfl k
    obtain ⟨i, rfl⟩ := (simpleEquiv n).surjective k
    simp only [simpleEquiv, Equiv.coe_fn_mk, Pi.zero_apply]
    by_cases had : a < d
    · rw [rootCoefficients_typeCIndexEquiv_of_lt had]
      split_ifs <;> simp_all
    · rw [rootCoefficients_typeCIndexEquiv_of_not_lt had]
      split_ifs <;> simp_all

/-- The pinned type `Cₙ` datum has `n²` positive roots, including rank zero. -/
theorem ncard_posRoots_typeCSimplyConnectedBase (n : ℕ) :
    (posRoots (typeCSimplyConnectedRootDatum n) (typeCSimplyConnectedBase n)).ncard = n ^ 2 := by
  have h := two_mul_ncard_posRoots (typeCSimplyConnectedRootDatum n) (typeCSimplyConnectedBase n)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

end TauCeti.DynkinType

end
