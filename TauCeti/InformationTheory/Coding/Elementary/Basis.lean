/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.InformationTheory.Coding.Elementary.Basic
import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# The adjacent-difference basis of the single-parity-check code

Over any ring `R`, the single-parity-check code `TauCeti.singleParityCheckCode R (Fin (n + 1))`
consists of the tuples `x : Fin (n + 1) → R` with coordinate sum zero. The `n` adjacent-difference
vectors `eᵢ - eᵢ₊₁` (`0 ≤ i < n`) form a free `R`-basis
`TauCeti.singleParityCheckCodeBasis R n` of this submodule, and the coordinates of a vector `x` in
this basis are its initial partial sums `x₀ + ⋯ + xᵢ`:

```text
x = ∑ i : Fin n, (∑ j ∈ Iic i.castSucc, x j) • (eᵢ - eᵢ₊₁).
```

This is simultaneously a bidiagonal basis for the single-parity-check code and the Bourbaki
simple-root basis of the classical zero-sum hyperplane of type `Aₙ`.

## Main declarations

* `TauCeti.singleParityCheckCodeBasis`: the adjacent-difference `R`-basis `{eᵢ - eᵢ₊₁}` of
  `singleParityCheckCode R (Fin (n + 1))`.
* `TauCeti.coe_singleParityCheckCodeBasis_apply`: the `i`-th basis vector coerces to
  `Pi.single i.castSucc 1 - Pi.single i.succ 1`.
* `TauCeti.singleParityCheckCodeBasis_repr_apply`: the `i`-th coordinate of `x` in this basis is
  the partial sum `∑ j ∈ Iic i.castSucc, (x : Fin (n + 1) → R) j`.
* `TauCeti.sum_smul_coe_singleParityCheckCodeBasis`: the partial-sum expansion of any vector in
  `singleParityCheckCode R (Fin (n + 1))`.
* `TauCeti.linearIndependent_coe_singleParityCheckCodeBasis`: the adjacent-difference vectors are
  `R`-linearly independent in `Fin (n + 1) → R`.
-/

public section

namespace TauCeti

open Finset

section Ring

variable (R : Type*) [Ring R]

private def singleParityCheckAdjacentDiff (n : ℕ) (i : Fin n) :
    singleParityCheckCode R (Fin (n + 1)) :=
  ⟨Pi.single i.castSucc 1 - Pi.single i.succ 1, by simp [sum_sub_distrib]⟩

private lemma sum_Iic_singleParityCheckAdjacentDiff {n : ℕ} (i k : Fin n) :
    ∑ j ∈ Iic k.castSucc, (singleParityCheckAdjacentDiff R n i : Fin (n + 1) → R) j =
      if i = k then 1 else 0 := by
  simp only [singleParityCheckAdjacentDiff, Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_Iic,
    Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> first | (simp; done) | (exfalso; omega)

private lemma sum_Iic_sum_smul_adjacentDiff {n : ℕ} (c : Fin n → R) (k : Fin n) :
    ∑ j ∈ Iic k.castSucc, ((∑ i : Fin n, c i • singleParityCheckAdjacentDiff R n i :
      singleParityCheckCode R (Fin (n + 1))) : Fin (n + 1) → R) j = c k := by
  simp_rw [Submodule.coe_sum, Finset.sum_apply]
  rw [sum_comm]
  simp_rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum,
    sum_Iic_singleParityCheckAdjacentDiff R]
  simp

private def singleParityCheckCoordEquiv (n : ℕ) :
    singleParityCheckCode R (Fin (n + 1)) ≃ₗ[R] (Fin n → R) where
  toFun x i := ∑ j ∈ Iic i.castSucc, (x : Fin (n + 1) → R) j
  map_add' _ _ := by ext; simp [sum_add_distrib]
  map_smul' _ _ := by ext; simp [mul_sum]
  invFun y := ∑ i : Fin n, y i • singleParityCheckAdjacentDiff R n i
  right_inv y := funext (sum_Iic_sum_smul_adjacentDiff R y)
  left_inv x := by
    refine sub_eq_zero.mp (Subtype.ext (eq_zero_of_forall_sum_Iic_eq_zero <| Fin.lastCases ?_ ?_))
    · rw [eq_univ_of_forall fun j ↦ mem_Iic.mpr (Fin.le_last j)]
      exact (mem_singleParityCheckCode R (Fin (n + 1))).mp
        ((∑ i : Fin n, (∑ j ∈ Iic i.castSucc, (x : Fin (n + 1) → R) j) •
          singleParityCheckAdjacentDiff R n i) - x).property
    · intro k
      simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, sum_sub_distrib, sub_eq_zero]
      exact sum_Iic_sum_smul_adjacentDiff R _ k

private lemma singleParityCheckCoordEquiv_apply (n : ℕ)
    (x : singleParityCheckCode R (Fin (n + 1))) (i : Fin n) :
    singleParityCheckCoordEquiv R n x i = ∑ j ∈ Iic i.castSucc, (x : Fin (n + 1) → R) j := rfl

private lemma singleParityCheckCoordEquiv_symm_apply (n : ℕ) (y : Fin n → R) :
    (singleParityCheckCoordEquiv R n).symm y =
      ∑ i : Fin n, y i • singleParityCheckAdjacentDiff R n i := rfl

/-- **The adjacent-difference basis of `singleParityCheckCode R (Fin (n + 1))`**: the `i`-th
basis vector is `eᵢ - eᵢ₊₁`, and the `i`-th coordinate of a vector `x` is its partial sum
`∑ j ∈ Iic i.castSucc, x j`. -/
noncomputable def singleParityCheckCodeBasis (n : ℕ) :
    Module.Basis (Fin n) R (singleParityCheckCode R (Fin (n + 1))) :=
  Module.Basis.ofEquivFun (singleParityCheckCoordEquiv R n)

/-- The `i`-th vector of `singleParityCheckCodeBasis R n` coerces to `eᵢ - eᵢ₊₁`. -/
@[simp]
theorem coe_singleParityCheckCodeBasis_apply (n : ℕ) (i : Fin n) :
    (singleParityCheckCodeBasis R n i : Fin (n + 1) → R) =
      Pi.single i.castSucc 1 - Pi.single i.succ 1 := by
  rw [singleParityCheckCodeBasis, congrFun (Module.Basis.coe_ofEquivFun _) i,
    singleParityCheckCoordEquiv_symm_apply]
  simp [singleParityCheckAdjacentDiff, Pi.single_apply]

/-- Coordinate evaluation of the `i`-th vector of `singleParityCheckCodeBasis R n`. -/
theorem coe_singleParityCheckCodeBasis_apply_apply (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    (singleParityCheckCodeBasis R n i : Fin (n + 1) → R) j =
      (if j = i.castSucc then 1 else 0) - if j = i.succ then 1 else 0 := by
  simp [Pi.single_apply]

/-- The `i`-th coordinate of `x` in `singleParityCheckCodeBasis R n` is the partial sum
`∑ j ∈ Iic i.castSucc, x j`. -/
@[simp]
theorem singleParityCheckCodeBasis_repr_apply (n : ℕ)
    (x : singleParityCheckCode R (Fin (n + 1))) (i : Fin n) :
    (singleParityCheckCodeBasis R n).repr x i = ∑ j ∈ Iic i.castSucc, (x : Fin (n + 1) → R) j :=
  (Module.Basis.ofEquivFun_repr_apply _ x i).trans (singleParityCheckCoordEquiv_apply R n x i)

/-- **The partial-sum expansion.** Every tuple `x : Fin (n + 1) → R` with coordinate sum zero is
the linear combination of the adjacent-difference basis vectors `eₖ - eₖ₊₁` whose coefficients are
its initial partial sums `x₀ + ⋯ + xₖ`. -/
theorem sum_smul_coe_singleParityCheckCodeBasis {n : ℕ} {x : Fin (n + 1) → R}
    (hx : x ∈ singleParityCheckCode R (Fin (n + 1))) :
    ∑ k : Fin n, (∑ j ∈ Iic k.castSucc, x j) •
      (singleParityCheckCodeBasis R n k : Fin (n + 1) → R) = x := by
  have h := congrArg Subtype.val ((singleParityCheckCodeBasis R n).sum_repr ⟨x, hx⟩)
  simpa only [Submodule.coe_sum, SetLike.val_smul, singleParityCheckCodeBasis_repr_apply] using h

/-- The adjacent-difference basis vectors `eᵢ - eᵢ₊₁` are `R`-linearly independent in
`Fin (n + 1) → R`. -/
theorem linearIndependent_coe_singleParityCheckCodeBasis (n : ℕ) :
    LinearIndependent R fun i : Fin n ↦ (singleParityCheckCodeBasis R n i : Fin (n + 1) → R) :=
  (singleParityCheckCodeBasis R n).linearIndependent.map'
    (singleParityCheckCode R (Fin (n + 1))).subtype (Submodule.ker_subtype _)

end Ring

end TauCeti
