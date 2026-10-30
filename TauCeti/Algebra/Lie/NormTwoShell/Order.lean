/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.Matrix.Reindex
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact periods of pinned actions on the signed shell Lie algebra

The pinned relabelling `Matrix.ShellLieAlgebra.reindex` of a symmetric integral
Gram matrix has the same order as its vertex permutation. Iterating it produces
the pinned relabelling of the permutation power, including its root-vector signs.
The Cartan coordinate vectors detect the permutation, even for an empty root shell.

For a positive-definite even Gram matrix these are the underlying linear maps of
the existing Lie equivalences. The period statements use function iteration and
the group of linear equivalences, so require no group structure on Lie equivalences.
They apply to disconnected diagrams and the empty diagram as well.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.8.
-/

public section

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)

/-- Powers of the pinned linear action retain the inversion signs of the permutation power. -/
theorem reindex_pow (hB : B.IsSymm) (n : ℕ) :
    (reindex σ hσ) ^ n = reindex (σ ^ n) (B.reindex_pow_eq_self σ σ hσ n) := by
  induction n with
  | zero => exact (reindex_refl (B := B)).symm
  | succ n ih =>
    rw [pow_succ', ih, LinearEquiv.mul_eq_trans]
    simpa only [Equiv.Perm.mul_def, pow_succ'] using
      reindex_trans (σ ^ n) (B.reindex_pow_eq_self σ σ hσ n) σ hB hσ

/-- The pinned linear action is faithful on vertex permutations, detected on Cartan vectors. -/
@[simp]
theorem reindex_eq_one_iff : reindex σ hσ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun e : ShellLieAlgebra B ≃ₗ[ℤ] ShellLieAlgebra B ↦
      (equivProd B (e (cartan B (Pi.single i 1)))).1) h
    simp only [reindex_cartan, Pi.single_comp_equiv, Equiv.symm_symm,
      LinearEquiv.coe_one, id_eq, equivProd_cartan] at hi
    exact Pi.single_left_injective (by norm_num : (1 : ℤ) ≠ 0) hi
  · rintro rfl
    exact reindex_refl

/-- The pinned action on the integral Lie carrier has the same order as the diagram action. -/
@[simp]
theorem orderOf_reindex (hB : B.IsSymm) : orderOf (reindex σ hσ) = orderOf σ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [reindex_pow σ hσ hB, reindex_eq_one_iff]

/-- A function iterate of the pinned action is the identity exactly at permutation periods.
This also states the exact period of the underlying map of the pinned Lie equivalence. -/
@[simp]
theorem reindex_iterate_eq_id_iff (hB : B.IsSymm) (n : ℕ) :
    (reindex σ hσ)^[n] = id ↔ σ ^ n = 1 := by
  rw [← LinearEquiv.coe_pow, ← (LinearEquiv.coe_one (R := ℤ) (M := ShellLieAlgebra B)),
    DFunLike.coe_fn_eq, reindex_pow σ hσ hB, reindex_eq_one_iff]

end Matrix.ShellLieAlgebra
