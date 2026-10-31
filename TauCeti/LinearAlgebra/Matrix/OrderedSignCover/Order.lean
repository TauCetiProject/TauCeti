/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.Reindex
public import TauCeti.LinearAlgebra.Matrix.Reindex
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Orders of pinned relabellings of the ordered sign cover

A permutation preserving a symmetric integral Gram matrix acts on its ordered sign
cover by `Matrix.SignCover.reindex`. This is the lift preserving the simple lifts,
with the inversion signs built into its definition. Its powers are the pinned lifts
of the corresponding permutation powers, and its order is exactly the order of the
permutation. In particular no extra central sign appears after a full period.

These statements concern the pinned lift; arbitrary lifts fixing the central sign
can have different orders. No positive-definiteness or diagonal hypothesis is needed.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.8.
-/

public section

namespace Matrix

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The sign of a permutation power is the product of the signs along its lattice orbit. -/
theorem inversionSign_pow (B : Matrix I I ℤ) (σ : Equiv.Perm I) (hB : B.IsSymm)
    (hσ : B.reindex σ σ = B) (n : ℕ) (a : I → ℤ) :
    inversionSign B (σ ^ n) a =
      ∏ k ∈ Finset.range n, inversionSign B σ (a ∘ (σ ^ k).symm) := by
  induction n with
  | zero =>
    simp only [pow_zero, Finset.prod_range_zero]
    exact inversionSign_refl B a
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_def, inversionSign_trans B (σ ^ n) hB σ,
      B.reindex_pow_eq_self σ σ hσ n, ih, Finset.prod_range_succ]

/-- There is no residual sign after a full period of the vertex permutation. A shorter
root orbit can still have negative monodromy. -/
theorem prod_inversionSign_eq_one_of_pow_eq_one (B : Matrix I I ℤ) (σ : Equiv.Perm I)
    (hB : B.IsSymm) (hσ : B.reindex σ σ = B) {n : ℕ} (hn : σ ^ n = 1) (a : I → ℤ) :
    (∏ k ∈ Finset.range n, inversionSign B σ (a ∘ (σ ^ k).symm)) = 1 := by
  rw [← inversionSign_pow B σ hB hσ n a, hn]
  exact inversionSign_refl B a

end Matrix

namespace Matrix.SignCover

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  (σ : Equiv.Perm I) (hB : B.IsSymm) (hσ : B.reindex σ σ = B)

attribute [local instance] TauCeti.trivialMulDistribMulAction

/-- Powers of the pinned cover lift are the pinned lifts of permutation powers. -/
theorem reindex_pow (n : ℕ) :
    (reindex σ hB hσ) ^ n = reindex (σ ^ n) hB (B.reindex_pow_eq_self σ σ hσ n) := by
  induction n with
  | zero => exact (reindex_refl (B := B) hB).symm
  | succ n ih =>
    rw [pow_succ', ih, MulAut.mul_def]
    simpa only [Equiv.Perm.mul_def, pow_succ'] using
      reindex_trans (σ ^ n) σ hB (B.reindex_pow_eq_self σ σ hσ n) hB hσ

/-- A pinned cover lift is the identity exactly when its vertex permutation is. -/
@[simp]
theorem reindex_eq_one_iff : reindex σ hB hσ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun e : SignCover B ≃* SignCover B ↦
      (e ((signFactorSet B).canonicalSection
        (.ofAdd (Pi.single i 1)))).right.toAdd) h
    rw [reindex_canonicalSection_single] at hi
    apply Pi.single_left_injective (by norm_num : (1 : ℤ) ≠ 0)
    simpa only [TauCeti.FactorSet.canonicalSection_apply, MulAut.one_apply,
      toAdd_ofAdd, Equiv.Perm.one_apply] using hi
  · rintro rfl
    exact reindex_refl hB

/-- The pinned cover lift has precisely the same order as the vertex permutation. -/
@[simp]
theorem orderOf_reindex : orderOf (reindex σ hB hσ) = orderOf σ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [reindex_pow, reindex_eq_one_iff]

end Matrix.SignCover
