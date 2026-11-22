/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.GroupTheory.Perm.Inversion

/-!
# Block and interleaved orders of a basis of pairs

A basis `B` indexed by `Fin n × Fin 2` consists of `n` pairs `(B (i, 0), B (i, 1))`. It can be
listed in two natural orders:

* the **interleaved** order `(B (0, 0), B (0, 1), B (1, 0), B (1, 1), …)`, the reindexing of `B`
  along `finProdFinEquiv`;
* the **block** order `(B (0, 0), …, B (n - 1, 0), B (0, 1), …, B (n - 1, 1))`, all first members
  before all second members.

The two orders differ by the shuffle placing the first block at the even positions and the second
block at the odd positions (`TauCeti.finSumFinEquivInterleave`). Its inversions are the pairs
`(B (i, 1), B (j, 0))` with `i < j`, so there are `n.choose 2 = n (n - 1) / 2` of them
(`TauCeti.sign_finSumFinEquivInterleave`), and the two orientations differ by `(-1) ^ n.choose 2`
(`Module.Basis.orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex`).

For a complex vector space and a real basis `(v₁, …, vₙ)` of a maximal totally real subspace, the
interleaved order `(v₁, i v₁, …, vₙ, i vₙ)` gives the complex orientation, while the block order
`(v₁, …, vₙ, i v₁, …, i vₙ)` is the orientation of the subspace followed by its `i`-image. So the
identification of a totally real subspace with its normal space by the complex structure changes
the induced orientation by `(-1) ^ n.choose 2`: it preserves it for `n = 1` and reverses it for
`n = 2`. This is the sign behind the self-intersection `-2` of a Lagrangian sphere in a symplectic
four-manifold.

## Main results

* `Module.Basis.orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex`: a basis listing
  the pairs of `B` in block order has the orientation `(-1) ^ n.choose 2` times that of `B`
  listed in interleaved order.
-/

public section

open Module

namespace Module.Basis

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- **Block versus interleaved order.** Let `B` be a basis indexed by `Fin n × Fin 2`, and let `c`
be the basis listing the pairs of `B` in block order: first `B (0, 0), …, B (n - 1, 0)`, then
`B (0, 1), …, B (n - 1, 1)`. Its orientation is `(-1) ^ n.choose 2` times that of the interleaved
listing `B (0, 0), B (0, 1), B (1, 0), B (1, 1), …`. -/
theorem orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex
    (B : Basis (Fin n × Fin 2) R M) (c : Basis (Fin (n + n)) R M)
    (h₀ : ∀ i, c (Fin.castAdd n i) = B (i, 0)) (h₁ : ∀ i, c (Fin.natAdd n i) = B (i, 1)) :
    c.orientation = (-1 : Rˣ) ^ n.choose 2 •
      (B.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))).orientation := by
  set σ : Equiv.Perm (Fin (n + n)) :=
    finSumFinEquiv.symm.trans (TauCeti.finSumFinEquivInterleave n)
  -- `c` is the interleaved basis read along the shuffle `σ`.
  have hc : c = (B.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))).reindex σ.symm := by
    refine Basis.eq_of_apply_eq fun j ↦ Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · rw [h₀, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_symm]
      congr 1
      apply (finProdFinEquiv.trans (finCongr (Nat.mul_two n))).injective
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.apply_symm_apply]
      ext
      simp [Nat.mul_comm]
    · rw [h₁, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_symm]
      congr 1
      apply (finProdFinEquiv.trans (finCongr (Nat.mul_two n))).injective
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.apply_symm_apply]
      ext
      simp [Nat.mul_comm, Nat.add_comm]
  rw [hc, Basis.orientation_reindex, Orientation.reindex_perm, Equiv.Perm.sign_symm,
    TauCeti.sign_finSumFinEquivInterleave]
  simp

end Module.Basis
