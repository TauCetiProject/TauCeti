/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.RingTheory.AdjoinRoot.OrderOf

/-!
# Multiplicative orders of companion matrices

For a monic polynomial `p` over a commutative ring `R`, `Polynomial.leftMulMatrix_root_eq_companion`
identifies `p.companion` with left multiplication by `AdjoinRoot.root p` in its power basis. Since
`Algebra.leftMulMatrix` is an injective ring homomorphism, `orderOf p.companion` equals
`orderOf (AdjoinRoot.root p)` (`Polynomial.orderOf_companion`). Specializing to `1 + X + ⋯ + X ^ n`
and `X ^ n + 1` gives orders `n + 1` and `2 * n` whenever `(2 : R) ≠ 0`.

## Main results

* `Polynomial.orderOf_companion`: `orderOf p.companion = orderOf (AdjoinRoot.root p)` for monic `p`.
* `Polynomial.orderOf_companion_geom_sum`: `orderOf (∑ k ∈ range (n + 1), X ^ k).companion = n + 1`
  when `(2 : R) ≠ 0`.
* `Polynomial.orderOf_companion_X_pow_add_one`: `orderOf (X ^ n + 1).companion = 2 * n` when
  `0 < n` and `(2 : R) ≠ 0`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **The multiplicative order of the companion matrix of a monic polynomial** equals the
multiplicative order of its adjoined root in `AdjoinRoot p`. -/
theorem orderOf_companion {p : R[X]} (hp : p.Monic) :
    orderOf p.companion = orderOf (AdjoinRoot.root p) := by
  rw [← leftMulMatrix_root_eq_companion hp]
  exact orderOf_injective (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis).toMonoidHom
    (Algebra.leftMulMatrix_injective _) (AdjoinRoot.root p)

/-- **The companion matrix of `1 + X + ⋯ + X ^ n` has multiplicative order `n + 1`** whenever
`(2 : R) ≠ 0`. -/
theorem orderOf_companion_geom_sum (n : ℕ) (h2 : (2 : R) ≠ 0) :
    orderOf (∑ k ∈ Finset.range (n + 1), (X : R[X]) ^ k).companion = n + 1 :=
  (orderOf_companion (monic_geom_sum_X (Nat.succ_ne_zero n))).trans
    (AdjoinRoot.orderOf_root_geom_sum n h2)

/-- **The companion matrix of `X ^ n + 1` has multiplicative order `2 * n`** whenever `0 < n` and
`(2 : R) ≠ 0`. -/
theorem orderOf_companion_X_pow_add_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (X ^ n + 1 : R[X]).companion = 2 * n :=
  (orderOf_companion (by simpa using monic_X_pow_add_C (1 : R) hn.ne')).trans
    (AdjoinRoot.orderOf_root_X_pow_add_one hn h2)

end Polynomial

end
