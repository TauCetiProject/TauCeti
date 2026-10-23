/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Lifting

/-!
# An explicit peripheral correction at odd exponents

For a pair `x₀, x₁` in a pro-`p` group and an odd exponent `u = 2k + 1`, the uncorrected
peripheral defect at exponent `u` has class `(u choose 2) · [x₀, x₁] = ku · [x₀, x₁]` in the first
graded piece of the closed lower central series. Conjugating `x₁ ^ u` by `x₀ ^ k` contributes the
opposite class. Thus the explicit conjugators `(1, x₀ ^ k)` on the pair and `1` on the cusp move
the defect into the second term of the series. The underlying class-two identity is
`Commute.mul_pow_two_mul_add_one_eq_pow_mul_inv_pow_mul_pow_mul_pow`.

The case `k = 1`, at exponent `3`, is the first nontrivial finite-level instance of the correction
process used to construct peripheral power automorphisms. In the dyadic case, `3` is a unit; by
contrast, for the basis of a rank-two free pro-`2` group no choice of conjugators reaches the
second level at exponent `2` (`TauCeti.Peripheral.level_two_eq_empty`).

## Main result

* `TauCeti.Peripheral.odd_correction_mem_level_two`: the conjugators `(1, x₀ ^ k)` and `1` solve
  the peripheral product identity at exponent `2k + 1` modulo the second closed lower central
  series term. In particular, at `k = 1` this gives the explicit correction at exponent `3` for a
  rank-two free pro-`2` group.
-/

public section

namespace TauCeti.Peripheral

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [CompactSpace F] [TotallyDisconnectedSpace F]

/-- At an odd exponent `2k + 1`, conjugating the second power in a pair by the `k`-th power of
the first element cancels the first graded defect. Explicitly, the conjugators `(1, x₀ ^ k)` on
the pair and the trivial cusp conjugator have peripheral defect in `γ₂`. For `k = 1` and `p = 2`,
this is a correction at the unit exponent `3`. -/
theorem odd_correction_mem_level_two (hF : IsProP p F) (x : Fin 2 → F) (k : ℕ) :
    (![1, x 0 ^ k], 1) ∈ level hF x ((2 * k + 1 : ℕ) : ℤ_[p]) 2 := by
  rw [mem_level_iff, closedLowerCentralSeries_def, ← QuotientGroup.eq_one_iff]
  set N := pLowerCentralSeries 0 F 2
  -- Modulo `γ₂`, the commutator of the two classes is central.
  have hc : ⁅x 1, x 0⁆ ∈ pLowerCentralSeries 0 F 1 :=
    commutator_mem_pLowerCentralSeries (j := 0) (k := 0) (mem_pLowerCentralSeries_zero 0 _)
      (mem_pLowerCentralSeries_zero 0 _)
  have hz (g : F) : Commute (g : F ⧸ N) ⁅(x 1 : F ⧸ N), (x 0 : F ⧸ N)⁆ := by
    simpa only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
      commute_mk_of_mem_pLowerCentralSeries hc g
  simp only [defect_def, hF.padicPow_natCast, cusp_def, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, inv_one, one_mul, mul_one, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_pow]
  rw [← (hz _).mul_pow_two_mul_add_one_eq_pow_mul_inv_pow_mul_pow_mul_pow (hz _), inv_pow,
    mul_inv_cancel]

end TauCeti.Peripheral
