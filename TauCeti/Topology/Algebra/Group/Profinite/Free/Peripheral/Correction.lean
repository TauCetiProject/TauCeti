/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Lifting

/-!
# An explicit peripheral correction at exponent three

For a pair `x₀, x₁` in a pro-`p` group, the uncorrected peripheral defect at exponent `3` has
class `3 · [x₀, x₁]` in the first graded piece of the closed lower central series.
Conjugating `x₁ ^ 3` by `x₀` contributes the opposite class. Thus the explicit conjugators
`(1, x₀)` on the basis and `1` on the cusp move the defect into the second term of the series.

This is the first nontrivial finite-level instance of the correction process used to construct
peripheral power automorphisms. In the dyadic case, `3` is a unit; by contrast, at exponent `2`
no choice of conjugators reaches the second level.

## Main result

* `TauCeti.Peripheral.three_correction_mem_level_two`: the conjugators `(1, x₀)` and `1` solve
  the peripheral product identity at exponent `3` modulo the second closed lower central series
  term. In particular, this gives the explicit correction for a rank-two free pro-`2` group.
-/

public section

namespace TauCeti.Peripheral

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [CompactSpace F] [TotallyDisconnectedSpace F]

/-- At exponent `3`, conjugating the second power in a pair by the first element cancels the first
graded defect. Explicitly, the conjugators `(1, x₀)` on the pair and the trivial cusp conjugator
have peripheral defect in `γ₂`. For `p = 2`, this is a correction at the unit exponent `3`. -/
theorem three_correction_mem_level_two (hF : IsProP p F) (x : Fin 2 → F) :
    (![1, x 0], 1) ∈ level hF x 3 2 := by
  rw [mem_level_iff, closedLowerCentralSeries_def]
  let N := pLowerCentralSeries 0 F 2
  rw [← QuotientGroup.eq_one_iff]
  let a : F := x 0
  let b : F := x 1
  let qa : F ⧸ N := a
  let qb : F ⧸ N := b
  let z : F ⧸ N := ⁅qb, qa⁆
  have hz (g : F) : Commute z (g : F ⧸ N) := by
    have h := (commute_mk_of_mem_pLowerCentralSeries
        (commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 b)
          (mem_pLowerCentralSeries_zero 0 a)) g).symm
    simpa only [z, qa, qb, ← QuotientGroup.mk'_apply, map_commutatorElement, zero_add,
      Nat.add_assoc] using h
  have hza : Commute z qa := hz a
  have hzb : Commute z qb := hz b
  have hconj : qa⁻¹ * qb ^ 3 * qa = z ^ 3 * qb ^ 3 := by
    -- Expose conjugation so the powered-commutator formula applies, then fold the local names.
    rw [show qa⁻¹ * qb ^ 3 * qa = MulAut.conj qa⁻¹ (qb ^ 3) by simp,
      conj_eq_commutatorElement_mul, commutatorElement_inv_left,
      ← hzb.symm.commutatorElement_pow_left 3]
    change qa⁻¹ * z ^ 3 * qa * qb ^ 3 = z ^ 3 * qb ^ 3
    rw [mul_assoc qa⁻¹ (z ^ 3) qa, (hza.pow_left 3).eq]
    simp only [inv_mul_cancel_left]
  have hpow : (qa * qb) ^ 3 = qa ^ 3 * qb ^ 3 * z ^ 3 := by
    exact Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
      hza.symm hzb.symm 3
  simp only [defect_def, hF.padicPow_ofNat, cusp_def, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, inv_one, one_mul, mul_one]
  -- The preceding simplification leaves the quotient coercion opaque; expose its group word.
  change ((a ^ 3 * (a⁻¹ * b ^ 3 * a) * ((a * b)⁻¹) ^ 3 : F) : F ⧸ N) = 1
  simp only [← QuotientGroup.mk'_apply, map_mul, map_inv, map_pow]
  -- Fold the quotient images into the local names used by the two collection identities.
  change qa ^ 3 * (qa⁻¹ * qb ^ 3 * qa) * (((qa * qb)⁻¹) ^ 3) = 1
  rw [hconj, (hzb.pow_pow 3 3).eq, ← mul_assoc, ← hpow, inv_pow, mul_inv_cancel]

end TauCeti.Peripheral
