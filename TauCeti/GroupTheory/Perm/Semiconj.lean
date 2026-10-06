/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cycles of permutations intertwined by a map

Let `f : α → β` intertwine a permutation `σ` of `α` with a permutation `τ` of `β`, that is
`f (σ x) = τ (f x)` for every `x` (`Function.Semiconj f σ τ`). Then `f` carries the cycle of `x`
onto the cycle of `f x`, going round it a whole number of times. This file records the resulting
relations between the cycle data of `σ` and of `τ`:

* `Function.Semiconj.minimalPeriod_dvd`: the length of the cycle of `f x` divides the length of
  the cycle of `x`.
* `Function.Semiconj.ncard_sameCycle_and_eq_mul_minimalPeriod`: more precisely, the length of the
  cycle of `x` is the length of the cycle of `f x` times the number of points of the cycle of `x`
  that lie in the fibre of `f` through `x`.
* `TauCeti.orbitCount_le_mul_orbitCount_of_semiconj`: if every fibre of `f` has at most `s`
  points, then `σ` has at most `s` times as many cycles as `τ`.

The typical instance is a permutation preserving a partition of `α` into blocks, with `f` the map
sending a point to its block and `τ` the induced permutation of the blocks. The cycle of a block
then has length the cycle length of any of its points divided by the number of points that cycle
has in the block.
-/

public section

open Equiv Equiv.Perm Function MulAction

variable {α β : Type*}

namespace Function.Semiconj

variable {f : α → β} {fa : α → α} {fb : β → β}

/-- If `f` intertwines `fa` with `fb`, the minimal period of `f x` under `fb` divides the
minimal period of `x` under `fa`. When `x` is not periodic the right side is `0`. -/
theorem minimalPeriod_dvd (h : Semiconj f fa fb) (x : α) :
    minimalPeriod fb (f x) ∣ minimalPeriod fa x :=
  ((isPeriodicPt_minimalPeriod fa x).map h).minimalPeriod_dvd

variable {σ : Perm α} {τ : Perm β}

/-- If `f` intertwines the permutations `σ` and `τ`, the points of the cycle of `x` that `f`
sends to `f x` form a single cycle of `σ ^ k`, where `k` is the length of the cycle of `f x`. -/
theorem setOf_sameCycle_and_eq (h : Semiconj f σ τ) (x : α) :
    {y | σ.SameCycle x y ∧ f y = f x} = {y | (σ ^ minimalPeriod τ (f x)).SameCycle x y} := by
  have hσ : ∀ i : ℤ, f ((σ ^ i) x) = (τ ^ i) (f x) := fun i ↦ by
    have hinv : Semiconj f ⇑(σ⁻¹) ⇑(τ⁻¹) := fun y ↦ by
      rw [Perm.eq_inv_iff_eq, ← h, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    rcases i with i | i
    · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, coe_pow, coe_pow]
      exact h.iterate_right i x
    · rw [zpow_negSucc, zpow_negSucc, ← inv_pow, ← inv_pow, coe_pow, coe_pow]
      exact hinv.iterate_right _ x
  have hk : ∀ i : ℤ, (τ ^ i) (f x) = f x ↔ (minimalPeriod τ (f x) : ℤ) ∣ i := fun i ↦
    zpow_smul_eq_iff_minimalPeriod_dvd (a := τ) (b := f x)
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨i, rfl⟩, hfy⟩
    obtain ⟨j, rfl⟩ := (hk i).1 (by rw [← hσ, hfy])
    exact ⟨j, by rw [← zpow_natCast, ← zpow_mul]⟩
  · rintro ⟨j, rfl⟩
    rw [← zpow_natCast, ← zpow_mul]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [hσ]
    exact (hk _).2 (dvd_mul_right _ _)

/-- **The cycle of a point wraps round the cycle of its image.** If `f` intertwines the
permutations `σ` and `τ` of finite types, the length of the cycle of `x` is the length of the
cycle of `f x` times the number of points of the cycle of `x` lying in the fibre of `f`
through `x`. -/
theorem ncard_sameCycle_and_eq_mul_minimalPeriod [Finite α] (h : Semiconj f σ τ) (x : α) :
    {y | σ.SameCycle x y ∧ f y = f x}.ncard * minimalPeriod τ (f x) = minimalPeriod σ x := by
  classical
  have := Fintype.ofFinite α
  set k := minimalPeriod τ (f x)
  have hσx : IsPeriodicPt σ (orderOf σ) x := by
    rw [IsPeriodicPt, IsFixedPt, ← coe_pow, pow_orderOf_eq_one, one_apply]
  have hk : 0 < k := (hσx.map h).minimalPeriod_pos (orderOf_pos σ)
  have hcard : {y | (σ ^ k).SameCycle x y}.ncard = minimalPeriod (σ ^ k) x := by
    simp_rw [sameCycle_iff_mem_orbit_zpowers, Set.ofPred_mem_eq, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact (minimalPeriod_eq_card (a := σ ^ k) (b := x)).symm
  rw [h.setOf_sameCycle_and_eq, hcard, coe_pow, minimalPeriod_iterate_eq_div_gcd hk.ne',
    Nat.gcd_eq_right (h.minimalPeriod_dvd x)]
  exact Nat.div_mul_cancel (h.minimalPeriod_dvd x)

end Function.Semiconj

namespace TauCeti

/-- If `f` intertwines the permutations `σ` and `τ` of finite types and every fibre of `f` has at
most `s` points, then `σ` has at most `s` times as many cycles as `τ`. -/
theorem orbitCount_le_mul_orbitCount_of_semiconj [Finite α] [Finite β] {f : α → β}
    {σ : Perm α} {τ : Perm β} (h : Semiconj f σ τ) {s : ℕ}
    (hs : ∀ y, (f ⁻¹' {y}).ncard ≤ s) :
    orbitCount σ ≤ s * orbitCount τ := by
  classical
  let Q := Quotient (SameCycle.setoid τ)
  have := Fintype.ofFinite Q
  -- Each cycle of `σ` is the cycle of a point lying over the representative of the cycle below.
  have hsurj : Surjective fun p : Σ c : Q, f ⁻¹' {c.out} ↦
      Quotient.mk (SameCycle.setoid σ) p.2.1 := by
    rintro ⟨x⟩
    obtain ⟨i, -, hi⟩ := (Quotient.mk_out (s := SameCycle.setoid τ) (f x)).symm.exists_pow_eq'
    refine ⟨⟨Quotient.mk _ (f x), (σ ^ i) x, ?_⟩,
      Quotient.sound (sameCycle_pow_left.2 (SameCycle.refl _ _))⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, coe_pow, h.iterate_right i x, ← coe_pow, hi]
  calc orbitCount σ = Nat.card (Quotient (SameCycle.setoid σ)) := orbitCount_def σ
    _ ≤ Nat.card (Σ c : Q, f ⁻¹' {c.out}) := Nat.card_le_card_of_surjective _ hsurj
    _ = ∑ c : Q, (f ⁻¹' {c.out}).ncard := by simp [Nat.card_sigma, Nat.card_coe_set_eq]
    _ ≤ ∑ _c : Q, s := Finset.sum_le_sum fun c _ ↦ hs c.out
    _ = s * orbitCount τ := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, orbitCount_def,
        Nat.card_eq_fintype_card]

end TauCeti
