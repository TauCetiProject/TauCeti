/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
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
      rw [Perm.eq_inv_iff_eq, ← h, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
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
    exact ⟨j, by rw [← zpow_natCast, ← _root_.zpow_mul]⟩
  · rintro ⟨j, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul]
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
    rw [IsPeriodicPt, IsFixedPt, ← coe_pow, pow_orderOf_eq_one, Equiv.Perm.one_apply]
  have hk : 0 < k := (hσx.map h).minimalPeriod_pos (orderOf_pos σ)
  rw [h.setOf_sameCycle_and_eq, ncard_setOf_sameCycle, coe_pow,
    minimalPeriod_iterate_eq_div_gcd hk.ne', Nat.gcd_eq_right (h.minimalPeriod_dvd x)]
  exact Nat.div_mul_cancel (h.minimalPeriod_dvd x)

/-- The map on cycle quotients induced by a semiconjugacy `Function.Semiconj f σ τ`. -/
def cycleQuotientMap (h : Semiconj f σ τ) :
    Quotient (SameCycle.setoid σ) → Quotient (SameCycle.setoid τ) :=
  Quotient.map f fun _ _ hxy ↦ hxy.map h

/-- `h.cycleQuotientMap` sends the cycle of `x` to the cycle of `f x`. -/
@[simp]
theorem cycleQuotientMap_mk (h : Semiconj f σ τ) (x : α) :
    h.cycleQuotientMap (Quotient.mk _ x) = Quotient.mk _ (f x) :=
  (rfl)

/-- The cycle length of `f x` divides the cycle length of `x`, at the level of cycle quotients. -/
theorem minimalPeriod_cycleQuotientMap_dvd (h : Semiconj f σ τ)
    (q : Quotient (SameCycle.setoid σ)) :
    Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
        (fun _ _ hxy ↦ hxy.minimalPeriod_eq) (h.cycleQuotientMap q) ∣
      Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
        (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q := by
  induction q using Quotient.ind with | _ x =>
  exact h.minimalPeriod_dvd x

/-- For a finite permutation semiconjugacy, the sum of the cycle lengths of `σ` over the fibre of
`h.cycleQuotientMap` above `c` equals the number of points of `α` mapped into `c`. -/
theorem sum_minimalPeriod_cycleQuotientMap_fiber_eq_natCard [Finite α]
    (h : Semiconj f σ τ) (c : Quotient (SameCycle.setoid τ)) :
    ∑ᶠ q ∈ {q | h.cycleQuotientMap q = c},
        Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q =
      Nat.card {y : α // Quotient.mk (SameCycle.setoid τ) (f y) = c} := by
  classical
  have := Fintype.ofFinite α
  have : Fintype (Quotient (SameCycle.setoid σ)) := Fintype.ofFinite _
  have hSfin : ({q | h.cycleQuotientMap q = c} : Set _).Finite := Set.toFinite _
  let t : Finset (Quotient (SameCycle.setoid σ)) :=
    Finset.univ.filter (fun q ↦ h.cycleQuotientMap q = c)
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin,
    show hSfin.toFinset = t by ext; simp [t]]
  have hcard : ∀ q ∈ t,
      Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q =
        (Finset.univ.filter (fun y : α ↦ Quotient.mk (SameCycle.setoid σ) y = q)).card := by
    intro q _
    induction q using Quotient.ind with | _ x =>
    rw [Quotient.lift_mk, ← Perm.natCard_fiber_quotientMk_sameCycle σ x, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [Finset.sum_congr rfl hcard, Finset.sum_card_fiberwise_eq_card_filter,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1; ext y
  simp [t]

/-- If every fibre of `f` has `k` elements, then the cycle lengths of `σ` over a cycle `c` of `τ`
sum to `k` times the cycle length of `c`. -/
theorem sum_minimalPeriod_cycleQuotientMap_fiber_eq_mul [Finite α] [Finite β]
    (h : Semiconj f σ τ) {k : ℕ} (hk : ∀ b : β, Nat.card {a : α // f a = b} = k)
    (c : Quotient (SameCycle.setoid τ)) :
    ∑ᶠ q ∈ {q | h.cycleQuotientMap q = c},
        Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q =
      k * Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) c := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  let eSigma :
      {y : α // Quotient.mk (SameCycle.setoid τ) (f y) = c} ≃
        Σ x : {x : β // Quotient.mk (SameCycle.setoid τ) x = c}, {y : α // f y = x.val} :=
    { toFun := fun ⟨y, hy⟩ ↦ ⟨⟨f y, hy⟩, ⟨y, rfl⟩⟩
      invFun := fun ⟨⟨_, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨y, hy ▸ hx⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, rfl⟩⟩ ↦ rfl }
  have hcyc : Nat.card {x : β // Quotient.mk (SameCycle.setoid τ) x = c} =
      Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
        (fun _ _ hxy ↦ hxy.minimalPeriod_eq) c := by
    induction c using Quotient.ind with | _ x =>
    exact Perm.natCard_fiber_quotientMk_sameCycle τ x
  calc
    ∑ᶠ q ∈ {q | h.cycleQuotientMap q = c},
        Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q
      = Nat.card {y : α // Quotient.mk (SameCycle.setoid τ) (f y) = c} :=
        h.sum_minimalPeriod_cycleQuotientMap_fiber_eq_natCard c
    _ = ∑ x : {x : β // Quotient.mk (SameCycle.setoid τ) x = c},
          Nat.card {y : α // f y = x.val} := by
        rw [Nat.card_congr eSigma, Nat.card_eq_fintype_card, Fintype.card_sigma]
        simp_rw [Nat.card_eq_fintype_card]
    _ = Nat.card {x : β // Quotient.mk (SameCycle.setoid τ) x = c} * k := by
        simp_rw [hk, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Nat.card_eq_fintype_card]
    _ = k * Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
          (fun _ _ hxy ↦ hxy.minimalPeriod_eq) c := by
        rw [mul_comm, hcyc]

/-- If every fibre of `f` has `k` elements, then the ratios of cycle lengths of `σ` over a cycle
`c` of `τ` to the cycle length of `c` sum to `k`. -/
theorem sum_minimalPeriod_div_cycleQuotientMap_fiber_eq [Finite α] [Finite β]
    (h : Semiconj f σ τ) {k : ℕ} (hk : ∀ b : β, Nat.card {a : α // f a = b} = k)
    (c : Quotient (SameCycle.setoid τ)) :
    ∑ᶠ q ∈ {q | h.cycleQuotientMap q = c},
        (Quotient.lift (s := SameCycle.setoid σ) (Function.minimalPeriod σ)
            (fun _ _ hxy ↦ hxy.minimalPeriod_eq) q /
          Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
            (fun _ _ hxy ↦ hxy.minimalPeriod_eq) c) = k := by
  classical
  have := Fintype.ofFinite β
  have hpos :
      0 < Quotient.lift (s := SameCycle.setoid τ) (Function.minimalPeriod τ)
        (fun _ _ hxy ↦ hxy.minimalPeriod_eq) c := by
    induction c using Quotient.ind with | _ x =>
    exact minimalPeriod_pos_of_mem_periodicPts ⟨orderOf τ, orderOf_pos _, by
      simp [IsPeriodicPt, IsFixedPt, ← coe_pow]⟩
  have hSfin : ({q | h.cycleQuotientMap q = c} : Set _).Finite := Set.toFinite _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h.sum_minimalPeriod_cycleQuotientMap_fiber_eq_mul hk c,
    finsum_mem_eq_finite_toFinset_sum _ hSfin,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q hq ↦
    Nat.div_mul_cancel ((hSfin.mem_toFinset.mp hq) ▸ h.minimalPeriod_cycleQuotientMap_dvd q)

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
      Quotient.mk (SameCycle.setoid σ) p.2.val := by
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
