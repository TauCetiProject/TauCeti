/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# Basic facts about rank-one discrete valuations

This file records general properties of rank-one discrete valuations
(`Valuation.IsRankOneDiscrete`): their value groups are multiplicatively Archimedean, and nonzero
elements admitting arbitrary `ℓ ^ k`-th roots (`ℓ > 1`) have valuation `1`.

## Main results

* `Valuation.mulArchimedean_valueGroup₀_of_isRankOneDiscrete`: the value group with zero of a
  rank-one discrete valuation is multiplicatively Archimedean.
* `Valuation.val_eq_one_of_forall_exists_pow_eq`: in a rank-one discrete valuation, an element with
  nonzero valuation that admits `ℓ ^ k`-th roots for all `k` (`ℓ > 1`) has valuation `1`.
-/

public section

namespace Valuation

variable {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]

/-- The value group with zero of a rank-one discrete valuation is multiplicatively Archimedean. -/
instance mulArchimedean_valueGroup₀_of_isRankOneDiscrete (v : Valuation R Γ) [v.IsRankOneDiscrete] :
    MulArchimedean v.ValueGroup₀ :=
  nonempty_rankOne_iff_mulArchimedean.mp
    ⟨IsRankOneDiscrete.rankOne v (by norm_num : (1 : NNReal) < 2)⟩

/-- In a rank-one discrete valuation, an element with nonzero valuation that admits `ℓ ^ k`-th
roots for all `k` (for some `ℓ > 1`) has valuation `1`. -/
theorem val_eq_one_of_forall_exists_pow_eq (v : Valuation R Γ) [v.IsRankOneDiscrete]
    {ℓ : ℕ} (hℓ : 1 < ℓ) {x : R} (hx : v x ≠ 0) (h : ∀ k : ℕ, ∃ z : R, z ^ ℓ ^ k = x) :
    v x = 1 := by
  set γ := IsRankOneDiscrete.generator v
  have hγ : γ < 1 := IsRankOneDiscrete.generator_lt_one v
  have mem_zpowers {a : R} (ha : v a ≠ 0) : ∃ n : ℤ, γ ^ n = Units.mk0 (v a) ha :=
    Subgroup.mem_zpowers_iff.mp <|
      (IsRankOneDiscrete.generator_zpowers_eq_valueGroup v).symm ▸
        MonoidWithZeroHom.mem_valueGroup _ ⟨a, rfl⟩
  obtain ⟨m, hm⟩ := mem_zpowers hx
  suffices hm0 : m = 0 by
    rw [hm0, zpow_zero] at hm
    exact congrArg Units.val hm.symm
  by_contra hm0
  obtain ⟨z, hz⟩ := h m.natAbs
  have hz0 : v z ≠ 0 := fun h0 ↦
    hx (by rw [← hz, map_pow, h0, zero_pow (pow_ne_zero _ (by omega))])
  obtain ⟨n, hn⟩ := mem_zpowers hz0
  have hpow : γ ^ (n * (ℓ ^ m.natAbs : ℕ)) = γ ^ m := by
    rw [zpow_mul, zpow_natCast, hn, hm]
    ext
    simp [← map_pow, hz]
  have heq : n * (ℓ ^ m.natAbs : ℕ) = m := (zpow_right_strictAnti hγ).injective hpow
  have hdvd : ℓ ^ m.natAbs ∣ m.natAbs :=
    ⟨n.natAbs, by
      conv_lhs => rw [← heq]
      rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm]⟩
  exact (Nat.lt_pow_self hℓ).not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hdvd)

end Valuation
