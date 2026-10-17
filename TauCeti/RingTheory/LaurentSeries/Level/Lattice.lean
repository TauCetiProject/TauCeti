/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Basis

/-!
# Lattice operations on ramified Laurent-series levels

The ramified levels inside the Puiseux field reproduce the divisibility lattice of positive
integers. Level containment is divisibility, intersections are indexed by greatest common
divisors, and composita are indexed by least common multiples.

The compositum calculation uses the power basis of a level. If `l = lcm n m`, the quotients
`l / n` and `l / m` are coprime, so Bézout expresses the level-`l` parameter as a product of
integer powers of the level-`n` and level-`m` parameters. The level-`l` power basis then shows
that these two smaller levels generate all of level `l`.

## Main results

* `TauCeti.puiseuxField.level_le_iff`: level containment is divisibility.
* `TauCeti.puiseuxField.level_inf`: the intersection of levels `n` and `m` is level `gcd n m`.
* `TauCeti.puiseuxField.level_sup`: the compositum of levels `n` and `m` is level `lcm n m`.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K]

/-- If `n` divides `m`, then level `n` is contained in level `m`. -/
theorem level_le_of_dvd {n m : ℕ+} (h : n ∣ m) : level K n ≤ level K m := by
  intro x hx
  rw [mem_level_iff] at hx ⊢
  exact range_levelEmbedding_le_of_dvd h hx

/-- Level containment is exactly divisibility of ramification indices. -/
@[simp]
theorem level_le_iff {n m : ℕ+} : level K n ≤ level K m ↔ n ∣ m := by
  refine ⟨fun h ↦ ?_, level_le_of_dvd⟩
  rw [← LaurentSeries.range_ramifiedEmbedding_le_iff (R := K)]
  intro x hx
  let y : TauCeti.puiseuxField K := ⟨x, mem_puiseuxField_iff.mpr ⟨n, hx⟩⟩
  have hyn : y ∈ level K n := by
    rw [mem_level_iff, mem_range_levelEmbedding_iff]
    exact hx
  have hym := h hyn
  rw [mem_level_iff, mem_range_levelEmbedding_iff] at hym
  exact hym

/-- The intersection of levels `n` and `m` is level `gcd n m`. -/
@[simp]
theorem level_inf (n m : ℕ+) : level K n ⊓ level K m = level K (n.gcd m) := by
  ext x
  rw [IntermediateField.mem_inf]
  simp only [mem_level_iff, mem_range_levelEmbedding_iff]
  rw [← Algebra.mem_inf, LaurentSeries.range_ramifiedEmbedding_inf]

private def gcdQuotient (n m : ℕ+) : ℕ+ :=
  ⟨(n : ℕ) / Nat.gcd n m, Nat.div_pos (Nat.gcd_le_left (m : ℕ) n.pos)
    (Nat.gcd_pos_of_pos_left (m : ℕ) n.pos)⟩

private theorem mul_gcdQuotient_eq_lcm (n m : ℕ+) :
    m * gcdQuotient n m = n.lcm m := by
  apply PNat.eq
  rw [PNat.mul_coe, PNat.lcm_coe]
  simp only [gcdQuotient, PNat.mk_coe]
  rw [Nat.lcm_comm, Nat.lcm_eq_mul_div,
    Nat.mul_div_assoc (m : ℕ) (Nat.gcd_dvd_right (m : ℕ) (n : ℕ)), Nat.gcd_comm]

/-- The parameter of level `lcm n m` belongs to the compositum of levels `n` and `m`. -/
theorem levelEmbedding_lcm_single_one_mem_sup (n m : ℕ+) :
    levelEmbedding K (n.lcm m) (single 1 1) ∈ level K n ⊔ level K m := by
  let a := gcdQuotient n m
  let b := gcdQuotient m n
  have hab : Nat.Coprime (a : ℕ) (b : ℕ) :=
    by simpa only [a, b, gcdQuotient, PNat.mk_coe, Nat.gcd_comm] using
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (m : ℕ) n.pos)
  have hma : m * a = n.lcm m := mul_gcdQuotient_eq_lcm n m
  have hnb : n * b = n.lcm m := by
    apply PNat.eq
    simpa only [b, PNat.mul_coe, PNat.lcm_coe, Nat.lcm_comm] using
      congrArg PNat.val (mul_gcdQuotient_eq_lcm m n)
  let u := levelEmbedding K (n.lcm m) (single 1 1)
  have hu : u ≠ 0 := (map_ne_zero (levelEmbedding K (n.lcm m))).mpr (by simp)
  have huma : u ^ (a : ℕ) = levelEmbedding K m (single 1 1) := by
    dsimp only [u]
    rw [← hma]
    exact levelEmbedding_single_one_pow m a
  have hunb : u ^ (b : ℕ) = levelEmbedding K n (single 1 1) := by
    dsimp only [u]
    rw [← hnb]
    exact levelEmbedding_single_one_pow n b
  have hum : levelEmbedding K m (single 1 1) ∈ level K n ⊔ level K m :=
    le_sup_right (a := level K n) (levelEmbedding_mem_level K m (single 1 1))
  have hun : levelEmbedding K n (single 1 1) ∈ level K n ⊔ level K m :=
    le_sup_left (b := level K m) (levelEmbedding_mem_level K n (single 1 1))
  have hbezout : (1 : ℤ) =
      (a : ℕ) * Nat.gcdA a b + (b : ℕ) * Nat.gcdB a b := by
    simpa only [hab.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab (a : ℕ) (b : ℕ)
  have hu_eq : u = levelEmbedding K m (single 1 1) ^ Nat.gcdA a b *
      levelEmbedding K n (single 1 1) ^ Nat.gcdB a b := calc
    u = u ^ (1 : ℤ) := by simp
    _ = u ^ ((a : ℕ) * Nat.gcdA a b + (b : ℕ) * Nat.gcdB a b) := by rw [← hbezout]
    _ = u ^ ((a : ℕ) * Nat.gcdA a b) * u ^ ((b : ℕ) * Nat.gcdB a b) := zpow_add₀ hu _ _
    _ = (u ^ (a : ℕ)) ^ Nat.gcdA a b * (u ^ (b : ℕ)) ^ Nat.gcdB a b := by
      simp only [← zpow_natCast, zpow_mul]
    _ = levelEmbedding K m (single 1 1) ^ Nat.gcdA a b *
        levelEmbedding K n (single 1 1) ^ Nat.gcdB a b := by rw [huma, hunb]
  rw [show levelEmbedding K (n.lcm m) (single 1 1) = u from rfl, hu_eq]
  exact mul_mem ((level K n ⊔ level K m).pow_mem hum _)
    ((level K n ⊔ level K m).pow_mem hun _)

/-- The compositum of levels `n` and `m` is level `lcm n m`. -/
@[simp]
theorem level_sup (n m : ℕ+) : level K n ⊔ level K m = level K (n.lcm m) := by
  apply le_antisymm
  · exact sup_le (level_le_of_dvd (PNat.dvd_lcm_left n m))
      (level_le_of_dvd (PNat.dvd_lcm_right n m))
  · exact (level_le_iff_levelEmbedding_single_one_mem K (n.lcm m)
      (level K n ⊔ level K m)).mpr (levelEmbedding_lcm_single_one_mem_sup n m)

end TauCeti.puiseuxField
