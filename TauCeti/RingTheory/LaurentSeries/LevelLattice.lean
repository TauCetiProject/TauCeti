/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.LevelBasis

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
theorem level_inf (n m : ℕ+) : level K n ⊓ level K m = level K (n.gcd m) := by
  ext x
  -- The available intersection theorem concerns the Hahn-series ranges, so expose membership
  -- in the three actual intermediate fields before applying their range characterizations.
  change (x ∈ level K n ∧ x ∈ level K m) ↔ x ∈ level K (n.gcd m)
  simp only [mem_level_iff, mem_range_levelEmbedding_iff]
  rw [← Algebra.mem_inf, LaurentSeries.range_ramifiedEmbedding_inf]

/-- Raising the parameter of level `n * d` to the `d`-th power gives the parameter of level
`n`. -/
@[simp]
theorem levelEmbedding_single_one_pow (n d : ℕ+) :
    levelEmbedding K (n * d) (single 1 1) ^ (d : ℕ) = levelEmbedding K n (single 1 1) := by
  rw [← map_pow (levelEmbedding K (n * d)) (single (1 : ℤ) (1 : K))]
  convert levelEmbedding_expand n d (single (1 : ℤ) (1 : K)) using 1
  simp only [HahnSeries.single_pow, LaurentSeries.expand_single, nsmul_eq_mul, mul_one, one_pow]

private theorem level_le_of_single_one_mem (d : ℕ+)
    (E : IntermediateField K⸨X⸩ (TauCeti.puiseuxField K))
    (hgen : levelEmbedding K d (single 1 1) ∈ E) : level K d ≤ E := by
  intro x hx
  let y : level K d := ⟨x, hx⟩
  obtain ⟨p, hp⟩ := (levelPowerBasis K d).exists_eq_aeval' y
  have hgen' : ((level K d).val (levelPowerBasis K d).gen) ∈ E := by
    rw [levelPowerBasis_gen]
    -- `coe_levelEquiv_apply` is stated for the subtype coercion, whereas this goal displays the
    -- propositionally equal `IntermediateField.val` map.
    change ((levelEquiv K d (LaurentSeries.Level.parameter K d) : level K d) :
      TauCeti.puiseuxField K) ∈ E
    rw [coe_levelEquiv_apply, LaurentSeries.Level.toPuiseux_apply,
      LaurentSeries.Level.ringEquiv_parameter]
    exact hgen
  have hp_mem : Polynomial.aeval ((level K d).val (levelPowerBasis K d).gen) p ∈ E := by
    apply (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgen'))
    exact Polynomial.aeval_mem_adjoin_singleton K⸨X⸩ _
  have hp' : x = Polynomial.aeval ((level K d).val (levelPowerBasis K d).gen) p := by
    have hpmap := congrArg (level K d).val hp
    -- Expose the value of the inclusion on `y = ⟨x, hx⟩` before commuting it with evaluation.
    change x = (level K d).val (Polynomial.aeval (levelPowerBasis K d).gen p) at hpmap
    simpa only [Polynomial.aeval_algHom_apply] using hpmap
  rwa [hp']

/-- The compositum of levels `n` and `m` is level `lcm n m`. -/
theorem level_sup (n m : ℕ+) : level K n ⊔ level K m = level K (n.lcm m) := by
  apply le_antisymm
  · exact sup_le (level_le_of_dvd (PNat.dvd_lcm_left n m))
      (level_le_of_dvd (PNat.dvd_lcm_right n m))
  · apply level_le_of_single_one_mem
    let g := Nat.gcd (n : ℕ) (m : ℕ)
    let a : ℕ+ := ⟨(n : ℕ) / g, Nat.div_pos (Nat.gcd_le_left (m : ℕ) n.pos) (by
      exact Nat.gcd_pos_of_pos_left _ n.pos)⟩
    let b : ℕ+ := ⟨(m : ℕ) / g, Nat.div_pos (Nat.gcd_le_right (n : ℕ) m.pos) (by
      exact Nat.gcd_pos_of_pos_left _ n.pos)⟩
    have hab : Nat.Coprime (a : ℕ) (b : ℕ) := by
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (m : ℕ) n.pos)
    have hma : m * a = n.lcm m := by
      apply Subtype.ext
      -- After extensionality, state the quotient calculation in `ℕ`, where the gcd/lcm API lives.
      change (m : ℕ) * ((n : ℕ) / Nat.gcd n m) = Nat.lcm n m
      rw [Nat.lcm_comm, Nat.lcm_eq_mul_div,
        Nat.mul_div_assoc (m : ℕ) (Nat.gcd_dvd_right (m : ℕ) (n : ℕ)), Nat.gcd_comm]
    have hnb : n * b = n.lcm m := by
      apply Subtype.ext
      -- As above, remove the positive-natural wrappers before using `Nat.lcm_eq_mul_div`.
      change (n : ℕ) * ((m : ℕ) / Nat.gcd n m) = Nat.lcm n m
      rw [Nat.lcm_eq_mul_div,
        Nat.mul_div_assoc (n : ℕ) (Nat.gcd_dvd_right (n : ℕ) (m : ℕ))]
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
    have hum : levelEmbedding K m (single 1 1) ∈ level K n ⊔ level K m := by
      apply le_sup_right (a := level K n)
      rw [mem_level_iff]
      exact ⟨single 1 1, rfl⟩
    have hun : levelEmbedding K n (single 1 1) ∈ level K n ⊔ level K m := by
      apply le_sup_left (b := level K m)
      rw [mem_level_iff]
      exact ⟨single 1 1, rfl⟩
    have hbezout : (1 : ℤ) =
        (a : ℕ) * Nat.gcdA a b + (b : ℕ) * Nat.gcdB a b := by
      simpa only [hab.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab (a : ℕ) (b : ℕ)
    have hu_eq : u = levelEmbedding K m (single 1 1) ^ Nat.gcdA a b *
        levelEmbedding K n (single 1 1) ^ Nat.gcdB a b := calc
      u = u ^ (1 : ℤ) := by simp
      _ = u ^ ((a : ℕ) * Nat.gcdA a b + (b : ℕ) * Nat.gcdB a b) := by rw [← hbezout]
      _ = u ^ ((a : ℕ) * Nat.gcdA a b) * u ^ ((b : ℕ) * Nat.gcdB a b) :=
        zpow_add₀ hu _ _
      _ = (u ^ (a : ℕ)) ^ Nat.gcdA a b * (u ^ (b : ℕ)) ^ Nat.gcdB a b := by
        simp only [← zpow_natCast, zpow_mul]
      _ = levelEmbedding K m (single 1 1) ^ Nat.gcdA a b *
          levelEmbedding K n (single 1 1) ^ Nat.gcdB a b := by rw [huma, hunb]
    have hu_mem : u ∈ level K n ⊔ level K m := by
      rw [hu_eq]
      exact mul_mem ((level K n ⊔ level K m).pow_mem hum _)
        ((level K n ⊔ level K m).pow_mem hun _)
    exact hu_mem

end TauCeti.puiseuxField
