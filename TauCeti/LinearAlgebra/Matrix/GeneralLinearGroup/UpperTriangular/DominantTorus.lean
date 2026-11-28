/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Order.Filter.Finite

/-!
# The dominant diagonal torus submonoid for a valuation

Given a valuation `v : Valuation R Γ₀` and a preordered index type `m`, the dominant diagonal
torus `TauCeti.dominantTorus m v` is the submonoid of `m → Rˣ` consisting of diagonal tuples `t`
whose entry valuations are monotone (`i ≤ j → v (t i) ≤ v (t j)`). When `m` is finite and
`Γ₀ˣ` is multiplicatively Archimedean (for instance `ℤᵐ⁰` or `ℝ≥0` for a non-archimedean local
field), high powers of any strictly dominant diagonal element absorb arbitrary off-diagonal
entries into the valuation ring and shift any diagonal tuple into `dominantTorus m v`, as used
to define the Iwahori–Hecke operators `U_t` for dominant `t`.

* `TauCeti.dominantTorus`: the submonoid `{t : m → Rˣ | Monotone fun i ↦ v (t i : R)}`.
* `TauCeti.mem_dominantTorus_iff`: membership characterization.
* `TauCeti.eventually_valuation_pow_div_mul_le_one_of_lt`: for units `x, y` with
  `v x < v y` over a valued division ring with `[MulArchimedean Γ₀ˣ]`, `(x / y) ^ k * a` has
  valuation `≤ 1` for all sufficiently large `k`.
* `TauCeti.eventually_valuation_pow_div_mul_le_one`: tuple version for a strictly dominant `t`
  on a finite preordered type `m`.
* `TauCeti.eventually_pow_mul_mem_dominantTorus`: for strictly dominant `t` and any `s : m → Kˣ`,
  `t ^ k * s ∈ dominantTorus m v` for all sufficiently large `k`.

## References

* W. Casselman, *Introduction to admissible representations of p-adic groups: `GL_n`*, notes.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` (`New.dominantTorus`,
  `New.eventually_v_mul_pow_le_one`, `New.eventually_pow_mul_mem_dominantTorus`).
-/

public section

open Filter

namespace TauCeti

section Ring

variable (m : Type*) [Preorder m] {R Γ₀ : Type*} [Ring R]
  [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The submonoid of diagonal tuples `t : m → Rˣ` whose valuations are monotone in the index:
`i ≤ j → v (t i : R) ≤ v (t j : R)`. -/
def dominantTorus : Submonoid (m → Rˣ) where
  carrier := {t | Monotone fun i ↦ v (t i : R)}
  one_mem' _ _ _ := le_rfl
  mul_mem' ht ht' _ _ hij := by
    simpa [map_mul] using mul_le_mul' (ht hij) (ht' hij)

@[simp]
theorem mem_dominantTorus_iff {t : m → Rˣ} :
    t ∈ dominantTorus m v ↔ Monotone fun i ↦ v (t i : R) :=
  Iff.rfl

end Ring

section DivisionRing

variable {m K Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

private lemma eventually_le_pow_of_one_lt [MulArchimedean Γ₀ˣ] {u b : Γ₀}
    (hb : b ≠ 0) (hu : 1 < u) : ∀ᶠ k : ℕ in atTop, b ≤ u ^ k := by
  let u' : Γ₀ˣ := Units.mk0 u (zero_lt_one.trans hu).ne'
  let b' : Γ₀ˣ := Units.mk0 b hb
  have hu' : (1 : Γ₀ˣ) < u' := by
    rw [← Units.val_lt_val, Units.val_one, Units.val_mk0]
    exact hu
  obtain ⟨N, hN⟩ := MulArchimedean.arch b' hu'
  filter_upwards [eventually_ge_atTop N] with k hk
  exact_mod_cast hN.trans (pow_le_pow_right' hu'.le hk)

/-- If `x, y : Kˣ` satisfy `v x < v y` over a valued division ring with `[MulArchimedean Γ₀ˣ]`,
then `x ^ k / y ^ k * a` has valuation `≤ 1` for all sufficiently large `k : ℕ`. -/
theorem eventually_valuation_pow_div_mul_le_one_of_lt [MulArchimedean Γ₀ˣ]
    {x y : Kˣ} (h : v (x : K) < v (y : K)) (a : K) :
    ∀ᶠ k : ℕ in atTop, v ((x : K) ^ k / (y : K) ^ k * a) ≤ 1 := by
  by_cases ha : v a = 0
  · filter_upwards with k
    simp [map_mul, ha]
  · have hx : (0 : Γ₀) < v (x : K) := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr x.ne_zero)
    have hy : (0 : Γ₀) < v (y : K) := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr y.ne_zero)
    have hu : (1 : Γ₀) < v (y : K) / v (x : K) := (one_lt_div₀ hx).mpr h
    filter_upwards [eventually_le_pow_of_one_lt ha hu] with k hk
    simp only [map_mul, map_div₀, map_pow]
    rw [div_mul_eq_mul_div, div_le_one₀ (pow_pos hy k)]
    have hpow := (le_div_iff₀ (pow_pos hx k)).mp (by simpa [div_pow] using hk)
    simpa [mul_comm] using hpow

/-- If `t : m → Kˣ` has strictly increasing valuations on a finite preordered type `m` and
`Γ₀ˣ` is multiplicatively Archimedean, then `(t i) ^ k / (t j) ^ k * a i j` has valuation `≤ 1`
for all `i < j` and all sufficiently large `k : ℕ`. -/
theorem eventually_valuation_pow_div_mul_le_one [Preorder m] [Finite m] [MulArchimedean Γ₀ˣ]
    {t : m → Kˣ} (ht : StrictMono fun i ↦ v (t i : K)) (a : m → m → K) :
    ∀ᶠ k : ℕ in atTop, ∀ i j : m, i < j → v ((t i : K) ^ k / (t j : K) ^ k * a i j) ≤ 1 := by
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  by_cases hij : i < j
  · filter_upwards [eventually_valuation_pow_div_mul_le_one_of_lt (ht hij) (a i j)] with k hk _
    exact hk
  · filter_upwards with k h
    exact absurd h hij

/-- If `t : m → Kˣ` has strictly increasing valuations on a finite partially ordered type `m` and
`Γ₀ˣ` is multiplicatively Archimedean, then for every `s : m → Kˣ`, the product `t ^ k * s` lies
in `dominantTorus m v` for all sufficiently large `k : ℕ`. -/
theorem eventually_pow_mul_mem_dominantTorus [PartialOrder m] [Finite m] [MulArchimedean Γ₀ˣ]
    {t : m → Kˣ} (ht : StrictMono fun i ↦ v (t i : K)) (s : m → Kˣ) :
    ∀ᶠ k : ℕ in atTop, t ^ k * s ∈ dominantTorus m v := by
  filter_upwards [eventually_valuation_pow_div_mul_le_one ht fun i j ↦ (s i : K) / (s j : K)]
    with k hk
  rw [mem_dominantTorus_iff, monotone_iff_forall_lt]
  intro i j hij
  have hle := hk i j hij
  have hpos : (0 : Γ₀) < v ((t j : K) ^ k * (s j : K)) := by
    rw [pos_iff_ne_zero, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero k (v.ne_zero_iff.mpr (t j).ne_zero))
      (v.ne_zero_iff.mpr (s j).ne_zero)
  have h_eq : v ((t i : K) ^ k / (t j : K) ^ k * ((s i : K) / (s j : K))) =
      v ((t i : K) ^ k * (s i : K)) / v ((t j : K) ^ k * (s j : K)) := by
    simp only [map_mul, map_div₀, map_pow, div_mul_div_comm]
  rw [h_eq, div_le_one₀ hpos] at hle
  simpa [Pi.mul_apply, Pi.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val] using hle

end DivisionRing

end TauCeti
