/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
import TauCeti.Algebra.Order.Ring.SchurInequality
import TauCeti.Analysis.Convex.Quasiconvex

/-!
# Schur's inequality with quasiconvex weights

Let `f` be quasiconvex on a set `s` of a linearly ordered field. For `x`, `y`, `z ∈ s` with
`0 ≤ f x`, `0 ≤ f y`, `0 ≤ f z`,

`0 ≤ f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y)`,

and if the three values of `f` are positive, equality holds exactly when `x = y = z`. Monotone,
antitone and convex functions are quasiconvex, so this contains the forms of Schur's inequality
with monotone, antitone or convex weights. The Schur sum is symmetric in `x`, `y`, `z`, and
after sorting the points quasiconvexity bounds the middle weight by the larger outer one, which
is the ordered form `TauCeti.schur_inequality_of_le`; the bound on the middle weight is
`QuasiconvexOn.le_max_of_mem_segment`.

The weights `t ↦ t ^ n` on `[0, ∞)` give the polynomial forms for natural exponents and
nonnegative points; for `n = 1` this is the cubic `x (x - y) (x - z) + ⋯ ≥ 0`. For `n ≠ 0` the
polynomial form vanishes exactly when `x = y = z` or two of the points are equal and the third
is `0`.

## Main results

* `QuasiconvexOn.schur_inequality`: Schur's inequality with nonnegative quasiconvex weights.
* `QuasiconvexOn.schur_inequality_eq_zero_iff`: for positive weights, equality holds exactly when
  `x = y = z`.
* `TauCeti.schur_inequality_pow`: `0 ≤ x ^ n (x - y) (x - z) + ⋯` for `x, y, z ≥ 0`.
* `TauCeti.schur_inequality_pow_eq_zero_iff`: its equality case for `n ≠ 0`.
-/

public section

open Set

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}
  {x y z : 𝕜}

/-- Schur's inequality with quasiconvex weights for sorted points `z ≤ y ≤ x`, with its equality
case for positive outer weights. -/
private theorem QuasiconvexOn.schur_of_le (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s)
    (hzy : z ≤ y) (hyx : y ≤ x) (hfx : 0 ≤ f x) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) ∧
      (0 < f x → 0 < f z →
        f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 →
          x = z) := by
  have hb : f y ≤ f x ∨ f y ≤ f z := by
    have := hf.le_max_of_mem_segment hz hx (Icc_subset_segment ⟨hzy, hyx⟩)
    rcases le_total (f z) (f x) with h | h
    · exact .inl (this.trans_eq (max_eq_right h))
    · exact .inr (this.trans_eq (max_eq_left h))
  exact ⟨TauCeti.schur_inequality_of_le hzy hyx hfx hfz hb, fun hfx hfz ↦
    (TauCeti.schur_inequality_eq_zero_iff_of_le hzy hyx hfx hfz hb).1⟩

/-- Schur's inequality with quasiconvex weights and its equality case, for points in any order:
the Schur sum is symmetric in the three points, so this is `QuasiconvexOn.schur_of_le` after
sorting them. -/
private theorem QuasiconvexOn.schur_aux (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ s) (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) ∧
      (0 < f x → 0 < f y → 0 < f z →
        f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 →
          x = y ∧ y = z) := by
  rcases le_total z y with hzy | hyz <;> rcases le_total y x with hyx | hxy <;>
    rcases le_total z x with hzx | hxz
  -- In each order, apply the sorted form to the sorted points; the sums agree up to `ring`.
  all_goals first
    | have h := hf.schur_of_le hx hz hzy hyx hfx hfz
    | have h := hf.schur_of_le hy hz hzx hxy hfy hfz
    | have h := hf.schur_of_le hx hy hyz hzx hfx hfy
    | have h := hf.schur_of_le hz hy hyx hxz hfz hfy
    | have h := hf.schur_of_le hy hx hxz hzy hfy hfx
    | have h := hf.schur_of_le hz hx hxy hyz hfz hfx
  all_goals exact ⟨by linarith [h.1], fun _ _ _ h₀ ↦
    have := h.2 (by assumption) (by assumption) (by linarith); ⟨by linarith, by linarith⟩⟩

/-- **Schur's inequality** with quasiconvex weights: if `f` is quasiconvex on `s` and nonnegative
at `x`, `y`, `z ∈ s`, then `0 ≤ f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y)`.
-/
theorem QuasiconvexOn.schur_inequality (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ s) (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) :=
  (hf.schur_aux hx hy hz hfx hfy hfz).1

/-- The equality case of Schur's inequality with quasiconvex weights: if `f` is quasiconvex on
`s` and positive at `x`, `y`, `z ∈ s`, then
`f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y) = 0` exactly when `x = y = z`. -/
theorem QuasiconvexOn.schur_inequality_eq_zero_iff (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s)
    (hy : y ∈ s) (hz : z ∈ s) (hfx : 0 < f x) (hfy : 0 < f y) (hfz : 0 < f z) :
    f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z := by
  refine ⟨(hf.schur_aux hx hy hz hfx.le hfy.le hfz.le).2 hfx hfy hfz, ?_⟩
  rintro ⟨rfl, rfl⟩
  ring

namespace TauCeti

/-- **Schur's inequality** for natural exponents: for `x, y, z ≥ 0`,
`0 ≤ x ^ n (x - y) (x - z) + y ^ n (y - z) (y - x) + z ^ n (z - x) (z - y)`. For `n = 1` this is
the cubic `0 ≤ x (x - y) (x - z) + y (y - z) (y - x) + z (z - x) (z - y)`. -/
theorem schur_inequality_pow (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ x ^ n * (x - y) * (x - z) + y ^ n * (y - z) * (y - x) + z ^ n * (z - x) * (z - y) :=
  -- `Ici 0` is `{x | 0 ≤ x}` by definition.
  (pow_left_monotoneOn.quasiconvexOn (convex_Ici 0)).schur_inequality hx hy hz (pow_nonneg hx n)
    (pow_nonneg hy n) (pow_nonneg hz n)

/-- The equality case of Schur's inequality for a natural exponent `n ≠ 0` and `x, y, z ≥ 0`:
`x ^ n (x - y) (x - z) + y ^ n (y - z) (y - x) + z ^ n (z - x) (z - y) = 0` exactly when
`x = y = z`, or two of the points are equal and the third is `0`. -/
theorem schur_inequality_pow_eq_zero_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) {n : ℕ}
    (hn : n ≠ 0) :
    x ^ n * (x - y) * (x - z) + y ^ n * (y - z) * (y - x) + z ^ n * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z ∨ x = y ∧ z = 0 ∨ y = z ∧ x = 0 ∨ z = x ∧ y = 0 := by
  -- With one point at `0`, the sum is `(a - b) (a ^ (n + 1) - b ^ (n + 1))` for the other two.
  have key {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a - b) * (a ^ (n + 1) - b ^ (n + 1)) = 0) :
      a = b := by
    rcases mul_eq_zero.1 h with h | h
    · exact sub_eq_zero.1 h
    · exact (pow_left_inj₀ ha hb n.succ_ne_zero).1 (sub_eq_zero.1 h)
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases hx.eq_or_lt with rfl | hx'
    · refine .inr (.inr (.inl ⟨key hy hz ?_, rfl⟩))
      rw [← h, zero_pow hn]
      ring
    rcases hy.eq_or_lt with rfl | hy'
    · refine .inr (.inr (.inr ⟨key hz hx ?_, rfl⟩))
      rw [← h, zero_pow hn]
      ring
    rcases hz.eq_or_lt with rfl | hz'
    · refine .inr (.inl ⟨key hx hy ?_, rfl⟩)
      rw [← h, zero_pow hn]
      ring
    -- `Ici 0` is `{x | 0 ≤ x}` by definition.
    exact .inl (((pow_left_monotoneOn.quasiconvexOn (convex_Ici 0)).schur_inequality_eq_zero_iff
      hx hy hz (pow_pos hx' n) (pow_pos hy' n) (pow_pos hz' n)).1 h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [zero_pow hn]

end TauCeti

end
