/-
Copyright (c) 2026 The Tau Ceti contributors, Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signs of affine functions on an interval

An affine function `g` on a linearly ordered field, positive at `a`, stays positive on `[a, b]`
until its first zero, and vanishes there only
(`AffineMap.exists_forall_pos_iff_lt_of_pos`).

Finitely many affine functions of a nonnegative parameter, all initially positive and at least
one decreasing, have a common positive exit parameter. All functions are nonnegative exactly
up to that parameter and strictly positive exactly before it. The proof uses
`Finset.exists_min_image` on the times at which decreasing functions vanish.

## Main results

* `AffineMap.exists_forall_pos_iff_lt_of_pos`: the threshold `z > a` such that, on `[a, b]`, an
  affine function positive at `a` is positive exactly before `z` and vanishes exactly at `z`.
* `Finset.exists_pos_forall_nonneg_add_mul_iff`: the positive exit parameter for a finite
  family of initially positive affine functions, at least one of which decreases.

The finite-family theorem is adapted from `Mei/Algebra/Order/Field/Finite.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

open Set

namespace AffineMap

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- **The first zero of an affine function.** If an affine function `g` on the line is positive
at `a < b`, there is a threshold `z > a`, lying in `(a, b]` exactly when `g b ≤ 0`, such that on
`[a, b]` the function is positive exactly before `z` and vanishes exactly at `z`. -/
theorem exists_forall_pos_iff_lt_of_pos (g : k →ᵃ[k] k) {a b : k} (hab : a < b) (hg : 0 < g a) :
    ∃ z, a < z ∧ (z ≤ b ↔ g b ≤ 0) ∧ ∀ s ∈ Icc a b, (0 < g s ↔ s < z) ∧ (g s = 0 ↔ s = z) := by
  -- `g` has constant slope `m`.
  obtain ⟨m, hgs⟩ : ∃ m, ∀ s, g s = g a + (s - a) * m :=
    ⟨g 1 - g 0, fun s ↦ by rw [g.apply_eq_add_mul_sub s, g.apply_eq_add_mul_sub a]; ring⟩
  rcases lt_or_ge m 0 with hm | hm
  · -- `g s = m * (s - z)` with `z = a - g a / m`.
    have hlin (s : k) : g s = m * (s - (a - g a / m)) := by
      have hm0 : m ≠ 0 := hm.ne
      rw [hgs s]
      field_simp
      ring
    refine ⟨a - g a / m, by linarith [div_neg_of_pos_of_neg hg hm], ?_, fun s _ ↦ ?_⟩
    · rw [hlin b]
      exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
    · rw [hlin s, mul_eq_zero, sub_eq_zero, or_iff_right hm.ne]
      exact ⟨⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩, Iff.rfl⟩
  · -- `g` does not decrease, so it stays positive.
    have hpos {s : k} (hs : a ≤ s) : 0 < g s := by
      rw [hgs]
      exact add_pos_of_pos_of_nonneg hg (mul_nonneg (sub_nonneg.2 hs) hm)
    refine ⟨b + 1, by linarith, ⟨fun h ↦ by linarith, fun h ↦ ?_⟩, fun s hs ↦ ?_⟩
    · exact absurd h (not_le.2 (hpos hab.le))
    · exact ⟨⟨fun _ ↦ by linarith [hs.2], fun _ ↦ hpos hs.1⟩,
        ⟨fun h ↦ ((hpos hs.1).ne' h).elim, fun h ↦ by linarith [hs.2]⟩⟩

end AffineMap

namespace Finset

variable {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A finite family of initially positive affine functions, with at least one
negative slope, is nonnegative up to a positive exit time and strictly positive
before that time. -/
theorem exists_pos_forall_nonneg_add_mul_iff (S : Finset ι) (b a : ι → 𝕜)
    (hb : ∀ i ∈ S, 0 < b i) (hneg : ∃ i ∈ S, a i < 0) :
    ∃ T : 𝕜, 0 < T ∧ ∀ t : 𝕜, 0 ≤ t →
      ((∀ i ∈ S, 0 ≤ b i + t * a i) ↔ t ≤ T) ∧
      ((∀ i ∈ S, 0 < b i + t * a i) ↔ t < T) := by
  classical
  let J := S.filter fun j => a j < 0
  have hJ : J.Nonempty := by
    obtain ⟨j, hj, hja⟩ := hneg
    exact ⟨j, mem_filter.mpr ⟨hj, hja⟩⟩
  obtain ⟨j, hj, hmin⟩ := J.exists_min_image (fun j => -b j / a j) hJ
  have hjS := (mem_filter.mp hj).1
  have haj : a j < 0 := (mem_filter.mp hj).2
  let T := -b j / a j
  have hT : 0 < T := div_pos_of_neg_of_neg (neg_neg_of_pos (hb j hjS)) haj
  have hzero : b j + T * a j = 0 := by
    dsimp only [T]
    field_simp [haj.ne]
    ring
  have hnonneg (t : 𝕜) (ht : 0 ≤ t) :
      (∀ i ∈ S, 0 ≤ b i + t * a i) ↔ t ≤ T := by
    constructor
    · intro htall
      have hi := htall j hjS
      nlinarith
    · intro htT i hiS
      by_cases hai : a i < 0
      · have hle : T ≤ -b i / a i := hmin i (mem_filter.mpr ⟨hiS, hai⟩)
        have hmul := (le_div_iff_of_neg hai).mp (htT.trans hle)
        linarith
      · exact add_nonneg (hb i hiS).le (mul_nonneg ht (le_of_not_gt hai))
  have hpos (t : 𝕜) (ht : 0 ≤ t) :
      (∀ i ∈ S, 0 < b i + t * a i) ↔ t < T := by
    constructor
    · intro htall
      have hi := htall j hjS
      nlinarith
    · intro htT i hiS
      by_cases hai : a i < 0
      · have hle : T ≤ -b i / a i := hmin i (mem_filter.mpr ⟨hiS, hai⟩)
        have hmul := (lt_div_iff_of_neg hai).mp (htT.trans_le hle)
        linarith
      · exact add_pos_of_pos_of_nonneg (hb i hiS) (mul_nonneg ht (le_of_not_gt hai))
  exact ⟨T, hT, fun t ht => ⟨hnonneg t ht, hpos t ht⟩⟩

end Finset
