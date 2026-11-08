/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# First exit from finitely many affine inequalities

Finitely many affine functions of a nonnegative parameter, all initially
positive and at least one decreasing, have a common positive exit parameter.
All functions are nonnegative exactly up to that parameter and strictly
positive exactly before it. This describes rays in a simplex through their
barycentric coordinates. The proof uses `Finset.exists_min_image` on the times
at which decreasing functions vanish.

Adapted from `Mei/Algebra/Order/Field/Finite.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

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
