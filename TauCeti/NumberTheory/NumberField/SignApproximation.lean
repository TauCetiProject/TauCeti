/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Prescribing the signs of a number field element at the real places

Weak approximation says that a number field `K` is dense in the product of its completions at the
infinite places; Mathlib records the diagonal form of this,
`NumberField.InfinitePlace.denseRange_algebraMap_pi`, on the product of the copies of `K` carrying
the topology of each infinite place. This file turns that topological statement into the
arithmetic one it is used for: an element of `K` may be prescribed, independently at each real
place, to be positive or negative there.

The passage is the usual one. Approximating the tuple whose entry at a place is `1` or `-1` to
within `1` forces the sign of each real embedding of the approximating element, because a real
number within distance `1` of `±1` has the sign of `±1`; the same estimate at any one place, real
or complex, keeps the element away from `0`.

## Main results

* `NumberField.exists_forall_infinitePlace_sub_lt`: weak approximation at the infinite
  places in `ε`-`δ` form, with targets in `K` measured by the places themselves.
* `NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq`: the family of targets that
  such an approximation is aimed at, of absolute value one at every infinite place and of
  prescribed sign at every real place.
* `NumberField.InfinitePlace.IsReal.mul_pos_of_apply_sub_lt`: an element closer to a target than
  the target is to `0`, as measured by a real place, has the sign of that target there.
* `NumberField.ne_zero_of_infinitePlace_sub_lt`: an element closer to a target than the target is
  to `0`, as measured by any infinite place, is nonzero.
* `NumberField.exists_ne_zero_forall_isReal_pos`: a nonzero element of `K` whose real
  embeddings have prescribed signs.
* `NumberField.exists_ne_zero_neg_iff_mem`: the same statement with the prescription given
  as the set of real places at which the element is to be negative.

## References

The weak approximation theorem for pairwise inequivalent absolute values is Artin--Whaples; see
E. Artin and G. Whaples, *Axiomatic characterization of fields by the product formula for
valuations*, Bull. Amer. Math. Soc. **51** (1945), and, for the number field statement,
J. W. S. Cassels and A. Fröhlich, *Algebraic Number Theory*, Chapter II.
-/

public section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K]

section

variable [NumberField K]

/-- **Weak approximation at the infinite places.** Given one target `a v : K` and one positive
tolerance `r v` for each infinite place `v` of a number field, some single `x : K` is within `r v`
of every target, as measured by the place at which that target was prescribed.

This is `NumberField.InfinitePlace.denseRange_algebraMap_pi` with the topology of the finite
product unwound into the individual places. -/
theorem exists_forall_infinitePlace_sub_lt (a : InfinitePlace K → K)
    (r : InfinitePlace K → ℝ) (hr : ∀ v, 0 < r v) :
    ∃ x : K, ∀ v : InfinitePlace K, v (x - a v) < r v := by
  let δ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun v _ => hr v
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi K)
    (fun v => WithAbs.toAbs v.1 (a v)) δ hδ
  refine ⟨x, fun v => ?_⟩
  have h := (dist_pi_lt_iff hδ).mp hx v
  rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at h
  rw [coe_apply, AbsoluteValue.map_sub]
  exact h.trans_le (Finset.inf'_le r (Finset.mem_univ v))

end

/-- **A family of targets of absolute value one with prescribed signs.**  For any prescribed sign
at each real place of a number field there is a family `b`, one element of `K` for each infinite
place, whose entry at `v` has absolute value one at `v` and whose entry at a real place `w` has
there exactly the prescribed sign.

This is the family that weak approximation at the infinite places is aimed at: an approximation
to within `1` is nonzero by `NumberField.ne_zero_of_infinitePlace_sub_lt`, and
`NumberField.InfinitePlace.IsReal.mul_pos_of_apply_sub_lt` turns it into a sign prescription. -/
theorem exists_forall_apply_eq_one_and_embedding_of_isReal_eq
    (s : {w : InfinitePlace K // w.IsReal} → ℤˣ) :
    ∃ b : InfinitePlace K → K, (∀ v : InfinitePlace K, v (b v) = 1) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        embedding_of_isReal w.2 (b w.1) = ((s w : ℤ) : ℝ) := by
  classical
  refine ⟨fun v => if h : v.IsReal then ((s ⟨v, h⟩ : ℤ) : K) else 1, fun v => ?_,
    fun w => by simp [w.2]⟩
  by_cases h : v.IsReal
  · rcases Int.units_eq_one_or (s ⟨v, h⟩) with hs | hs <;> simp [h, hs, coe_apply]
  · simp [h]

/-- **An approximation of a target has the sign of that target.**  At a real place `w`, an element
`x` closer to `y` than `y` is to `0`, as measured by `w`, has the same sign as `y` under the real
embedding at `w`.

Together with `NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq` this is the whole
archimedean content of a sign prescription: everything else is the approximation itself. -/
theorem InfinitePlace.IsReal.mul_pos_of_apply_sub_lt {w : InfinitePlace K} (hw : w.IsReal)
    {x y : K} (h : w (x - y) < w y) :
    0 < embedding_of_isReal hw y * embedding_of_isReal hw x := by
  simp only [← norm_embedding_of_isReal hw, map_sub, Real.norm_eq_abs] at h
  cases abs_cases (embedding_of_isReal hw x - embedding_of_isReal hw y) <;>
    cases abs_cases (embedding_of_isReal hw y) <;> nlinarith

/-- An element closer to `y` than `y` is to `0`, as measured by an infinite place, is nonzero. -/
theorem ne_zero_of_infinitePlace_sub_lt {w : InfinitePlace K} {x y : K} (h : w (x - y) < w y) :
    x ≠ 0 := by
  rintro rfl
  simp [coe_apply] at h

variable [NumberField K]

/-- **A nonzero element with prescribed signs at the real places.** For any family of nonzero
reals `s`, indexed by the real infinite places of a number field `K`, some nonzero `x : K` has
`s w` and the image of `x` under the real embedding at `w` of the same sign, at every real place
`w` simultaneously. -/
theorem exists_ne_zero_forall_isReal_pos (s : {w : InfinitePlace K // w.IsReal} → ℝ)
    (hs : ∀ w, s w ≠ 0) :
    ∃ x : K, x ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < s w * embedding_of_isReal w.2 x := by
  -- Aim at `1` where the prescribed sign is positive and at `-1` where it is negative.
  obtain ⟨b, habs, hb⟩ := exists_forall_apply_eq_one_and_embedding_of_isReal_eq (K := K)
    fun w => if 0 < s w then 1 else -1
  obtain ⟨x, hx⟩ := exists_forall_infinitePlace_sub_lt b (fun v => v (b v)) fun v => by
    simp [habs]
  refine ⟨x, ne_zero_of_infinitePlace_sub_lt (hx (Classical.arbitrary _)), fun w => ?_⟩
  have h := w.2.mul_pos_of_apply_sub_lt (hx w.1)
  rw [hb w] at h
  rcases (hs w).lt_or_gt with h' | h' <;> simp [h', h'.not_gt] at h <;> nlinarith

/-- **A nonzero element of `K` negative at exactly a prescribed set of real places.** Since the
real places at which an element is negative determine its sign pattern, this is
`NumberField.exists_ne_zero_forall_isReal_pos` with the pattern presented as a set. -/
theorem exists_ne_zero_neg_iff_mem (S : Set {w : InfinitePlace K // w.IsReal}) :
    ∃ x : K, x ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, embedding_of_isReal w.2 x < 0 ↔ w ∈ S := by
  classical
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_forall_isReal_pos (K := K) (fun w => if w ∈ S then -1 else 1)
      fun w => by split_ifs <;> norm_num
  refine ⟨x, hx0, fun w => ?_⟩
  have h := hx w
  by_cases hw : w ∈ S <;> simp [hw] at h ⊢ <;> linarith

end NumberField
