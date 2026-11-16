/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/

/- Weight-rounding construction adapted from
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/FiniteSupport.lean`. -/
module

public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Finite weight vectors in `ℝ≥0∞`

A *weight vector* on a `Finset s` is a function `f : X → ℝ≥0∞` with `∑ x ∈ s, f x = 1`; the
weights of a probability measure on its finite carrier are the motivating example.  This file
records the arithmetic of comparing two weight vectors, and of rounding one onto a grid.

When a weight vector `g` is dominated by `f` away from one designated atom `x₀` -- so that `g`
arises from `f` by transferring weight onto `x₀` -- the designated atom can only gain, and it
gains exactly the total excess `∑ x ∈ s, (f x - g x)`.  Only equality of the two total masses and
finiteness of `f` away from `x₀` are used there, not normalization to one: the weights at `x₀`
may be infinite.

A weighted sum with weights summing to one is at most twice its part over the large terms, as
soon as it is at least twice the threshold separating large terms from small ones.

Rounding to a common denominator `M` cannot be done pointwise, since the weights have to keep
summing to one.  `TauCeti.exists_nat_weights_of_sum_eq_one` rounds every weight but the one at
`x₀` down to a multiple of `1 / M` and lets `x₀` absorb the slack; the rounded weights are then
dominated away from `x₀` and lose less than `1 / M` each.

## Main results

* `ENNReal.toReal_sub_add_toReal_sub` -- the excesses in both directions add up to the distance;
* `TauCeti.sum_mul_le_two_mul_sum_mul_ite` -- a weighted sum is dominated by its large terms;
* `TauCeti.le_of_sum_eq_of_forall_ne_le` -- an atom dominating everywhere else can only gain;
* `TauCeti.add_sum_tsub_eq_of_forall_ne_le` -- it gains exactly the total excess;
* `TauCeti.exists_nat_weights_of_sum_eq_one` -- rounding a weight vector to a common denominator.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*}

/-- The excess of `a` over `b` and the excess of `b` over `a` add up to their distance: for finite
`a` and `b`, `(a - b) + (b - a) = |a - b|`, read in `ℝ`. -/
theorem _root_.ENNReal.toReal_sub_add_toReal_sub {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a - b).toReal + (b - a).toReal = |a.toReal - b.toReal| := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_sub_of_le h hb, ENNReal.toReal_zero, zero_add,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono hb h))]
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_sub_of_le h ha, ENNReal.toReal_zero, add_zero,
      abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono ha h))]

/-- For weights summing to `1` and a threshold `t` with `2 t ≤ ∑ j, w j * a j`, the weighted sum is
at most twice its part over the indices with `t ≤ a j`: the other terms contribute at most `t`. -/
theorem sum_mul_le_two_mul_sum_mul_ite {J : Type*} [Fintype J] {w : J → ℝ≥0}
    (hw : ∑ j, w j = 1) (a : J → ℝ≥0∞) {t : ℝ≥0∞}
    (h : 2 * t ≤ ∑ j, (w j : ℝ≥0∞) * a j) :
    ∑ j, (w j : ℝ≥0∞) * a j ≤ 2 * ∑ j, (w j : ℝ≥0∞) * if t ≤ a j then a j else 0 := by
  set B := ∑ j, (w j : ℝ≥0∞) * if t ≤ a j then a j else 0
  by_cases ht : t = ∞
  · -- The sum is `∞`, so some term with `a j = ∞` and a nonzero weight lies in the part.
    subst ht
    rw [ENNReal.mul_top two_ne_zero, top_le_iff, ENNReal.sum_eq_top] at h
    obtain ⟨j, -, hj⟩ := h
    obtain ⟨hwj, haj⟩ : (w j : ℝ≥0∞) ≠ 0 ∧ a j = ∞ := by
      rcases ENNReal.mul_eq_top.1 hj with h' | h'
      · exact h'
      · exact absurd h'.1 ENNReal.coe_ne_top
    have hB : B = ∞ := top_le_iff.1 <| by
      calc (∞ : ℝ≥0∞) = (w j : ℝ≥0∞) * if ∞ ≤ a j then a j else 0 := by
            simp [haj, ENNReal.mul_top hwj]
        _ ≤ B := Finset.single_le_sum (f := fun j ↦ (w j : ℝ≥0∞) * if ∞ ≤ a j then a j else 0)
            (fun _ _ ↦ bot_le) (Finset.mem_univ j)
    simp [hB]
  have hsplit : ∑ j, (w j : ℝ≥0∞) * a j ≤ B + t := by
    calc ∑ j, (w j : ℝ≥0∞) * a j
        ≤ ∑ j, ((w j : ℝ≥0∞) * (if t ≤ a j then a j else 0) + (w j : ℝ≥0∞) * t) := by
          gcongr with j
          split_ifs with hj
          · exact le_self_add
          · rw [mul_zero, zero_add]
            gcongr
            exact (not_le.1 hj).le
      _ = B + t := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum, hw,
            ENNReal.coe_one, one_mul]
  have htB : t ≤ B := (ENNReal.add_le_add_iff_right ht).1 <| by
    rw [← two_mul]
    exact h.trans hsplit
  calc ∑ j, (w j : ℝ≥0∞) * a j ≤ B + t := hsplit
    _ ≤ B + B := by gcongr
    _ = 2 * B := (two_mul B).symm


variable {s : Finset X} {f g : X → ℝ≥0∞} {x₀ : X}

/-- The total weight of `g` away from `x₀` is finite and at most that of `f`. -/
private theorem sum_erase_le_and_ne_top [DecidableEq X] (hne : ∀ x ∈ s, x ≠ x₀ → f x ≠ ⊤)
    (hdom : ∀ x ∈ s, x ≠ x₀ → g x ≤ f x) :
    ∑ x ∈ s.erase x₀, g x ≤ ∑ x ∈ s.erase x₀, f x ∧ ∑ x ∈ s.erase x₀, g x ≠ ⊤ := by
  have hle : ∑ x ∈ s.erase x₀, g x ≤ ∑ x ∈ s.erase x₀, f x :=
    Finset.sum_le_sum fun x hx => hdom x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
  refine ⟨hle, ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun x hx => ?_) hle⟩
  exact hne x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)

/-- Away from `x₀` the smaller of two weight vectors of equal total mass is `g`, and `f` is finite
there, so the designated atom `x₀` can only gain weight. -/
theorem le_of_sum_eq_of_forall_ne_le (hx₀ : x₀ ∈ s) (hfg : ∑ x ∈ s, f x = ∑ x ∈ s, g x)
    (hne : ∀ x ∈ s, x ≠ x₀ → f x ≠ ⊤) (hdom : ∀ x ∈ s, x ≠ x₀ → g x ≤ f x) : f x₀ ≤ g x₀ := by
  classical
  obtain ⟨hle, hfin⟩ := sum_erase_le_and_ne_top hne hdom
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc f x₀ + ∑ x ∈ s.erase x₀, g x ≤ f x₀ + ∑ x ∈ s.erase x₀, f x := by gcongr
    _ = g x₀ + ∑ x ∈ s.erase x₀, g x := by simpa only [Finset.add_sum_erase _ _ hx₀] using hfg

/-- The designated atom `x₀` absorbs exactly the total weight transferred onto it. -/
theorem add_sum_tsub_eq_of_forall_ne_le (hx₀ : x₀ ∈ s) (hfg : ∑ x ∈ s, f x = ∑ x ∈ s, g x)
    (hne : ∀ x ∈ s, x ≠ x₀ → f x ≠ ⊤) (hdom : ∀ x ∈ s, x ≠ x₀ → g x ≤ f x) :
    f x₀ + ∑ x ∈ s, (f x - g x) = g x₀ := by
  classical
  refine (ENNReal.add_left_inj (sum_erase_le_and_ne_top hne hdom).2).1 ?_
  have hsub : ∑ x ∈ s.erase x₀, (f x - g x) + ∑ x ∈ s.erase x₀, g x = ∑ x ∈ s.erase x₀, f x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le
      (hdom x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
  rw [← Finset.add_sum_erase s (fun x => f x - g x) hx₀,
    tsub_eq_zero_of_le (le_of_sum_eq_of_forall_ne_le hx₀ hfg hne hdom), zero_add, add_assoc, hsub,
    Finset.add_sum_erase _ _ hx₀, hfg, Finset.add_sum_erase _ _ hx₀]

/-- **Rounding a weight vector to a common denominator.**  A weight vector of total mass one is
turned into one whose entries are the multiples `m x / M` of `1 / M`, by rounding every weight but
the one at a designated atom `x₀` down and letting `x₀` absorb the slack.  Away from `x₀` the
rounded weight is below the original one and within `1 / M` of it; at `x₀` nothing is claimed,
since that is where all the slack goes.

The conclusion is stated multiplicatively, as `m x ≤ M * f x` and `M * f x ≤ m x + 1`, so that it
holds with no inequality between `M` and the size of the weights. -/
theorem exists_nat_weights_of_sum_eq_one (hx₀ : x₀ ∈ s) (hf : ∑ x ∈ s, f x = 1) (M : ℕ) :
    ∃ m : X → ℕ, ∑ x ∈ s, m x = M ∧ (∀ x ∈ s, x ≠ x₀ → (m x : ℝ≥0∞) ≤ M * f x) ∧
      ∀ x ∈ s, x ≠ x₀ → (M : ℝ≥0∞) * f x ≤ (m x : ℝ≥0∞) + 1 := by
  classical
  -- an entry of a weight vector of total mass one is at most one, hence finite
  have hfin : ∀ y ∈ s, f y ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (hf ▸ Finset.single_le_sum (f := f) (fun z _ => zero_le) hy)
  have hmul : ∀ y ∈ s, (M : ℝ≥0∞) * f y = ENNReal.ofReal ((M : ℝ) * (f y).toReal) := fun y hy => by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal (hfin y hy)]
  have hfloor_le : ∀ y ∈ s, ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) ≤ M * f y := fun y hy => by
    rw [hmul y hy, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.floor_le (by positivity))
  have hlt_floor : ∀ y ∈ s, (M : ℝ≥0∞) * f y ≤ ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) + 1 :=
    fun y hy => by
      rw [hmul y hy, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by positivity) zero_le_one]
      exact ENNReal.ofReal_le_ofReal (Nat.lt_floor_add_one _).le
  have herase : ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (f y).toReal⌋₊ ≤ M := by
    have hcast : ((∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
      push_cast
      calc ∑ y ∈ s.erase x₀, ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞)
          ≤ ∑ y ∈ s.erase x₀, (M : ℝ≥0∞) * f y :=
            Finset.sum_le_sum fun y hy => hfloor_le y (Finset.mem_of_mem_erase hy)
        _ = (M : ℝ≥0∞) * ∑ y ∈ s.erase x₀, f y := by rw [Finset.mul_sum]
        _ ≤ (M : ℝ≥0∞) * 1 := by
            gcongr
            rw [← hf]
            exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        _ = M := mul_one _
    exact_mod_cast hcast
  refine ⟨fun x => if x = x₀ then M - ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (f y).toReal⌋₊
    else ⌊(M : ℝ) * (f x).toReal⌋₊, ?_, ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ hx₀]
    have h : ∑ y ∈ s.erase x₀, (if y = x₀ then
        M - ∑ z ∈ s.erase x₀, ⌊(M : ℝ) * (f z).toReal⌋₊ else ⌊(M : ℝ) * (f y).toReal⌋₊)
        = ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (f y).toReal⌋₊ :=
      Finset.sum_congr rfl fun y hy => by simp [Finset.ne_of_mem_erase hy]
    rw [h]
    simp only [↓reduceIte]
    omega
  · exact fun x hxs hx => by simpa only [ite_eq_right hx] using hfloor_le x hxs
  · exact fun x hxs hx => by simpa only [ite_eq_right hx] using hlt_floor x hxs

end TauCeti

end
