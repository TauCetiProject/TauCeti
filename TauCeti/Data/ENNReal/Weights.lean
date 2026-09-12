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

Two weight vectors split against each other: the mass `min (f x) (g x)` matched at `x` and the
excess `f x - g x` above `g` add up to `f x`.  When `g` is dominated by `f` away from one
designated atom `x₀` -- so that `g` arises from `f` by transferring weight onto `x₀` -- the
designated atom can only gain, and it gains exactly the total excess.  Only equality of the two
finite total masses is used there, not normalization to one.

Rounding to a common denominator `M` cannot be done pointwise, since the weights have to keep
summing to one.  `TauCeti.exists_nat_weights_of_sum_eq_one` rounds every weight but the one at
`x₀` down to a multiple of `1 / M` and lets `x₀` absorb the slack; the rounded weights are then
dominated away from `x₀` and lose less than `1 / M` each.

## Main results

* `Finset.sum_min_add_sum_tsub` -- the matched mass and the excess mass add up to the total;
* `TauCeti.le_of_sum_eq_of_forall_ne_le` -- an atom dominating everywhere else can only gain;
* `TauCeti.add_sum_tsub_eq_of_forall_ne_le` -- it gains exactly the total excess;
* `TauCeti.exists_nat_weights_of_sum_eq_one` -- rounding a weight vector to a common denominator.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {X : Type*}

/-- The mass of `f` matched by `g` and the mass of `f` above `g` add up to `f`. -/
theorem _root_.Finset.sum_min_add_sum_tsub (s : Finset X) (f g : X → ℝ≥0∞) :
    ∑ x ∈ s, min (f x) (g x) + ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => (add_comm _ _).trans tsub_add_min

variable {s : Finset X} {f g : X → ℝ≥0∞} {x₀ : X}

/-- Away from `x₀` the smaller of two weight vectors of equal finite total mass is `g`, so the
designated atom `x₀` can only gain weight. -/
theorem le_of_sum_eq_of_forall_ne_le (hx₀ : x₀ ∈ s) (hfg : ∑ x ∈ s, f x = ∑ x ∈ s, g x)
    (hne : ∑ x ∈ s, f x ≠ ⊤) (hdom : ∀ x ∈ s, x ≠ x₀ → g x ≤ f x) : f x₀ ≤ g x₀ := by
  by_contra hlt
  push Not at hlt
  have hmin : ∀ x ∈ s, min (f x) (g x) = g x := fun x hx => by
    rcases eq_or_ne x x₀ with rfl | hx'
    · exact min_eq_right hlt.le
    · exact min_eq_right (hdom x hx hx')
  have hsum : ∑ x ∈ s, g x + ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x := by
    have h := Finset.sum_min_add_sum_tsub s f g
    rwa [Finset.sum_congr rfl hmin] at h
  have key : ∑ x ∈ s, g x + ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, g x + 0 := by
    rw [add_zero, hsum, hfg]
  have hzero : ∑ x ∈ s, (f x - g x) = 0 :=
    (ENNReal.add_right_inj (by rw [← hfg]; exact hne)).1 key
  exact absurd (tsub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hzero x₀ hx₀)) (not_le.2 hlt)

open scoped Classical in
/-- The designated atom `x₀` absorbs exactly the total weight transferred onto it. -/
theorem add_sum_tsub_eq_of_forall_ne_le (hx₀ : x₀ ∈ s) (hfg : ∑ x ∈ s, f x = ∑ x ∈ s, g x)
    (hne : ∑ x ∈ s, f x ≠ ⊤) (hdom : ∀ x ∈ s, x ≠ x₀ → g x ≤ f x) :
    f x₀ + ∑ x ∈ s, (f x - g x) = g x₀ := by
  have hx := le_of_sum_eq_of_forall_ne_le hx₀ hfg hne hdom
  have hsplit : ∀ x ∈ s, min (f x) (g x) + (if x = x₀ then g x₀ - f x₀ else 0) = g x := by
    intro x hxs
    split_ifs with hxx
    · subst hxx
      rw [min_eq_left hx, add_tsub_cancel_of_le hx]
    · rw [add_zero]
      exact min_eq_right (hdom x hxs hxx)
  have hsum : ∑ x ∈ s, min (f x) (g x) + (g x₀ - f x₀) = ∑ x ∈ s, g x := by
    have h1 : ∑ x ∈ s, (min (f x) (g x) + (if x = x₀ then g x₀ - f x₀ else 0)) = ∑ x ∈ s, g x :=
      Finset.sum_congr rfl hsplit
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' s x₀ fun _ => g x₀ - f x₀] at h1
    simpa [hx₀] using h1
  have hfin : ∑ x ∈ s, min (f x) (g x) ≠ ⊤ :=
    ne_top_of_le_ne_top hne (Finset.sum_le_sum fun x _ => min_le_left _ _)
  have hdiff : ∑ x ∈ s, (f x - g x) = g x₀ - f x₀ :=
    (ENNReal.add_right_inj hfin).1
      (((Finset.sum_min_add_sum_tsub s f g).trans hfg).trans hsum.symm)
  rw [hdiff, add_tsub_cancel_of_le hx]

/-- **Rounding a weight vector to a common denominator.**  A weight vector of total mass one is
turned into one whose entries are the multiples `m x / M` of `1 / M`, by rounding every weight but
the one at a designated atom `x₀` down and letting `x₀` absorb the slack.  Away from `x₀` the
rounded weight is below the original one and within `1 / M` of it; at `x₀` nothing is claimed,
since that is where all the slack goes.

The conclusion is stated multiplicatively, as `m x ≤ M * f x` and `M * f x ≤ m x + 1`, so that it
holds with no inequality between `M` and the size of the weights. -/
theorem exists_nat_weights_of_sum_eq_one (hx₀ : x₀ ∈ s) (hf : ∑ x ∈ s, f x = 1) {M : ℕ}
    (hM : 0 < M) :
    ∃ m : X → ℕ, ∑ x ∈ s, m x = M ∧ (∀ x ∈ s, x ≠ x₀ → (m x : ℝ≥0∞) ≤ M * f x) ∧
      ∀ x ∈ s, x ≠ x₀ → (M : ℝ≥0∞) * f x ≤ (m x : ℝ≥0∞) + 1 := by
  classical
  -- an entry of a weight vector of total mass one is at most one, hence finite
  have hfin : ∀ y ∈ s, f y ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (hf ▸ Finset.single_le_sum (f := f) (fun z _ => zero_le) hy)
  have hfloor_le : ∀ y ∈ s, ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) ≤ M * f y := by
    intro y hy
    calc ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (⌊(M : ℝ) * (f y).toReal⌋₊ : ℝ) := by rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((M : ℝ) * (f y).toReal) :=
          ENNReal.ofReal_le_ofReal (Nat.floor_le (by positivity))
      _ = M * f y := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_toReal (hfin y hy)]
  have hlt_floor : ∀ y ∈ s, (M : ℝ≥0∞) * f y ≤ ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) + 1 := by
    intro y hy
    calc (M : ℝ≥0∞) * f y = ENNReal.ofReal ((M : ℝ) * (f y).toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_toReal (hfin y hy)]
      _ ≤ ENNReal.ofReal ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℝ) + 1) :=
          ENNReal.ofReal_le_ofReal (Nat.lt_floor_add_one _).le
      _ = ((⌊(M : ℝ) * (f y).toReal⌋₊ : ℕ) : ℝ≥0∞) + 1 := by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
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
