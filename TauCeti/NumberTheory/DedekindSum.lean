/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Positivity
import TauCeti.Data.Nat.ModEq

/-!
# Dedekind sums and their reciprocity law

For integers `d` and `c`, the Dedekind sum is
`s(d, c) = ∑_{r=1}^{c-1} (r / c) (⟨d r / c⟩ - 1/2)`, where `⟨x⟩ = x - ⌊x⌋` is the fractional part.
For `c ≥ 1` coprime to `d` this is the classical sum `∑_{r mod c} ((r / c)) ((d r / c))` of the
sawtooth function `((x)) = ⟨x⟩ - 1/2` (with `((x)) = 0` at integers), since then `c ∤ d r` for
`0 < r < c`. Dedekind sums give the root of unity in the transformation law of the Dedekind eta
function under `SL₂(ℤ)`: for `γ = (a b; c d)` with `c > 0` it is
`exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`.

The sum depends on `d` only modulo `c`, it is odd in `d` when `d` is coprime to `c`, and it
satisfies Dedekind's reciprocity law: for coprime `h, c ≥ 1`,
`s(h, c) + s(c, h) = (h² + c² + 1) / (12 h c) - 1/4`.

## Implementation notes

The proof of the reciprocity law is elementary. Writing `⟨h r / c⟩ = h r / c - ⌊h r / c⌋` turns
`s(h, c)` into the floor sum `∑_{r < c} r ⌊h r / c⌋`. Since `r ↦ h r mod c` permutes the residues
modulo `c`, summing `h r - c ⌊h r / c⌋` and its square over them gives two linear relations among
`∑ ⌊h r / c⌋`, `∑ ⌊h r / c⌋²` and the floor sum. Counting, with weight `r`, the lattice points of
the rectangle `[0, c) × [0, h)` on the two sides of the diagonal `c s = h r` relates the floor
sum for `(h, c)` to the sums of `⌊c s / h⌋` and `⌊c s / h⌋²`, and the reciprocity law follows.

## Main definitions

* `TauCeti.dedekindSum d c`: the Dedekind sum `s(d, c)`, as a rational number.

## Main results

* `TauCeti.dedekindSum_add_mul_self`, `TauCeti.dedekindSum_emod`: `s(d, c)` depends only on
  `d mod c`.
* `TauCeti.dedekindSum_neg`: `s(-d, c) = -s(d, c)` for `d` coprime to `c`.
* `TauCeti.dedekindSum_add_dedekindSum`: the reciprocity law of Dedekind sums.
* `TauCeti.dedekindSum_one_left`: `s(1, c) = (c - 1)(c - 2) / (12 c)` for `c ≥ 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  §§3.4–3.7 (the eta transformation and Theorem 3.7, the reciprocity law).
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, Chapter 2
  (the elementary lattice-point proof of the reciprocity law).
-/

public section

open Finset

namespace TauCeti

/-- The **Dedekind sum** `s(d, c) = ∑_{r=1}^{c-1} (r / c) (⟨d r / c⟩ - 1/2)`, where `⟨x⟩` is the
fractional part `Int.fract x`. It vanishes for `c ≤ 1`. For `d` coprime to `c ≥ 1` this is the
classical sum of products of sawtooth functions `((r / c)) ((d r / c))`; when `gcd(d, c) > 1`, a
summand with `c ∣ d r` contributes `-r / (2c)` here rather than the sawtooth value `0`. -/
def dedekindSum (d c : ℤ) : ℚ :=
  ∑ r ∈ Ioo 0 c, (r / c : ℚ) * (Int.fract ((d * r : ℤ) / c : ℚ) - 1 / 2)

/-- The Dedekind sum `s(d, c)` depends on `d` only modulo `c`. -/
@[simp]
theorem dedekindSum_add_mul_self (d k c : ℤ) : dedekindSum (d + k * c) c = dedekindSum d c := by
  refine sum_congr rfl fun r hr ↦ ?_
  have hc : (c : ℚ) ≠ 0 := by
    have := (mem_Ioo.1 hr).1.trans (mem_Ioo.1 hr).2
    positivity
  have : (((d + k * c) * r : ℤ) : ℚ) / c = ((d * r : ℤ) : ℚ) / c + ((k * r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [this, Int.fract_add_intCast]

/-- The Dedekind sum `s(d, c)` only depends on the residue `d % c`. -/
@[simp]
theorem dedekindSum_emod (d c : ℤ) : dedekindSum (d % c) c = dedekindSum d c := by
  conv_rhs => rw [← Int.emod_add_ediv_mul d c]
  exact (dedekindSum_add_mul_self _ _ _).symm

/-- For `d` coprime to `c`, the Dedekind sum is odd in `d`: `s(-d, c) = -s(d, c)`. -/
theorem dedekindSum_neg {d c : ℤ} (hdc : IsCoprime d c) :
    dedekindSum (-d) c = -dedekindSum d c := by
  rw [dedekindSum, dedekindSum, ← sum_neg_distrib]
  refine sum_congr rfl fun r hr ↦ ?_
  obtain ⟨hr0, hrc⟩ := mem_Ioo.1 hr
  have hc : (c : ℚ) ≠ 0 := by
    have := hr0.trans hrc
    positivity
  -- Since `c ∤ d r` for `0 < r < c`, the fractional part of `d r / c` is nonzero.
  have hfract : Int.fract (((d * r : ℤ) : ℚ) / c) ≠ 0 := by
    rw [Ne, Int.fract_eq_zero_iff]
    rintro ⟨z, hz⟩
    have hdr : d * r = c * z := by
      rw [eq_div_iff hc] at hz
      exact_mod_cast (hz.symm.trans (mul_comm _ _))
    have hdvd : c ∣ r := hdc.symm.dvd_of_dvd_mul_left ⟨z, hdr⟩
    exact (Int.le_of_dvd hr0 hdvd).not_gt hrc
  rw [show ((-d * r : ℤ) : ℚ) / c = -(((d * r : ℤ) : ℚ) / c) by push_cast; ring,
    Int.fract_neg hfract]
  ring

/-- The Dedekind sum `s(d, c)` is the empty sum for `c ≤ 1`. -/
theorem dedekindSum_of_le_one (d : ℤ) {c : ℤ} (hc : c ≤ 1) : dedekindSum d c = 0 := by
  exact sum_eq_zero fun r hr ↦ absurd hr (by rw [mem_Ioo]; omega)

@[simp]
theorem dedekindSum_one_right (d : ℤ) : dedekindSum d 1 = 0 :=
  dedekindSum_of_le_one d le_rfl

/-! ### The reciprocity law -/

/-- For natural arguments, `s(h, c) = ∑_{r < c} (r / c) ((h r mod c) / c - 1/2)`. -/
private theorem dedekindSum_natCast (h c : ℕ) :
    dedekindSum h c = ∑ r ∈ range c, ((r : ℚ) / c) * (((h * r % c : ℕ) : ℚ) / c - 1 / 2) := by
  rw [dedekindSum, ← sum_subset (s₁ := Ioo 0 c) (fun r hr ↦ mem_range.2 (mem_Ioo.1 hr).2)]
  · refine sum_nbij' Int.toNat Nat.cast (fun r hr ↦ ?_) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
      (fun r hr ↦ ?_) (fun r hr ↦ ?_)
    · simp only [mem_Ioo] at hr ⊢; omega
    · simp only [mem_Ioo] at hr ⊢; omega
    · simp only [mem_Ioo] at hr ⊢; omega
    · simp
    · simp only [mem_Ioo] at hr
      lift r to ℕ using hr.1.le
      simp only [Int.toNat_natCast, Int.cast_natCast]
      rw [← Int.fract_div_natCast_eq_div_natCast_mod]
      push_cast
      rfl
  · intro r hrc hr
    obtain rfl : r = 0 := by
      rw [mem_Ioo] at hr
      rw [mem_range] at hrc
      omega
    simp

private theorem sum_range_cast_id (n : ℕ) : ∑ r ∈ range n, (r : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem sum_range_cast_sq (n : ℕ) :
    ∑ r ∈ range n, (r : ℚ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem natCast_mul_mod (h c r : ℕ) :
    ((h * r % c : ℕ) : ℚ) = h * r - c * (h * r / c : ℕ) := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]

/-- The Dedekind sum through the floor sum `∑_{r < c} r ⌊h r / c⌋`:
`s(h, c) = h (c - 1)(2c - 1) / (6c) - (∑_{r < c} r ⌊h r / c⌋) / c - (c - 1) / 4`. -/
private theorem dedekindSum_natCast_eq_floorSum {c : ℕ} (hc : 0 < c) (h : ℕ) :
    dedekindSum h c = h * (c - 1) * (2 * c - 1) / (6 * c) -
      (∑ r ∈ range c, r * (h * r / c) : ℕ) / c - (c - 1) / 4 := by
  have hc' : (c : ℚ) ≠ 0 := by positivity
  have hterm (r : ℕ) : ((r : ℚ) / c) * (((h * r % c : ℕ) : ℚ) / c - 1 / 2) =
      h / c ^ 2 * (r : ℚ) ^ 2 - 1 / c * ((r * (h * r / c) : ℕ) : ℚ) - 1 / (2 * c) * r := by
    rw [natCast_mul_mod]
    push_cast
    field_simp
  rw [dedekindSum_natCast, sum_congr rfl fun r _ ↦ hterm r, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, sum_range_cast_sq, sum_range_cast_id]
  push_cast
  field_simp
  ring

/-- Summing `h r = c ⌊h r / c⌋ + (h r mod c)` over a full residue system. -/
private theorem mul_sum_div {h c : ℕ} (hhc : h.Coprime c) :
    (c : ℚ) * ∑ r ∈ range c, ((h * r / c : ℕ) : ℚ) = (h - 1) * (c * (c - 1) / 2) := by
  have hperm := Nat.Coprime.sum_range_mul_mod hhc (fun r ↦ (r : ℚ))
  simp only [natCast_mul_mod, sum_sub_distrib, ← mul_sum, sum_range_cast_id] at hperm
  linear_combination -hperm

/-- Summing the squares of `h r - c ⌊h r / c⌋` over a full residue system. -/
private theorem sq_mul_sum_div_sq {h c : ℕ} (hhc : h.Coprime c) :
    (c : ℚ) ^ 2 * ∑ r ∈ range c, ((h * r / c : ℕ) : ℚ) ^ 2 =
      2 * h * c * (∑ r ∈ range c, r * (h * r / c) : ℕ) +
        (1 - h ^ 2) * (c * (c - 1) * (2 * c - 1) / 6) := by
  have hperm := Nat.Coprime.sum_range_mul_mod hhc (fun r ↦ (r : ℚ) ^ 2)
  have hterm (r : ℕ) : (((h * r % c : ℕ) : ℚ)) ^ 2 = h ^ 2 * (r : ℚ) ^ 2 -
      2 * h * c * ((r * (h * r / c) : ℕ) : ℚ) + c ^ 2 * ((h * r / c : ℕ) : ℚ) ^ 2 := by
    rw [natCast_mul_mod]
    push_cast
    ring
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_range_cast_sq] at hperm
  push_cast at hperm ⊢
  linear_combination hperm

/-- The lattice points `(r, s)` with `0 ≤ s < h` lying below the line `c s = h r`. -/
private theorem filter_range_mul_le {h c r : ℕ} (hh : 0 < h) (hc : 0 < c) (hr : r < c) :
    (range h).filter (fun s ↦ c * s ≤ h * r) = range (h * r / c + 1) := by
  ext s
  simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hc]
  constructor
  · rintro ⟨-, hs⟩
    linarith
  · intro hs
    refine ⟨?_, by linarith⟩
    by_contra! hsh
    nlinarith

/-- Counting the lattice points of the rectangle `[0, c) × [0, h)` on either side of the
diagonal `c s = h r`, weighted by `r`. -/
private theorem sum_mul_div_add_sum_sum {h c : ℕ} (hh : 0 < h) (hc : 0 < c)
    (hhc : h.Coprime c) :
    ∑ r ∈ range c, r * (h * r / c + 1) + ∑ s ∈ range h, ∑ r ∈ range (c * s / h + 1), r =
      h * ∑ r ∈ range c, r := by
  have hsplit : ∀ r ∈ range c, ∀ s ∈ range h,
      (if c * s ≤ h * r then r else 0) + (if h * r ≤ c * s then r else 0) = r := by
    intro r hr s hs
    rw [mem_range] at hr hs
    by_cases h₁ : c * s ≤ h * r <;> by_cases h₂ : h * r ≤ c * s <;> simp only [h₁, h₂,
      ↓reduceIte, add_zero, zero_add]
    · have hdvd : c ∣ r := hhc.symm.dvd_of_dvd_mul_left ⟨s, (le_antisymm h₁ h₂).symm⟩
      obtain rfl : r = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hr
      rfl
    · omega
  have h₁ : ∑ r ∈ range c, ∑ s ∈ range h, (if c * s ≤ h * r then r else 0) =
      ∑ r ∈ range c, r * (h * r / c + 1) := by
    refine sum_congr rfl fun r hr ↦ ?_
    rw [← sum_filter, filter_range_mul_le hh hc (mem_range.1 hr), sum_const, card_range,
      smul_eq_mul, mul_comm]
  have h₂ : ∑ r ∈ range c, ∑ s ∈ range h, (if h * r ≤ c * s then r else 0) =
      ∑ s ∈ range h, ∑ r ∈ range (c * s / h + 1), r := by
    rw [sum_comm]
    refine sum_congr rfl fun s hs ↦ ?_
    rw [← sum_filter, filter_range_mul_le hc hh (mem_range.1 hs)]
  rw [← h₁, ← h₂, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [← sum_add_distrib, sum_congr rfl (hsplit r hr), sum_const, card_range, smul_eq_mul]

/-- **The reciprocity law of Dedekind sums** (Apostol, Theorem 3.7): for coprime integers
`h, c ≥ 1`, `s(h, c) + s(c, h) = (h² + c² + 1) / (12 h c) - 1/4`. -/
theorem dedekindSum_add_dedekindSum {h c : ℤ} (hh : 0 < h) (hc : 0 < c) (hhc : IsCoprime h c) :
    dedekindSum h c + dedekindSum c h = (h ^ 2 + c ^ 2 + 1) / (12 * h * c) - 1 / 4 := by
  lift h to ℕ using hh.le
  lift c to ℕ using hc.le
  rw [Nat.isCoprime_iff_coprime] at hhc
  have hh' : 0 < h := by exact_mod_cast hh
  have hc' : 0 < c := by exact_mod_cast hc
  have hh'' : (h : ℚ) ≠ 0 := by positivity
  have hc'' : (c : ℚ) ≠ 0 := by positivity
  -- The lattice-point count, with `∑_{r ≤ p} r = p (p + 1) / 2` for `p = ⌊c s / h⌋`.
  have hcount := congrArg (Nat.cast : ℕ → ℚ) (sum_mul_div_add_sum_sum hh' hc' hhc)
  have hp (x : ℕ) : ((c * x / h + 1 : ℕ) : ℚ) * (((c * x / h + 1 : ℕ) : ℚ) - 1) / 2 =
      (((c * x / h : ℕ) : ℚ) ^ 2 + ((c * x / h : ℕ) : ℚ)) / 2 := by
    push_cast
    ring
  push_cast at hcount
  simp only [sum_range_cast_id, mul_add, mul_one, sum_add_distrib, hp, ← sum_div] at hcount
  -- The two residue-permutation identities for `c` modulo `h`.
  have h₁ := mul_sum_div hhc.symm
  have h₂ := sq_mul_sum_div_sq hhc.symm
  push_cast at h₂
  -- Eliminating the sums of `⌊c s / h⌋` and `⌊c s / h⌋²` relates the two floor sums.
  have hST : (h : ℚ) * ∑ x ∈ range c, (x : ℚ) * ((h * x / c : ℕ) : ℚ) +
      c * ∑ x ∈ range h, (x : ℚ) * ((c * x / h : ℕ) : ℚ) =
      h * (h - 1) * (c * (c - 1) / 2) -
        ((1 - c ^ 2) * ((h - 1) * (2 * h - 1) / 6) + (c - 1) * (h * (h - 1) / 2)) / 2 := by
    refine mul_left_cancel₀ hh'' ?_
    linear_combination h ^ 2 * hcount - (1 / 2 : ℚ) * h₂ - (h / 2 : ℚ) * h₁
  rw [dedekindSum_natCast_eq_floorSum hc', dedekindSum_natCast_eq_floorSum hh']
  push_cast
  field_simp
  linear_combination (-288 : ℚ) * hST

/-- The Dedekind sum `s(1, c) = (c - 1)(c - 2) / (12 c)` for `c ≥ 0`; for `c ≥ 1` this is the case
`h = 1` of the reciprocity law. -/
theorem dedekindSum_one_left {c : ℤ} (hc : 0 ≤ c) :
    dedekindSum 1 c = (c - 1) * (c - 2) / (12 * c) := by
  obtain rfl | hc := hc.eq_or_lt
  · simp [dedekindSum_of_le_one]
  have h := dedekindSum_add_dedekindSum one_pos hc isCoprime_one_left
  rw [dedekindSum_one_right, add_zero] at h
  have hc' : (c : ℚ) ≠ 0 := by positivity
  rw [h]
  field_simp
  ring
end TauCeti
