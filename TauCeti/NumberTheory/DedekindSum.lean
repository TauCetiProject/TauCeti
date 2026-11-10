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
import TauCeti.Algebra.BigOperators.FloorSum
import TauCeti.Data.Nat.Cast.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Positivity

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

/-- The characteristic finite-sum formula for the Dedekind sum. -/
theorem dedekindSum_def (d c : ℤ) :
    dedekindSum d c =
      ∑ r ∈ Ioo 0 c, (r / c : ℚ) * (Int.fract ((d * r : ℤ) / c : ℚ) - 1 / 2) := by
  unfold dedekindSum
  rfl

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

/-- The Dedekind sum through the floor sum `∑_{r < c} r ⌊h r / c⌋`:
`s(h, c) = h (c - 1)(2c - 1) / (6c) - (∑_{r < c} r ⌊h r / c⌋) / c - (c - 1) / 4`. -/
private theorem dedekindSum_natCast_eq_floorSum {c : ℕ} (hc : 0 < c) (h : ℕ) :
    dedekindSum h c = h * (c - 1) * (2 * c - 1) / (6 * c) -
      (∑ r ∈ range c, r * (h * r / c) : ℕ) / c - (c - 1) / 4 := by
  have hc' : (c : ℚ) ≠ 0 := by positivity
  have hterm (r : ℕ) : ((r : ℚ) / c) * (((h * r % c : ℕ) : ℚ) / c - 1 / 2) =
      h / c ^ 2 * (r : ℚ) ^ 2 - 1 / c * ((r * (h * r / c) : ℕ) : ℚ) - 1 / (2 * c) * r := by
    rw [Nat.cast_mod_eq_sub_mul_div]
    push_cast
    field_simp
  rw [dedekindSum_natCast, sum_congr rfl fun r _ ↦ hterm r, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, sum_range_cast_sq, sum_range_cast_id]
  push_cast
  field_simp
  ring

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
  have h₁ := hhc.symm.mul_sum_div (K := ℚ)
  have h₂ := hhc.symm.sq_mul_sum_div_sq (K := ℚ)
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
