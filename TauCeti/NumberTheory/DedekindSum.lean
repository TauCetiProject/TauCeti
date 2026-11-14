/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.FloorSum

/-!
# The sawtooth function and Dedekind sums

This file defines the odd, period-`1` sawtooth function `((x))` (`TauCeti.sawtooth`) and the
classical Dedekind sum `s(d, c)` (`TauCeti.dedekindSum`), together with its basic modular
symmetries and Dedekind's reciprocity law.

For a linearly ordered floor field `k`, `sawtooth x` is `0` when `x` is an integer
(`Int.fract x = 0`) and `Int.fract x - 1 / 2` otherwise. Setting `sawtooth` to `0` at integers
makes it odd everywhere (`sawtooth (-x) = -sawtooth x`), not only away from `ℤ`. Consequently, for
every `d, c : ℤ` the sum `∑ r ∈ Finset.Ioo 0 c, sawtooth (d * r / c)` vanishes by the reflection
`r ↦ c - r`, so the symmetric definition
$$s(d, c) = \sum_{r = 1}^{c - 1} \left(\!\left(\frac{r}{c}\right)\!\right)
  \left(\!\left(\frac{d r}{c}\right)\!\right)$$
coincides unconditionally with `∑ r ∈ Finset.Ioo 0 c, (r / c) * sawtooth (d * r / c)`, and when
`IsCoprime d c` none of the arguments `d * r / c` is an integer, giving the unguarded
fractional-part sum `∑ r ∈ Finset.Ioo 0 c, (r / c) * (Int.fract (d * r / c) - 1 / 2)`.

Dedekind's reciprocity law (`TauCeti.dedekindSum_add_dedekindSum`) is proved by Rademacher's
elementary lattice-point method, combining the residue bijection `x ↦ m * x % n` on `Finset.Ico 1 n`
with Gauss's floor-sum reciprocity and the weighted square floor-sum identity from
`TauCeti.Data.Nat.FloorSum`.

## Main definitions

* `TauCeti.sawtooth`: the odd period-`1` sawtooth function `((x))`.
* `TauCeti.dedekindSum`: the Dedekind sum `s(d, c) : ℚ` for `d, c : ℤ`.

## Main results

* `TauCeti.sawtooth_neg`, `TauCeti.periodic_sawtooth`, `TauCeti.cast_sawtooth`: oddness,
  period-`1` invariance, and compatibility with `Rat.cast`.
* `TauCeti.dedekindSum_eq_sum_div_mul_sawtooth`,
  `TauCeti.dedekindSum_eq_sum_fract_of_isCoprime`: equivalent summation formulas for `s(d, c)`.
* `TauCeti.dedekindSum_congr`, `TauCeti.dedekindSum_neg_left`,
  `TauCeti.dedekindSum_eq_of_mul_modEq_one`: congruence mod `c`, oddness in `d`, and invariance
  under modular inversion `d * d' ≡ 1 [ZMOD c]`.
* `TauCeti.dedekindSum_add_dedekindSum`: **Dedekind's reciprocity law**
  `s(h, k) + s(k, h) = (h ^ 2 + k ^ 2 + 1) / (12 * h * k) - 1 / 4` for coprime `h, k > 0`.
* `TauCeti.dedekindSum_one_left`: `s(1, c) = (c - 1) * (c - 2) / (12 * c)` for `c > 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., §§3.3–3.5,
  Theorems 3.6 and 3.7.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, 1972,
  Ch. 1, §2.
-/

public section

namespace TauCeti

/-! ### The sawtooth function `((x))` -/

section Sawtooth

section Basic

variable {k : Type*} [Field k] [LinearOrder k] [FloorRing k]

/-- The classical sawtooth function `((x))`: equal to `0` at integers (`Int.fract x = 0`) and to
`Int.fract x - 1 / 2` elsewhere. -/
def sawtooth (x : k) : k :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

theorem sawtooth_def (x : k) :
    sawtooth x = if Int.fract x = 0 then 0 else Int.fract x - 1 / 2 :=
  (rfl)

theorem sawtooth_of_fract_eq_zero {x : k} (hx : Int.fract x = 0) : sawtooth x = 0 :=
  ite_eq_left hx

theorem sawtooth_of_fract_ne_zero {x : k} (hx : Int.fract x ≠ 0) :
    sawtooth x = Int.fract x - 1 / 2 :=
  ite_eq_right hx

theorem sawtooth_of_mem_range_intCast {x : k} (hx : x ∈ Set.range Int.cast) : sawtooth x = 0 :=
  sawtooth_of_fract_eq_zero (Int.fract_eq_zero_iff.mpr hx)

theorem sawtooth_of_notMem_range_intCast {x : k} (hx : x ∉ Set.range Int.cast) :
    sawtooth x = Int.fract x - 1 / 2 :=
  sawtooth_of_fract_ne_zero (Int.fract_ne_zero_iff.mpr hx)

/-- `sawtooth x = 0` iff `x` is an integer or a half-integer (`Int.fract x ∈ {0, 1/2}`). -/
theorem sawtooth_eq_zero_iff {x : k} :
    sawtooth x = 0 ↔ Int.fract x = 0 ∨ Int.fract x = 1 / 2 := by
  rw [sawtooth_def]
  split_ifs with hx
  · simp [hx]
  · simp [hx, sub_eq_zero]

@[simp] theorem sawtooth_zero : sawtooth (0 : k) = 0 := by simp [sawtooth]
@[simp] theorem sawtooth_one : sawtooth (1 : k) = 0 := by simp [sawtooth]
@[simp] theorem sawtooth_intCast (z : ℤ) : sawtooth (z : k) = 0 := by simp [sawtooth]
@[simp] theorem sawtooth_natCast (n : ℕ) : sawtooth (n : k) = 0 := by simp [sawtooth]

@[simp]
theorem sawtooth_ofNat (n : ℕ) [n.AtLeastTwo] : sawtooth (ofNat(n) : k) = 0 := by simp [sawtooth]

end Basic

section OrderedAdd

variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedAddMonoid k] [FloorRing k]

@[simp] theorem sawtooth_fract (x : k) : sawtooth (Int.fract x) = sawtooth x := by simp [sawtooth]
@[simp] theorem sawtooth_add_intCast (x : k) (z : ℤ) : sawtooth (x + z) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_intCast_add (z : ℤ) (x : k) : sawtooth (z + x) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_sub_intCast (x : k) (z : ℤ) : sawtooth (x - z) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_add_natCast (x : k) (n : ℕ) : sawtooth (x + n) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_natCast_add (n : ℕ) (x : k) : sawtooth (n + x) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_sub_natCast (x : k) (n : ℕ) : sawtooth (x - n) = sawtooth x := by
  simp [sawtooth]
@[simp] theorem sawtooth_add_one (x : k) : sawtooth (x + 1) = sawtooth x := by simp [sawtooth]
@[simp] theorem sawtooth_one_add (x : k) : sawtooth (1 + x) = sawtooth x := by simp [sawtooth]
@[simp] theorem sawtooth_sub_one (x : k) : sawtooth (x - 1) = sawtooth x := by simp [sawtooth]

/-- The sawtooth function has period `1`. -/
theorem periodic_sawtooth : Function.Periodic (sawtooth : k → k) 1 :=
  sawtooth_add_one

/-- The sawtooth function is odd everywhere, including at integers. -/
@[simp]
theorem sawtooth_neg (x : k) : sawtooth (-x) = -sawtooth x := by
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    simp [sawtooth, hx, hnx]
  · have hnx : Int.fract (-x) ≠ 0 := mt Int.fract_neg_eq_zero.mp hx
    rw [sawtooth_of_fract_ne_zero hnx, sawtooth_of_fract_ne_zero hx, Int.fract_neg hx]
    ring

theorem sawtooth_intCast_sub (z : ℤ) (x : k) : sawtooth (z - x) = -sawtooth x := by
  rw [sub_eq_add_neg, sawtooth_intCast_add, sawtooth_neg]

theorem sawtooth_one_sub (x : k) : sawtooth (1 - x) = -sawtooth x := by
  simpa using sawtooth_intCast_sub 1 x

end OrderedAdd

section OrderedField

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k]

@[simp]
theorem sawtooth_inv_two : sawtooth (2⁻¹ : k) = 0 := by
  have hfract : Int.fract (2⁻¹ : k) = 2⁻¹ :=
    Int.fract_eq_self.mpr ⟨by positivity, by norm_num⟩
  simp [sawtooth, hfract, one_div]

theorem sawtooth_one_div_two : sawtooth (1 / 2 : k) = 0 := by simp

/-- Every value of `sawtooth` lies strictly inside `(-1 / 2, 1 / 2)`. -/
theorem abs_sawtooth_lt_one_div_two (x : k) : |sawtooth x| < 1 / 2 := by
  rw [sawtooth_def]
  split_ifs with hx
  · norm_num
  · have hpos : 0 < Int.fract x := lt_of_le_of_ne' (Int.fract_nonneg x) hx
    have hlt : Int.fract x < 1 := Int.fract_lt_one x
    rw [abs_lt]
    constructor <;> linarith

/-- Casting from `ℚ` to a strictly ordered floor field commutes with `sawtooth`. -/
@[simp, norm_cast]
theorem cast_sawtooth (x : ℚ) : ((sawtooth x : ℚ) : k) = sawtooth (x : k) := by
  by_cases hx : Int.fract x = 0
  · have hxk : Int.fract (x : k) = 0 := by rw [← Rat.cast_fract, hx, Rat.cast_zero]
    simp [sawtooth_def, hx, hxk]
  · simp [sawtooth_def, hx, ← Rat.cast_fract]

end OrderedField

end Sawtooth

/-! ### Dedekind sums `s(d, c)` -/

/-- **The Dedekind sum** `s(d, c)` for integers `d` and `c`:
`∑ r ∈ Finset.Ioo 0 c, sawtooth (r / c) * sawtooth (d * r / c)`.
When `c ≤ 1` the interval `Finset.Ioo 0 c` is empty, so `dedekindSum d c = 0`. -/
def dedekindSum (d c : ℤ) : ℚ :=
  ∑ r ∈ Finset.Ioo 0 c, sawtooth ((r : ℚ) / c) * sawtooth ((d * r : ℚ) / c)

theorem dedekindSum_def (d c : ℤ) :
    dedekindSum d c =
      ∑ r ∈ Finset.Ioo 0 c, sawtooth ((r : ℚ) / c) * sawtooth ((d * r : ℚ) / c) :=
  (rfl)

private theorem Ioo_zero_eq_empty {c : ℤ} (hc : c ≤ 1) : Finset.Ioo 0 c = ∅ := by
  ext r
  simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
  omega

/-- `dedekindSum d c` vanishes whenever `c ≤ 1`. -/
theorem dedekindSum_of_le_one {c : ℤ} (hc : c ≤ 1) (d : ℤ) : dedekindSum d c = 0 := by
  simp [dedekindSum, Ioo_zero_eq_empty hc]

/-- `dedekindSum d c` vanishes whenever `c ≤ 0`. -/
theorem dedekindSum_of_nonpos {c : ℤ} (hc : c ≤ 0) (d : ℤ) : dedekindSum d c = 0 :=
  dedekindSum_of_le_one (by omega) d

@[simp]
theorem dedekindSum_zero_right (d : ℤ) : dedekindSum d 0 = 0 :=
  dedekindSum_of_le_one (by decide) d

@[simp]
theorem dedekindSum_one_right (d : ℤ) : dedekindSum d 1 = 0 :=
  dedekindSum_of_le_one le_rfl d

@[simp]
theorem dedekindSum_two_right (d : ℤ) : dedekindSum d 2 = 0 := by
  have hset : Finset.Ioo (0 : ℤ) 2 = {1} := by
    ext r
    simp only [Finset.mem_Ioo, Finset.mem_singleton]
    omega
  simp [dedekindSum, hset]

@[simp]
theorem dedekindSum_zero_left (c : ℤ) : dedekindSum 0 c = 0 := by simp [dedekindSum]

private theorem sum_Ioo_natCast {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℤ → M) :
    ∑ r ∈ Finset.Ioo (0 : ℤ) n, f r = ∑ r ∈ Finset.Ico 1 n, f r := by
  refine (Finset.sum_nbij' (fun r : ℕ ↦ (r : ℤ)) Int.toNat ?_ ?_ ?_ ?_ ?_).symm
  · intro r hr; simp only [Finset.mem_Ico, Finset.mem_Ioo] at hr ⊢; omega
  · intro r hr; simp only [Finset.mem_Ioo, Finset.mem_Ico] at hr ⊢; omega
  · exact fun r _ ↦ Int.toNat_natCast r
  · intro r hr; simp only [Finset.mem_Ioo] at hr; exact Int.toNat_of_nonneg (by omega)
  · exact fun _ _ ↦ rfl

/-- Express `dedekindSum d n` for `n : ℕ` as a sum over `Finset.Ico 1 n`. -/
theorem dedekindSum_natCast_right (d : ℤ) (n : ℕ) :
    dedekindSum d n =
      ∑ r ∈ Finset.Ico 1 n, sawtooth ((r : ℚ) / n) * sawtooth ((d * r : ℚ) / n) := by
  rw [dedekindSum, sum_Ioo_natCast]
  simp

/-- By reflecting `r ↦ c - r` and using the oddness and `1`-periodicity of `sawtooth`, the sum
`∑ r ∈ Finset.Ioo 0 c, sawtooth (d * r / c)` vanishes for every `d, c : ℤ` without any coprimality
assumption. -/
theorem sum_sawtooth_mul_div_Ioo (d c : ℤ) :
    ∑ r ∈ Finset.Ioo 0 c, sawtooth ((d * r : ℚ) / c) = 0 := by
  rcases le_or_gt c 1 with hc | hc
  · simp [Ioo_zero_eq_empty hc]
  · have hc0 : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hrefl : ∑ r ∈ Finset.Ioo 0 c, sawtooth ((d * r : ℚ) / c) =
        -∑ r ∈ Finset.Ioo 0 c, sawtooth ((d * r : ℚ) / c) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_nbij' (fun r ↦ c - r) (fun r ↦ c - r) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_Ioo] at hr ⊢
        omega
      · intro r hr
        simp only [Finset.mem_Ioo] at hr ⊢
        omega
      · intro r _; omega
      · intro r _; omega
      · intro r _
        have harg : (d * (c - r : ℤ) : ℚ) / c = (d : ℚ) - (d * r : ℚ) / c := by
          push_cast
          field_simp
        rw [harg, sawtooth_intCast_sub, neg_neg]
    linarith

/-- Unconditional linear-weight formula for the Dedekind sum: the `- 1 / 2` shift in the first
factor drops out because `sum_sawtooth_mul_div_Ioo` vanishes. -/
theorem dedekindSum_eq_sum_div_mul_sawtooth (d c : ℤ) :
    dedekindSum d c = ∑ r ∈ Finset.Ioo 0 c, ((r : ℚ) / c) * sawtooth ((d * r : ℚ) / c) := by
  rcases le_or_gt c 1 with hc | hc
  · simp [dedekindSum_of_le_one hc, Ioo_zero_eq_empty hc]
  · have hc' : (0 : ℚ) < c := Int.cast_pos.mpr (by omega)
    have hcongr : ∀ r ∈ Finset.Ioo 0 c,
        sawtooth ((r : ℚ) / c) * sawtooth ((d * r : ℚ) / c) =
          ((r : ℚ) / c) * sawtooth ((d * r : ℚ) / c) -
            (1 / 2) * sawtooth ((d * r : ℚ) / c) := by
      intro r hr
      simp only [Finset.mem_Ioo] at hr
      have hrpos : (0 : ℚ) < r := Int.cast_pos.mpr hr.1
      have hrlt : (r : ℚ) < c := Int.cast_lt.mpr hr.2
      have hfract : Int.fract ((r : ℚ) / c) = (r : ℚ) / c :=
        Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hc').mpr hrlt⟩
      have hne : Int.fract ((r : ℚ) / c) ≠ 0 := by
        rw [hfract]
        positivity
      rw [sawtooth_of_fract_ne_zero hne, hfract]
      ring
    rw [dedekindSum, Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sawtooth_mul_div_Ioo]
    ring

/-- When `d` and `c` are coprime, `(d * r : ℚ) / c` is never an integer for `0 < r < c`, so
`sawtooth ((d * r : ℚ) / c)` simplifies directly to `Int.fract ((d * r : ℚ) / c) - 1 / 2`. -/
theorem dedekindSum_eq_sum_fract_of_isCoprime {d c : ℤ} (hdc : IsCoprime d c) :
    dedekindSum d c =
      ∑ r ∈ Finset.Ioo 0 c, ((r : ℚ) / c) * (Int.fract ((d * r : ℚ) / c) - 1 / 2) := by
  rw [dedekindSum_eq_sum_div_mul_sawtooth]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  simp only [Finset.mem_Ioo] at hr
  have hc0 : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have hnotint : ((d * r : ℚ) / c) ∉ Set.range Int.cast := by
    rintro ⟨k, hk⟩
    have hmul : (k : ℚ) * c = d * r := by
      rw [hk, div_mul_cancel₀ _ hc0]
    have hmulZ : c * k = d * r := by
      have : k * c = d * r := by exact_mod_cast hmul
      linarith
    have hdvd : c ∣ d * r := ⟨k, hmulZ.symm⟩
    have hcr : c ∣ r := hdc.symm.dvd_of_dvd_mul_left hdvd
    exact absurd (Int.le_of_dvd hr.1 hcr) (by omega)
  rw [sawtooth_of_notMem_range_intCast hnotint]

/-- `s(d, c)` depends on `d` only modulo `c`. -/
theorem dedekindSum_congr {d₁ d₂ c : ℤ} (h : d₁ ≡ d₂ [ZMOD c]) :
    dedekindSum d₁ c = dedekindSum d₂ c := by
  rcases le_or_gt c 0 with hc | hc
  · simp [dedekindSum_of_nonpos hc]
  · obtain ⟨k, hk⟩ := h.symm.dvd
    have hc0 : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    rw [dedekindSum, dedekindSum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have harg : (d₁ * r : ℚ) / c = (d₂ * r : ℚ) / c + (k * r : ℤ) := by
      have hd₁ : d₁ = d₂ + c * k := by omega
      rw [hd₁]
      push_cast
      field_simp
    rw [harg, sawtooth_add_intCast]

@[simp]
theorem dedekindSum_add_mul_left (d k c : ℤ) :
    dedekindSum (d + k * c) c = dedekindSum d c :=
  dedekindSum_congr <| by
    rw [mul_comm k c]
    exact Int.ModEq.add_right_cancel' (c * k) (by simp [Int.ModEq])

@[simp]
theorem dedekindSum_add_self (d c : ℤ) : dedekindSum (d + c) c = dedekindSum d c := by
  simpa using dedekindSum_add_mul_left d 1 c

@[simp]
theorem dedekindSum_sub_self (d c : ℤ) : dedekindSum (d - c) c = dedekindSum d c := by
  simpa [sub_eq_add_neg] using dedekindSum_add_mul_left d (-1) c

@[simp]
theorem dedekindSum_emod (d c : ℤ) : dedekindSum (d % c) c = dedekindSum d c :=
  dedekindSum_congr (Int.mod_modEq d c)

@[simp]
theorem dedekindSum_self (c : ℤ) : dedekindSum c c = 0 := by
  have h := dedekindSum_add_self 0 c
  simpa using h

/-- `s(-d, c) = -s(d, c)`. -/
@[simp]
theorem dedekindSum_neg_left (d c : ℤ) : dedekindSum (-d) c = -dedekindSum d c := by
  rw [dedekindSum, dedekindSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hneg : ((-d : ℤ) * r : ℚ) / c = -((d * r : ℚ) / c) := by
    push_cast
    ring
  rw [hneg, sawtooth_neg, mul_neg]

/-- **Modular-inverse symmetry of Dedekind sums**: if `d * d' ≡ 1 [ZMOD c]`, then
`s(d, c) = s(d', c)` (Apostol, Theorem 3.6(c)). -/
theorem dedekindSum_eq_of_mul_modEq_one {d d' c : ℤ} (h : d * d' ≡ 1 [ZMOD c]) :
    dedekindSum d c = dedekindSum d' c := by
  rcases le_or_gt c 1 with hc | hc
  · simp [dedekindSum_of_le_one hc]
  · let n : ℕ := c.toNat
    have hn : (n : ℤ) = c := Int.toNat_of_nonneg (by omega)
    have hpos : 0 ≤ d % c := Int.emod_nonneg d (by omega)
    let m : ℕ := (d % c).toNat
    have hm : (m : ℤ) = d % c := Int.toNat_of_nonneg hpos
    have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := by
      have hmmod : (m : ℤ) * d' ≡ 1 [ZMOD n] := by
        rw [hm, hn]
        exact ((Int.mod_modEq d c).mul_right d').trans h
      obtain ⟨k, hk⟩ := hmmod.symm.dvd
      exact ⟨d', -k, by linarith⟩
    have hmn : m.Coprime n := by
      simpa [Int.isCoprime_iff_nat_coprime] using hcopZ
    rw [← dedekindSum_emod d c, ← hm, ← hn, dedekindSum_natCast_right, dedekindSum_natCast_right]
    have hterm : ∀ x ∈ Finset.Ico 1 n,
        sawtooth ((x : ℚ) / n) * sawtooth (((m : ℤ) * x : ℚ) / n) =
          sawtooth (((m * x % n : ℕ) : ℚ) / n) *
            sawtooth ((d' * (m * x % n : ℕ) : ℚ) / n) := by
      intro x _
      have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h1 : (((m : ℤ) * x : ℚ) / n) =
          ((m * x % n : ℕ) : ℚ) / n + ((m * x / n : ℕ) : ℤ) := by
        have hdiv := Nat.mod_add_div (m * x) n
        have hdivQ : ((m * x % n : ℕ) : ℚ) + (n : ℚ) * (m * x / n : ℕ) = (m : ℚ) * x := by
          exact_mod_cast hdiv
        rw [Int.cast_natCast, Int.cast_natCast]
        field_simp
        linarith
      have hmod : d' * ((m * x % n : ℕ) : ℤ) ≡ x [ZMOD n] := by
        have hs : ((m * x % n : ℕ) : ℤ) ≡ (m : ℤ) * x [ZMOD n] := by
          exact_mod_cast Nat.mod_modEq (m * x) n
        have hmd : (m : ℤ) ≡ d [ZMOD n] := by
          rw [hm, hn]
          exact Int.mod_modEq d c
        calc
          d' * ((m * x % n : ℕ) : ℤ) ≡ d' * ((m : ℤ) * x) [ZMOD n] := hs.mul_left d'
          _ ≡ d' * (d * x) [ZMOD n] := (hmd.mul_right x).mul_left d'
          _ = (d * d') * x := by ring
          _ ≡ 1 * x [ZMOD n] := by
            rw [hn]
            exact h.mul_right x
          _ = x := one_mul _
      obtain ⟨k, hk⟩ := hmod.symm.dvd
      have h2 : (d' * (m * x % n : ℕ) : ℚ) / n = (x : ℚ) / n + (k : ℤ) := by
        have hd' : d' * ((m * x % n : ℕ) : ℤ) = (x : ℤ) + (n : ℤ) * k := by omega
        have hd'Q : (d' : ℚ) * (m * x % n : ℕ) = (x : ℚ) + (n : ℚ) * k := by
          rw [← Int.cast_natCast (m * x % n), ← Int.cast_mul, hd']
          push_cast
          ring
        field_simp
        linarith
      rw [h1, sawtooth_add_intCast, h2, sawtooth_add_intCast, mul_comm]
    rw [Finset.sum_congr rfl hterm]
    exact hmn.sum_Ico_mul_mod fun s ↦
      sawtooth ((s : ℚ) / n) * sawtooth ((d' * (s : ℕ) : ℚ) / n)

private theorem sum_Ico_one_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M)
    (h0 : f 0 = 0) : ∑ x ∈ Finset.Ico 1 n, f x = ∑ x ∈ Finset.range n, f x := by
  rcases n with _ | n
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), h0, zero_add]

private theorem sum_Ico_id_rat (n : ℕ) :
    ∑ x ∈ Finset.Ico 1 n, (x : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  have hpow := sum_range_pow n 1
  norm_num [Finset.sum_range_succ] at hpow
  rw [sum_Ico_one_eq_sum_range n _ (by simp), hpow]
  ring

private theorem sum_Ico_sq_rat (n : ℕ) :
    ∑ x ∈ Finset.Ico 1 n, (x : ℚ) ^ 2 =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  have hpow := sum_range_pow n 2
  norm_num [Finset.sum_range_succ] at hpow
  rw [sum_Ico_one_eq_sum_range n _ (by simp), hpow]
  ring

private theorem dedekindSum_natCast_of_coprime {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) :
    dedekindSum m n =
      ∑ x ∈ Finset.Ico 1 n,
        ((x : ℚ) / n) * (((m : ℚ) * x / n - 1 / 2) - (m * x / n : ℕ)) := by
  have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hmn
  rw [dedekindSum_eq_sum_fract_of_isCoprime hcopZ, sum_Ioo_natCast]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hdivQ : ((m * x % n : ℕ) : ℚ) + (n : ℚ) * (m * x / n : ℕ) = (m : ℚ) * x := by
    exact_mod_cast Nat.mod_add_div (m * x) n
  have hfract : Int.fract (((m : ℤ) * (x : ℤ) : ℚ) / (n : ℤ)) =
      (m : ℚ) * x / n - (m * x / n : ℕ) := by
    have hf : Int.fract (((m * x : ℕ) : ℚ) / n) = ((m * x % n : ℕ) : ℚ) / n :=
      Int.fract_div_natCast_eq_div_natCast_mod
    push_cast at hf ⊢
    rw [hf]
    field_simp
    linarith
  rw [hfract]
  push_cast
  ring

/-- **Dedekind's reciprocity law** (Apostol, Theorem 3.7; Rademacher–Grosswald, Ch. 1, §2):
for coprime positive integers `h` and `k`,
$$s(h, k) + s(k, h) = \frac{h^2 + k^2 + 1}{12 h k} - \frac{1}{4}.$$ -/
theorem dedekindSum_add_dedekindSum {h k : ℤ} (hh : 0 < h) (hk : 0 < k) (hhk : IsCoprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) ^ 2 + (k : ℚ) ^ 2 + 1) / (12 * h * k) - 1 / 4 := by
  let m : ℕ := h.toNat
  let n : ℕ := k.toNat
  have hmZ : (m : ℤ) = h := Int.toNat_of_nonneg hh.le
  have hnZ : (n : ℤ) = k := Int.toNat_of_nonneg hk.le
  have hm : 0 < m := by omega
  have hn : 0 < n := by omega
  have hmn : m.Coprime n := by
    rw [← hmZ, ← hnZ, Int.isCoprime_iff_nat_coprime] at hhk
    simpa using hhk
  rw [← hmZ, ← hnZ, dedekindSum_natCast_of_coprime hn hmn,
    dedekindSum_natCast_of_coprime hm hmn.symm]
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Step 1: Gauss floor-sum reciprocity in `ℚ`.
  have hgauss :
      ∑ x ∈ Finset.Ico 1 n, ((m * x / n : ℕ) : ℚ) +
        ∑ y ∈ Finset.Ico 1 m, ((n * y / m : ℕ) : ℚ) =
      ((n : ℚ) - 1) * ((m : ℚ) - 1) := by
    have hnat := congrArg (Nat.cast : ℕ → ℚ) hmn.sum_mul_div_add_sum_mul_div
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_sub hn, Nat.cast_sub hm, Nat.cast_one] at hnat
    exact hnat
  -- Step 2: Weighted square floor-sum reciprocity in `ℚ`.
  have hrad :
      ∑ x ∈ Finset.Ico 1 n, ((m * x / n : ℕ) : ℚ) ^ 2 +
        2 * ∑ y ∈ Finset.Ico 1 m, (y : ℚ) * (n * y / m : ℕ) -
        ∑ y ∈ Finset.Ico 1 m, ((n * y / m : ℕ) : ℚ) =
      ((n : ℚ) - 1) * ((m : ℚ) - 1) ^ 2 := by
    have hnat := congrArg (Nat.cast : ℕ → ℚ) hmn.sum_sq_mul_div_add_sum_odd_mul_div
    have hodd : ∀ y ∈ Finset.Ico 1 m,
        (((2 * y - 1) * (n * y / m) : ℕ) : ℚ) =
          2 * ((y : ℚ) * (n * y / m : ℕ)) - (n * y / m : ℕ) := by
      intro y hy
      have hy1 : 1 ≤ 2 * y := by have := (Finset.mem_Ico.mp hy).1; omega
      rw [Nat.cast_mul, Nat.cast_sub hy1]
      push_cast
      ring
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum, Finset.sum_congr rfl hodd,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hn, Nat.cast_sub hm, Nat.cast_one] at hnat
    simp_rw [Nat.cast_pow] at hnat
    linarith [hnat]
  -- Step 3: Permute `x ↦ m * x % n` on `Ico 1 n` inside `r ↦ r * (r - n)`.
  have hperm :
      ∑ x ∈ Finset.Ico 1 n,
          ((m : ℚ) ^ 2 * (x : ℚ) ^ 2 - ((m : ℚ) * n) * (x : ℚ) -
            (2 * (m : ℚ) * n) * ((x : ℚ) * (m * x / n : ℕ)) +
            (n : ℚ) ^ 2 * (m * x / n : ℕ) + (n : ℚ) ^ 2 * ((m * x / n : ℕ) : ℚ) ^ 2) =
        ∑ r ∈ Finset.Ico 1 n, ((r : ℚ) ^ 2 - (n : ℚ) * (r : ℚ)) := by
    trans ∑ x ∈ Finset.Ico 1 n,
        ((m * x % n : ℕ) : ℚ) * (((m * x % n : ℕ) : ℚ) - n)
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hdivQ : ((m * x % n : ℕ) : ℚ) = (m : ℚ) * x - (n : ℚ) * (m * x / n : ℕ) := by
        have := congrArg (Nat.cast : ℕ → ℚ) (Nat.mod_add_div (m * x) n)
        push_cast at this
        linarith
      rw [hdivQ]
      ring
    · rw [hmn.sum_Ico_mul_mod fun r ↦ (r : ℚ) * ((r : ℚ) - n)]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hperm
  have hexp (a b : ℕ) :
      ∑ x ∈ Finset.Ico 1 b,
          ((x : ℚ) / b) * (((a : ℚ) * x / b - 1 / 2) - (a * x / b : ℕ)) =
        ((a : ℚ) / b ^ 2) * ∑ x ∈ Finset.Ico 1 b, (x : ℚ) ^ 2 -
          (1 / (2 * (b : ℚ))) * ∑ x ∈ Finset.Ico 1 b, (x : ℚ) -
          (1 / (b : ℚ)) * ∑ x ∈ Finset.Ico 1 b, (x : ℚ) * (a * x / b : ℕ) := by
    have hterm : ∀ x ∈ Finset.Ico 1 b,
        ((x : ℚ) / b) * (((a : ℚ) * x / b - 1 / 2) - (a * x / b : ℕ)) =
          ((a : ℚ) / b ^ 2) * (x : ℚ) ^ 2 - (1 / (2 * (b : ℚ))) * x -
            (1 / (b : ℚ)) * ((x : ℚ) * (a * x / b : ℕ)) := fun _ _ ↦ by ring
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp m n, hexp n m, sum_Ico_id_rat n, sum_Ico_sq_rat n, sum_Ico_id_rat m, sum_Ico_sq_rat m]
  rw [sum_Ico_id_rat n, sum_Ico_sq_rat n] at hperm
  set Sx := ∑ x ∈ Finset.Ico 1 n, (x : ℚ) * (m * x / n : ℕ)
  set Sy := ∑ y ∈ Finset.Ico 1 m, (y : ℚ) * (n * y / m : ℕ)
  have hcomb :
      2 * (m : ℚ) * n * Sx + 2 * (n : ℚ) ^ 2 * Sy =
        ((m : ℚ) ^ 2 - 1) * ((n : ℚ) * (n - 1) * (2 * n - 1) / 6) -
          ((m : ℚ) - 1) * n * ((n : ℚ) * (n - 1) / 2) +
          (n : ℚ) ^ 2 * ((n - 1) * (m - 1)) + (n : ℚ) ^ 2 * ((n - 1) * (m - 1) ^ 2) := by
    linear_combination -hperm + (n : ℚ) ^ 2 * hrad + (n : ℚ) ^ 2 * hgauss
  apply mul_left_cancel₀ (by positivity : 2 * (m : ℚ) * n ^ 2 ≠ 0)
  have hSx : 2 * (m : ℚ) * n ^ 2 * ((1 / (n : ℚ)) * Sx) = 2 * (m : ℚ) * n * Sx := by field_simp
  have hSy : 2 * (m : ℚ) * n ^ 2 * ((1 / (m : ℚ)) * Sy) = 2 * (n : ℚ) ^ 2 * Sy := by field_simp
  have hpoly :
      2 * (m : ℚ) * n ^ 2 *
          (((m : ℚ) / n ^ 2) * ((n : ℚ) * (n - 1) * (2 * n - 1) / 6) -
            (1 / (2 * (n : ℚ))) * ((n : ℚ) * (n - 1) / 2) +
          (((n : ℚ) / m ^ 2) * ((m : ℚ) * (m - 1) * (2 * m - 1) / 6) -
            (1 / (2 * (m : ℚ))) * ((m : ℚ) * (m - 1) / 2))) -
        (((m : ℚ) ^ 2 - 1) * ((n : ℚ) * (n - 1) * (2 * n - 1) / 6) -
          ((m : ℚ) - 1) * n * ((n : ℚ) * (n - 1) / 2) +
          (n : ℚ) ^ 2 * ((n - 1) * (m - 1)) + (n : ℚ) ^ 2 * ((n - 1) * (m - 1) ^ 2)) =
      2 * (m : ℚ) * n ^ 2 *
        ((((m : ℤ) : ℚ) ^ 2 + ((n : ℤ) : ℚ) ^ 2 + 1) / (12 * ((m : ℤ) : ℚ) * ((n : ℤ) : ℚ)) -
          1 / 4) := by
    push_cast
    field_simp
    ring
  linarith [hcomb, hSx, hSy, hpoly]

/-- Closed form for `s(1, c)` when `c > 0`: `s(1, c) = (c - 1) * (c - 2) / (12 * c)`. -/
theorem dedekindSum_one_left {c : ℤ} (hc : 0 < c) :
    dedekindSum 1 c = ((c : ℚ) - 1) * ((c : ℚ) - 2) / (12 * c) := by
  have hrec := dedekindSum_add_dedekindSum zero_lt_one hc isCoprime_one_left
  rw [dedekindSum_one_right, add_zero] at hrec
  have hc0 : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  rw [hrec]
  push_cast
  field_simp
  ring

end TauCeti
