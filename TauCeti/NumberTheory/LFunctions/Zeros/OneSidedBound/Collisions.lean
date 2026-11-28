/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Collisions among long rows of a theta lift

A collision occurs when both a place and its partner at an active prime-power exponent carry
long rows. Outside the exceptional primes, either the budget allows the full geometric series,
or the order of the signed prime label forces every collision into its tail.

The collision sum and loss estimate are those of `New.Data.collisionSum` and
`New.Data.mul_collisionSum_le_loss` in `New/UpperBound/Size/ShortColumns.lean` and
`New/UpperBound/Divisibility/JetExponent.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src).
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- Sum the inverse prime powers, scaled by the long-row length `a`, for which a place in `A`
has its partner again in `A`. The exponent is positive and is odd at inert primes; every
positive exponent is allowed at the ramified prime. To exclude a set of places from collisions,
take `A` to be the set of long-row places after deleting that set. -/
noncomputable def collisionSum {ι : Type*} (d : ℕ) [Fact d.Prime] (p : ℕ)
    [DecidableEq ι] (A : Finset ι)
    (partner : ℕ → ι → ι) (a : ℝ) : ℝ :=
  ∑ τ ∈ A, ∑' e : ℕ,
    if 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e) ∧ partner e τ ∈ A then
      a / (p : ℝ) ^ e
    else 0

/-- The defining formula for the unweighted collision sum (no factor of `1/2` at `p = d`). -/
theorem collisionSum_def {ι : Type*} (d : ℕ) [Fact d.Prime] (p : ℕ)
    [DecidableEq ι] (A : Finset ι)
    (partner : ℕ → ι → ι) (a : ℝ) :
    collisionSum d p A partner a = ∑ τ ∈ A, ∑' e : ℕ,
      if 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e) ∧ partner e τ ∈ A then
        a / (p : ℝ) ^ e
      else 0 := (rfl)

/-- An empty set of long-row places has no collisions. -/
@[simp] theorem collisionSum_empty {ι : Type*} (d : ℕ) [Fact d.Prime] (p : ℕ) [DecidableEq ι]
    (partner : ℕ → ι → ι) (a : ℝ) : collisionSum d p ∅ partner a = 0 := by
  simp [collisionSum_def]

/-- A zero long-row length gives a zero collision sum. -/
@[simp] theorem collisionSum_zero {ι : Type*} (d : ℕ) [Fact d.Prime] (p : ℕ) [DecidableEq ι]
    (A : Finset ι) (partner : ℕ → ι → ι) : collisionSum d p A partner 0 = 0 := by
  simp [collisionSum_def]

/-- The indices `0` and `1` have no active exponents. -/
theorem collisionSum_eq_zero_of_le_one {ι : Type*} {d p : ℕ} [Fact d.Prime] [DecidableEq ι]
    (A : Finset ι) (partner : ℕ → ι → ι) (a : ℝ) (hp : p ≤ 1) :
    collisionSum d p A partner a = 0 := by
  have hd : d.Prime := Fact.out
  interval_cases p <;>
    simp [collisionSum_def, hd.ne_zero.symm, hd.ne_one.symm,
      legendreSym.at_zero, legendreSym.at_one]

/-- If every collision exponent is at least `o`, the geometric tail starting at `o`
bounds the collision sum. -/
theorem collisionSum_le_of_le_exponent {ι : Type*} {d p o : ℕ} [Fact d.Prime] [DecidableEq ι]
    {A : Finset ι} {partner : ℕ → ι → ι} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ τ ∈ A, ∀ e : ℕ, 0 < e → (p = d ∨ legendreSym d p = -1 ∧ Odd e) →
      partner e τ ∈ A → o ≤ e) :
    collisionSum d p A partner a ≤ 2 * #A * a / (p : ℝ) ^ o := by
  by_cases hsmall : p ≤ 1
  · rw [collisionSum_eq_zero_of_le_one A partner a hsmall]
    positivity
  have hp : 1 < p := Nat.lt_of_not_ge hsmall
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have hq : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hp₀ (by norm_num)]
    simpa using hp₂
  have hq₁ : (p : ℝ)⁻¹ < 1 := by linarith
  have hg := (summable_geometric_of_lt_one (by positivity) hq₁).mul_left a
  have hcard : (∑ _τ ∈ A, 2 * a / (p : ℝ) ^ o) = 2 * (#A : ℝ) * a / (p : ℝ) ^ o := by
    rw [sum_const, nsmul_eq_mul]
    ring
  rw [collisionSum_def, ← hcard]
  refine sum_le_sum fun τ hτ ↦ ?_
  let f (e : ℕ) := if 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e) ∧ partner e τ ∈ A then
    a / (p : ℝ) ^ e else 0
  have hf (e : ℕ) : 0 ≤ f e ∧ f e ≤ a * ((p : ℝ)⁻¹) ^ e := by
    simp only [f, inv_pow, ← div_eq_mul_inv]
    split
    · exact ⟨by positivity, le_rfl⟩
    · exact ⟨le_rfl, by positivity⟩
  have hs := hg.of_nonneg_of_le (fun e ↦ (hf e).1) (fun e ↦ (hf e).2)
  have hz : ∑ e ∈ range o, f e = 0 := by
    refine sum_eq_zero fun e he ↦ ite_eq_right fun hc ↦ ?_
    exact (Nat.not_le_of_lt (mem_range.mp he)) (h τ hτ e hc.1 hc.2.1 hc.2.2)
  rw [← hs.sum_add_tsum_nat_add o, hz, zero_add]
  calc
    ∑' e : ℕ, f (e + o) ≤ ∑' e : ℕ, (a / (p : ℝ) ^ o) * ((p : ℝ)⁻¹) ^ e := by
      refine ((summable_nat_add_iff o).2 hs).tsum_le_tsum (fun e ↦ ?_)
        ((summable_geometric_of_lt_one (by positivity) hq₁).mul_left _)
      simpa only [pow_add, inv_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using (hf (e + o)).2
    _ = (a / (p : ℝ) ^ o) * (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq₁]
    _ ≤ _ := by
      rw [mul_div_assoc, mul_comm (2 : ℝ)]
      gcongr
      rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹)]
      linarith

/-- For a nonexceptional prime the total collision cost of `m` lifts is at most
`2 * |A| * a / p`, with the extra factor of `m` only in the two amplified classes modulo `m`.
The residue condition says that a partner returning to the identity class satisfies
`-p^e = 1` modulo the base level. The nonexceptional condition says that an inert prime with
odd signed order at most `clog p m` must be in one of the two amplified classes. In
particular, if `2 * |A| ≤ f * (log b)^2`, the bound fits the loss with numerator
`f * a * (log b)^2`. -/
theorem Parameters.mul_collisionSum_le_of_nonexceptional (P : Parameters)
    {ι : Type*} [DecidableEq ι] {p m : ℕ} {A : Finset ι} {partner : ℕ → ι → ι} {a : ℝ}
    (ha : 0 ≤ a)
    (hclass : ∀ τ ∈ A, ∀ e > 0, partner e τ ∈ A → (p : ZMod P.q₀) ^ e = -1)
    (hordinary : legendreSym P.d p = -1 → Odd (orderOf (-(p : ZMod P.q₀))) →
      orderOf (-(p : ZMod P.q₀)) ≤ Nat.clog p m →
        (p : ZMod m) = 1 ∨ (p : ZMod m) = -1) :
    m * collisionSum P.d p A partner a ≤
      (if (p : ZMod m) = 1 ∨ (p : ZMod m) = -1 then (m : ℝ) else 1) *
        (2 * #A * a / p) := by
  by_cases hsmall : p ≤ 1
  · rw [collisionSum_eq_zero_of_le_one A partner a hsmall, mul_zero]
    split <;> positivity
  have hp : 1 < p := Nat.lt_of_not_ge hsmall
  split_ifs with hamp
  · have h := collisionSum_le_of_le_exponent (p := p) (o := 1) (A := A) (partner := partner)
      (d := P.d) ha (fun _ _ _ he _ _ ↦ he)
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_one] using h) (Nat.cast_nonneg m)
  have htail : collisionSum P.d p A partner a ≤
      2 * #A * a / (p : ℝ) ^ (Nat.clog p m + 1) := by
    refine collisionSum_le_of_le_exponent ha fun τ hτ e he hactive hmem ↦ ?_
    have hpow := hclass τ hτ e he hmem
    rcases hactive with rfl | ⟨hinert, hodd⟩
    · exact (P.d_pow_ne_neg_one e hpow).elim
    have hsign : (-(p : ZMod P.q₀)) ^ e = 1 := by rw [hodd.neg_pow, hpow, neg_neg]
    have hord := orderOf_dvd_of_pow_eq_one hsign
    by_contra! hle
    exact hamp (hordinary hinert (hodd.of_dvd_nat hord)
      ((Nat.le_of_dvd he hord).trans (by omega)))
  have hm : (m : ℝ) ≤ (p : ℝ) ^ Nat.clog p m := by exact_mod_cast Nat.le_pow_clog hp m
  rw [one_mul]
  calc
    _ ≤ (m : ℝ) * (2 * #A * a / (p : ℝ) ^ (Nat.clog p m + 1)) := by gcongr
    _ ≤ (p : ℝ) ^ Nat.clog p m * (2 * #A * a / (p : ℝ) ^ (Nat.clog p m + 1)) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp

end TauCeti.OneSidedBound
