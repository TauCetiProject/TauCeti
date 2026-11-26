/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The flow programme of height-two Lubin–Tate letters

Fix a cycle length `n` and a natural number `p`, in practice a prime. Write
`γ_LT(p) = p / (p² - 1)` and `ρ_LT(p) = 1 / (p² - 1)` for the Taylor rates of the Lubin–Tate
formal group of height two. For a demand vector `D : ZMod n → ℝ`, a *flow* is a family
`x s i ≥ 0`, indexed by the letters `s : ZMod n` and the odd `i < n`, such that
`∑ᵢ (pⁱ x s i + x (s - i) i) ≤ D s` for every letter `s`; the entry `x s i` counts bi-power
monomials `y_s ^ (pⁱ) y_(s+i)`. The *flow programme* `𝔉_p(D)` is `γ_LT(p) ∑ₛ D s` minus the
largest total `∑ₛ ∑ᵢ x s i` of a flow.

## Main results

* `TauCeti.flowProgramme`: the flow programme `𝔉_p(D)`.
* `TauCeti.flowProgramme_le`: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s`, with no hypotheses.
* `TauCeti.le_flowProgramme`: `ρ_LT(p) ∑ₛ D s ≤ 𝔉_p(D)` for `D ≥ 0` and `p ≠ 1`: summing the
  constraints bounds the total of a flow by `∑ₛ D s / (p + 1)`.
* `TauCeti.flowProgramme_eq_of_max_le_mul_min`: `𝔉_p(D) = ρ_LT(p) ∑ₛ D s` when `p > 1`, `n ≥ 2`
  and `D s ≤ p D t` for all letters `s`, `t`; the flow on the shift `i = 1` solving
  `p x s + x (s - 1) = D s` is nonnegative and attains the bound.
-/

@[expose] public section

open Finset

namespace TauCeti

/-- The *flow programme* `𝔉_p(D)` on the cycle `ZMod n`: `γ_LT(p) ∑ₛ D s`, with
`γ_LT(p) = p / (p² - 1)`, minus the largest total `∑ₛ ∑ᵢ x s i` of a flow `x ≥ 0`, indexed by the
letters `s` and the odd `i < n`, with `∑ᵢ (pⁱ x s i + x (s - i) i) ≤ D s` for every `s`. -/
noncomputable def flowProgramme (p n : ℕ) [NeZero n] (D : ZMod n → ℝ) : ℝ :=
  (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s -
    sSup {t : ℝ | ∃ x : ZMod n → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧
      (∀ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) ≤ D s) ∧
      t = ∑ s, ∑ i ∈ (range n).filter Odd, x s i}

variable {p n : ℕ} [NeZero n] {D : ZMod n → ℝ}

/-- Summing the constraints of a flow bounds its total by `∑ₛ D s / (p + 1)`. -/
private theorem sum_flow_le {x : ZMod n → ℕ → ℝ} (hx0 : ∀ s i, 0 ≤ x s i)
    (hx : ∀ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) ≤ D s) :
    ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤ (∑ s, D s) / (p + 1) := by
  have hpi : ∀ i ∈ (range n).filter Odd, (p : ℝ) ≤ (p : ℝ) ^ i := fun i hi ↦ by
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    exact_mod_cast Nat.le_self_pow hi0 p
  have hshift : ∀ i : ℕ, ∑ s, x (s - i) i = ∑ s, x s i := fun i ↦
    Fintype.sum_equiv (Equiv.subRight (i : ZMod n)) _ _ fun _ ↦ rfl
  rw [le_div_iff₀ (by positivity), mul_comm, Finset.mul_sum]
  calc ∑ s, ((p : ℝ) + 1) * ∑ i ∈ (range n).filter Odd, x s i
      = ∑ i ∈ (range n).filter Odd, ∑ s, ((p : ℝ) + 1) * x s i := by
        simp_rw [Finset.mul_sum]; exact sum_comm
    _ ≤ ∑ i ∈ (range n).filter Odd, ∑ s, ((p : ℝ) ^ i * x s i + x (s - i) i) :=
        sum_le_sum fun i hi ↦ by
          rw [sum_add_distrib, hshift i, ← sum_add_distrib]
          exact sum_le_sum fun s _ ↦ by nlinarith [hx0 s i, hpi i hi]
    _ = ∑ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) := sum_comm
    _ ≤ ∑ s, D s := sum_le_sum fun s _ ↦ hx s

/-- `γ_LT(p) - ρ_LT(p) = 1 / (p + 1)` for `p ≠ 1`. -/
private theorem div_sub_one_div_sq_sub_one (hp : p ≠ 1) :
    (p : ℝ) / ((p : ℝ) ^ 2 - 1) - 1 / ((p : ℝ) ^ 2 - 1) = 1 / (p + 1) := by
  have h1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp)
  rw [← sub_div, show (p : ℝ) ^ 2 - 1 = (p - 1) * (p + 1) by ring, ← div_div, div_self h1]

/-- The upper bound of the flow programme: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s`, as the zero flow is
admissible whenever any flow is. -/
theorem flowProgramme_le (p n : ℕ) [NeZero n] (D : ZMod n → ℝ) :
    flowProgramme p n D ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s := by
  refine sub_le_self _ (Real.sSup_nonneg ?_)
  rintro _ ⟨x, hx0, -, rfl⟩
  exact sum_nonneg fun s _ ↦ sum_nonneg fun i _ ↦ hx0 s i

/-- The lower bound of the flow programme: `ρ_LT(p) ∑ₛ D s ≤ 𝔉_p(D)` for a nonnegative demand
`D`, with `ρ_LT(p) = 1 / (p² - 1)`, since a flow has total at most `∑ₛ D s / (p + 1)`. -/
theorem le_flowProgramme (hp : p ≠ 1) (hD : ∀ s, 0 ≤ D s) :
    1 / ((p : ℝ) ^ 2 - 1) * ∑ s, D s ≤ flowProgramme p n D := by
  rw [flowProgramme, le_sub_comm, ← sub_mul, div_sub_one_div_sq_sub_one hp, one_div_mul_eq_div]
  refine csSup_le ⟨0, fun _ _ ↦ 0, fun _ _ ↦ le_rfl, fun s ↦ ?_, by simp⟩ ?_
  · simpa using hD s
  · rintro _ ⟨x, hx0, hx, rfl⟩
    exact sum_flow_le hx0 hx

/-- A finite alternating sum of a nonnegative antitone sequence lies between `0` and its first
term. -/
private theorem sum_range_neg_one_pow_mul_mem_Icc (n : ℕ) :
    ∀ a : ℕ → ℝ, Antitone a → (∀ k, 0 ≤ a k) →
      0 ≤ ∑ k ∈ range n, (-1) ^ k * a k ∧ ∑ k ∈ range n, (-1) ^ k * a k ≤ a 0 := by
  induction n with
  | zero => intro a _ ha0; simpa using ha0 0
  | succ n ih =>
    intro a ha ha0
    obtain ⟨h1, h2⟩ := ih (fun k ↦ a (k + 1)) (fun i j hij ↦ ha (by omega)) fun k ↦ ha0 _
    rw [sum_range_succ']
    simp only [pow_succ, mul_neg_one, neg_mul, sum_neg_distrib, pow_zero, one_mul]
    exact ⟨by linarith [ha (Nat.zero_le 1)], by linarith⟩

/-- For `p > 1`, `n ≥ 2` and a demand with `D s ≤ p D t` for all `s`, `t`, the equations
`p y s + y (s - 1) = D s` have a nonnegative solution on `ZMod n`: the alternating sum
`y s = ∑_{k < n} (-1/p)ᵏ D (s - k) / (p (1 - (-1/p)ⁿ))`. -/
private theorem exists_nonneg_shift_solution (hp : 1 < p) (hD : ∀ s t, D s ≤ p * D t) :
    ∃ y : ZMod n → ℝ, (∀ s, 0 ≤ y s) ∧ ∀ s, (p : ℝ) * y s + y (s - 1) = D s := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp
  have hD0 : ∀ s, 0 ≤ D s := fun s ↦ by nlinarith [hD s s]
  set r : ℝ := -1 / p with hr
  have hrn : r ^ n < 1 := by
    refine (le_abs_self _).trans_lt ?_
    rw [abs_pow, hr, abs_div, abs_neg, abs_one, Nat.abs_cast]
    exact pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hq) (NeZero.ne n)
  set A : ZMod n → ℝ := fun s ↦ ∑ k ∈ range n, r ^ k * D (s - k)
  have hA0 : ∀ s, 0 ≤ A s := fun s ↦ by
    have hanti : Antitone fun k : ℕ ↦ D (s - k) / (p : ℝ) ^ k := by
      refine antitone_nat_of_succ_le fun k ↦ ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
      have h := hD (s - (k + 1 : ℕ)) (s - k)
      have hpk : (0 : ℝ) ≤ (p : ℝ) ^ k := by positivity
      nlinarith
    convert (sum_range_neg_one_pow_mul_mem_Icc n _ hanti fun k ↦ div_nonneg (hD0 _)
      (by positivity)).1 using 2 with k
    rw [hr, div_pow, neg_one_pow_eq_pow_mod_two]
    ring_nf
  have key : ∀ s, (p : ℝ) * A s + A (s - 1) = p * (1 - r ^ n) * D s := fun s ↦ by
    set f : ℕ → ℝ := fun k ↦ r ^ k * D (s - k)
    have h1 : A (s - 1) = -p * ∑ k ∈ range n, f (k + 1) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [f, Nat.cast_succ, sub_add_eq_sub_sub_swap, pow_succ, hr]
      field_simp
    calc (p : ℝ) * A s + A (s - 1) = p * ∑ k ∈ range n, (f k - f (k + 1)) := by
          rw [h1, sum_sub_distrib]; ring
      _ = p * (1 - r ^ n) * D s := by
          rw [sum_range_sub']; simp [f]; ring
  refine ⟨fun s ↦ A s / (p * (1 - r ^ n)), fun s ↦ div_nonneg (hA0 s)
    (mul_nonneg (by positivity) (by linarith)), fun s ↦ ?_⟩
  dsimp only
  have hc : (p : ℝ) * (1 - r ^ n) ≠ 0 := mul_ne_zero (by positivity) (by linarith)
  rw [mul_div_assoc', ← add_div, div_eq_iff hc]
  linear_combination key s

/-- The flow programme of a nearly constant demand: for `p > 1`, `n ≥ 2` and `D s ≤ p D t` for all
letters `s`, `t`, `𝔉_p(D) = ρ_LT(p) ∑ₛ D s` with `ρ_LT(p) = 1 / (p² - 1)`, attained by the flow on
the shift `i = 1` solving `p x s + x (s - 1) = D s`. -/
theorem flowProgramme_eq_of_max_le_mul_min (hp : 1 < p) (hn : 1 < n)
    (hD : ∀ s t, D s ≤ p * D t) :
    flowProgramme p n D = 1 / ((p : ℝ) ^ 2 - 1) * ∑ s, D s := by
  have hD0 : ∀ s, 0 ≤ D s := fun s ↦ by
    nlinarith [hD s s, show (1 : ℝ) < p by exact_mod_cast hp]
  refine le_antisymm ?_ (le_flowProgramme hp.ne' hD0)
  obtain ⟨y, hy0, hy⟩ := exists_nonneg_shift_solution hp hD
  have hsum : ∑ s, y s = (∑ s, D s) / (p + 1) := by
    rw [eq_div_iff (by positivity), ← sum_congr rfl fun s _ ↦ hy s, sum_add_distrib,
      ← Finset.mul_sum, Fintype.sum_equiv (Equiv.subRight 1) (fun s ↦ y (s - 1)) y fun _ ↦ rfl]
    ring
  have h1 : 1 ∈ (range n).filter Odd := mem_filter.mpr ⟨mem_range.mpr hn, odd_one⟩
  have hx : ∀ (g : ℕ → ℝ → ℝ → ℝ), (∀ i, g i 0 0 = 0) → ∀ s : ZMod n,
      ∑ i ∈ (range n).filter Odd, g i (if i = 1 then y s else 0)
        (if i = 1 then y (s - i) else 0) = g 1 (y s) (y (s - 1)) := fun g hg s ↦ by
    rw [sum_eq_single_of_mem 1 h1 fun i _ hi ↦ by simp [hi, hg]]
    simp
  rw [flowProgramme, sub_le_comm, ← sub_mul, div_sub_one_div_sq_sub_one hp.ne',
    one_div_mul_eq_div, ← hsum]
  refine le_csSup ⟨(∑ s, D s) / (p + 1), ?_⟩
    ⟨fun s i ↦ if i = 1 then y s else 0, fun s i ↦ ?_, fun s ↦ ?_, ?_⟩
  · rintro _ ⟨x, hx0, hx, rfl⟩
    exact sum_flow_le hx0 hx
  · dsimp only
    split_ifs <;> simp [hy0]
  · refine (hx (fun i a b ↦ (p : ℝ) ^ i * a + b) (by simp) s).trans_le ?_
    simp [hy s]
  · simpa using (sum_congr rfl fun s _ ↦ hx (fun _ a _ ↦ a) (fun _ ↦ rfl) s).symm

end TauCeti
