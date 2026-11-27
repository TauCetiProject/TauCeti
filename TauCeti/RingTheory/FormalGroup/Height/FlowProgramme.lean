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
import TauCeti.Algebra.Order.BigOperators.Sum.Alternating

/-!
# The flow programme of height-two Lubin–Tate letters

Fix a cycle length `n` and a natural number `p`, in practice a prime. Write
`γ_LT(p) = p / (p² - 1)` and `ρ_LT(p) = 1 / (p² - 1)` for the Taylor rates of the Lubin–Tate
formal group of height two. For a demand vector `D : ZMod n → ℝ`, a *flow* is a family
`x s i ≥ 0`, indexed by the letters `s : ZMod n` and the odd `i < n`, such that
`∑ᵢ (pⁱ x s i + x (s - i) i) ≤ D s` for every letter `s`; the entry `x s i` counts bi-power
monomials `y_s ^ (pⁱ) y_(s+i)`. The *flow programme* `𝔉_p(D)` is `γ_LT(p) ∑ₛ D s` minus the
supremum of the totals `∑ₛ ∑ᵢ x s i` of the flows.

## Main results

* `TauCeti.flowProgramme`: the flow programme `𝔉_p(D)`.
* `TauCeti.IsFlow`: the flows of a demand `D`; `TauCeti.flowProgramme_eq_sub_sSup` restates
  `𝔉_p(D)` through them.
* `TauCeti.IsFlow.sum_sum_le_div`: the total of a flow is at most `∑ₛ D s / (p + 1)`.
* `TauCeti.flowProgramme_le_sub_of_isFlow`, `TauCeti.sub_le_flowProgramme`: bounds on `𝔉_p(D)`
  from one flow, and from a bound on the totals of all flows.
* `TauCeti.flowProgramme_le`: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s`, with no hypotheses.
* `TauCeti.le_flowProgramme`: `ρ_LT(p) ∑ₛ D s ≤ 𝔉_p(D)` for `D ≥ 0` and `p ≠ 1`.
* `TauCeti.flowProgramme_eq_of_max_le_mul_min`: `𝔉_p(D) = ρ_LT(p) ∑ₛ D s` when `p > 1`, `n ≥ 2`
  and `D s ≤ p D t` for all letters `s`, `t`.

## References

* L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>, is the source of the flow
  programme and of the statements proved here: the bounds are
  `GlobalTheory.FlowProgrammeFacts.main`, and the equality for a nearly constant demand is
  `UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le`. The proofs here are written anew.
-/

public section

open Finset

namespace TauCeti

/-- The *flow programme* `𝔉_p(D)` on the cycle `ZMod n`: `γ_LT(p) ∑ₛ D s`, with
`γ_LT(p) = p / (p² - 1)`, minus the supremum of the totals `∑ₛ ∑ᵢ x s i` of the flows `x ≥ 0`,
indexed by the letters `s` and the odd `i < n`, with `∑ᵢ (pⁱ x s i + x (s - i) i) ≤ D s` for every
`s`. For `D ≥ 0` the zero flow is a flow and the totals are bounded, so the supremum is the largest
total. If some `D s < 0`, there is no flow and the supremum is `sSup ∅ = 0`, so
`𝔉_p(D) = γ_LT(p) ∑ₛ D s`. At `p = 1` the division by `p² - 1 = 0` gives `γ_LT(1) = 0`. -/
noncomputable def flowProgramme (p n : ℕ) [NeZero n] (D : ZMod n → ℝ) : ℝ :=
  (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s -
    sSup {t : ℝ | ∃ x : ZMod n → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧
      (∀ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) ≤ D s) ∧
      t = ∑ s, ∑ i ∈ (range n).filter Odd, x s i}

/-- A *flow* for the demand `D : ZMod n → ℝ` at `p`: a family `x s i ≥ 0` with
`∑ᵢ (pⁱ x s i + x (s - i) i) ≤ D s` for every letter `s`, the sum running over the odd `i < n`. -/
structure IsFlow {n : ℕ} (p : ℕ) (D : ZMod n → ℝ) (x : ZMod n → ℕ → ℝ) : Prop where
  nonneg : ∀ s i, 0 ≤ x s i
  sum_le : ∀ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) ≤ D s

variable {p n : ℕ} {D : ZMod n → ℝ} {x : ZMod n → ℕ → ℝ}

/-- The zero family is a flow for a nonnegative demand. -/
theorem isFlow_zero (hD : ∀ s, 0 ≤ D s) : IsFlow p D 0 :=
  ⟨fun _ _ ↦ le_rfl, fun s ↦ by simpa using hD s⟩

/-- A demand with `D s ≤ p D t` for all letters `s`, `t` and `p > 1` is nonnegative. -/
private theorem nonneg_of_le_mul (hp : 1 < p) (hD : ∀ s t, D s ≤ p * D t) (s : ZMod n) :
    0 ≤ D s := by
  nlinarith [hD s s, show (1 : ℝ) < p by exact_mod_cast hp]

variable [NeZero n]

/-- `𝔉_p(D)` is `γ_LT(p) ∑ₛ D s` minus the supremum of the totals of the flows. -/
theorem flowProgramme_eq_sub_sSup :
    flowProgramme p n D = (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s -
      sSup {t : ℝ | ∃ x, IsFlow p D x ∧ t = ∑ s, ∑ i ∈ (range n).filter Odd, x s i} := by
  rw [flowProgramme]
  congr 2
  ext t
  exact ⟨fun ⟨x, h0, h1, ht⟩ ↦ ⟨x, ⟨h0, h1⟩, ht⟩, fun ⟨x, ⟨h0, h1⟩, ht⟩ ↦ ⟨x, h0, h1, ht⟩⟩

/-- The total of a flow is at most `∑ₛ D s / (p + 1)`. -/
theorem IsFlow.sum_sum_le_div (hx : IsFlow p D x) :
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
          exact sum_le_sum fun s _ ↦ by nlinarith [hx.nonneg s i, hpi i hi]
    _ = ∑ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i) := sum_comm
    _ ≤ ∑ s, D s := sum_le_sum fun s _ ↦ hx.sum_le s

/-- A flow `x` bounds the flow programme from above: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s - ∑ₛ ∑ᵢ x s i`. -/
theorem flowProgramme_le_sub_of_isFlow (hx : IsFlow p D x) :
    flowProgramme p n D ≤
      (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s - ∑ s, ∑ i ∈ (range n).filter Odd, x s i := by
  rw [flowProgramme_eq_sub_sSup]
  refine sub_le_sub_left ?_ _
  refine le_csSup ⟨(∑ s, D s) / (p + 1), ?_⟩ ⟨x, hx, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hy.sum_sum_le_div

/-- If every flow of a nonnegative demand `D` has total at most `c`, then
`γ_LT(p) ∑ₛ D s - c ≤ 𝔉_p(D)`. -/
theorem sub_le_flowProgramme {c : ℝ} (hD : ∀ s, 0 ≤ D s)
    (h : ∀ x, IsFlow p D x → ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤ c) :
    (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s - c ≤ flowProgramme p n D := by
  rw [flowProgramme_eq_sub_sSup]
  refine sub_le_sub_left (csSup_le ?_ ?_) _
  · exact ⟨_, 0, isFlow_zero hD, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx

/-- `γ_LT(p) - ρ_LT(p) = 1 / (p + 1)` for `p ≠ 1`. -/
private theorem div_sub_one_div_sq_sub_one (hp : p ≠ 1) :
    (p : ℝ) / ((p : ℝ) ^ 2 - 1) - 1 / ((p : ℝ) ^ 2 - 1) = 1 / (p + 1) := by
  have h1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp)
  rw [← sub_div, show (p : ℝ) ^ 2 - 1 = (p - 1) * (p + 1) by ring, ← div_div, div_self h1]

/-- `ρ_LT(p) ∑ₛ D s = γ_LT(p) ∑ₛ D s - ∑ₛ D s / (p + 1)` for `p ≠ 1`. -/
private theorem one_div_sq_sub_one_mul_sum (hp : p ≠ 1) :
    1 / ((p : ℝ) ^ 2 - 1) * ∑ s, D s =
      (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s - (∑ s, D s) / (p + 1) := by
  linear_combination (-∑ s, D s) * div_sub_one_div_sq_sub_one hp

/-- The upper bound of the flow programme: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s`. It holds for every `p`,
`n` and `D`. -/
theorem flowProgramme_le (p n : ℕ) [NeZero n] (D : ZMod n → ℝ) :
    flowProgramme p n D ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s := by
  rw [flowProgramme_eq_sub_sSup]
  refine sub_le_self _ (Real.sSup_nonneg ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact sum_nonneg fun s _ ↦ sum_nonneg fun i _ ↦ hx.nonneg s i

/-- The lower bound of the flow programme: `ρ_LT(p) ∑ₛ D s ≤ 𝔉_p(D)` for a nonnegative demand
`D` and `p ≠ 1`, with `ρ_LT(p) = 1 / (p² - 1)`. -/
theorem le_flowProgramme (hp : p ≠ 1) (hD : ∀ s, 0 ≤ D s) :
    1 / ((p : ℝ) ^ 2 - 1) * ∑ s, D s ≤ flowProgramme p n D := by
  rw [one_div_sq_sub_one_mul_sum hp]
  exact sub_le_flowProgramme hD fun x hx ↦ hx.sum_sum_le_div

/-- For `p > 1`, `n ≥ 2` and a demand with `D s ≤ p D t` for all `s`, `t`, the equations
`p y s + y (s - 1) = D s` have a nonnegative solution on `ZMod n`: the alternating sum
`y s = ∑_{k < n} (-1/p)ᵏ D (s - k) / (p (1 - (-1/p)ⁿ))`. -/
private theorem exists_nonneg_shift_solution (hp : 1 < p) (hD : ∀ s t, D s ≤ p * D t) :
    ∃ y : ZMod n → ℝ, (∀ s, 0 ≤ y s) ∧ ∀ s, (p : ℝ) * y s + y (s - 1) = D s := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp
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
    convert hanti.sum_range_neg_one_pow_mul_nonneg
      (fun k ↦ div_nonneg (nonneg_of_le_mul hp hD _) (by positivity)) n using 2 with k
    rw [hr, div_pow]
    ring
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
          rw [sum_range_sub']
          simp only [f, pow_zero, one_mul, Nat.cast_zero, sub_zero, ZMod.natCast_self]
          ring
  refine ⟨fun s ↦ A s / (p * (1 - r ^ n)), fun s ↦ div_nonneg (hA0 s)
    (mul_nonneg (by positivity) (by linarith)), fun s ↦ ?_⟩
  dsimp only
  have hc : (p : ℝ) * (1 - r ^ n) ≠ 0 := mul_ne_zero (by positivity) (by linarith)
  rw [mul_div_assoc', ← add_div, div_eq_iff hc]
  linear_combination key s

/-- The flow programme of a nearly constant demand: for `p > 1`, `n ≥ 2` and `D s ≤ p D t` for all
letters `s`, `t`, `𝔉_p(D) = ρ_LT(p) ∑ₛ D s` with `ρ_LT(p) = 1 / (p² - 1)`. -/
theorem flowProgramme_eq_of_max_le_mul_min (hp : 1 < p) (hn : 1 < n)
    (hD : ∀ s t, D s ≤ p * D t) :
    flowProgramme p n D = 1 / ((p : ℝ) ^ 2 - 1) * ∑ s, D s := by
  refine le_antisymm ?_ (le_flowProgramme hp.ne' (nonneg_of_le_mul hp hD))
  obtain ⟨y, hy0, hy⟩ := exists_nonneg_shift_solution hp hD
  have hsum : ∑ s, y s = (∑ s, D s) / (p + 1) := by
    rw [eq_div_iff (by positivity), ← sum_congr rfl fun s _ ↦ hy s, sum_add_distrib,
      ← Finset.mul_sum, Fintype.sum_equiv (Equiv.subRight 1) (fun s ↦ y (s - 1)) y fun _ ↦ rfl]
    ring
  have h1 : 1 ∈ (range n).filter Odd := mem_filter.mpr ⟨mem_range.mpr hn, odd_one⟩
  -- The flow carried by the shift `i = 1` alone, equal to `y` there.
  have hflow : IsFlow p D fun s i ↦ if i = 1 then y s else 0 := by
    refine ⟨fun s i ↦ ?_, fun s ↦ ?_⟩
    · split_ifs
      exacts [hy0 s, le_rfl]
    · rw [sum_eq_single_of_mem 1 h1 fun i _ hi ↦ by simp [hi]]
      simp only [↓reduceIte, pow_one, Nat.cast_one]
      exact (hy s).le
  have htotal : ∑ s, ∑ i ∈ (range n).filter Odd, (if i = 1 then y s else 0) = ∑ s, y s :=
    sum_congr rfl fun s _ ↦ by simp only [sum_ite_eq', h1, ↓reduceIte]
  rw [one_div_sq_sub_one_mul_sum hp.ne', ← hsum, ← htotal]
  exact flowProgramme_le_sub_of_isFlow hflow

end TauCeti
