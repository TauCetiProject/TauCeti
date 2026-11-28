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
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Algebra.Order.BigOperators.Sum.Alternating
import TauCeti.Algebra.Order.Ring.Basic
import TauCeti.Geometry.Convex.Cone.Farkas

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
* `TauCeti.IsFlow.sum_sum_le_sum_mul`: weak duality for a flow: its total is at most
  `∑ₛ D s * σ s` for every `σ ≥ 0` with `1 ≤ pⁱ σ s + σ (s + i)` for all odd `i < n`.
* `TauCeti.IsFlow.sum_sum_le_div`: the total of a flow is at most `∑ₛ D s / (p + 1)`, the case
  `σ s = 1 / (p + 1)`.
* `TauCeti.flowProgramme_le_sub_of_isFlow`, `TauCeti.sub_le_flowProgramme`: bounds on `𝔉_p(D)`
  from one flow, and from a bound on the totals of all flows.
* `TauCeti.flowProgramme_le`: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s`, with no hypotheses.
* `TauCeti.le_flowProgramme`: `ρ_LT(p) ∑ₛ D s ≤ 𝔉_p(D)` for `D ≥ 0` and `p ≠ 1`.
* `TauCeti.flowProgramme_eq_of_max_le_mul_min`: `𝔉_p(D) = ρ_LT(p) ∑ₛ D s` when `p > 1`, `n ≥ 2`
  and `D s ≤ p D t` for all letters `s`, `t`.
* `TauCeti.IsDualRadiusVector`: dual radius vectors `σ : ZMod n → ℝ` with `0 ≤ σ s ≤ 1` and
  `1 ≤ pⁱ σ s + σ (s + i)` for all odd `i < n`.
* `TauCeti.sum_mul_sub_le_flowProgramme`: weak duality for the flow programme: the dual objective
  `∑ₛ D s * (γ_LT(p) - σ s)` is at most `𝔉_p(D)` for such `σ`, in particular for every dual
  radius vector.
* `TauCeti.exists_isDualRadiusVector_flowProgramme_eq`: for `D ≥ 0` the dual objective takes the
  value `𝔉_p(D)` at some dual radius vector.
* `TauCeti.flowProgramme_duality`: strong LP duality for even `n > 0` and `D ≥ 0`: `𝔉_p(D)` is the
  maximum of the dual objective `∑ₛ D s * (γ_LT(p) - σ s)` over the dual radius vectors `σ`,
  attained at one satisfying `1 ≤ pⁱ σ s + σ (s + i)` for every odd `i : ℕ`.

## References

* L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>, is the source of the flow
  programme and of the statements proved here: the bounds are
  `GlobalTheory.FlowProgrammeFacts.main`, and the equality for a nearly constant demand is
  `UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le`. The dual radius vectors are
  `Formalism.IncomingBounds.IsDual` in `Formalism/IncomingBounds/IncomingBound.lean`, and the
  duality statement is `LemmaFa` in `Formalism/IncomingBounds/WeightIdentities.lean`. The proofs
  here are written anew.
* The strong duality is deduced from Farkas' lemma for a finite linear programme,
  `Matrix.forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq` in
  `TauCeti.Geometry.Convex.Cone.Farkas`.
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

/-- **Weak duality** for a flow: if `σ ≥ 0` satisfies `1 ≤ pⁱ σ s + σ (s + i)` for every letter `s`
and every odd `i < n`, then the total of any flow for `D` is at most `∑ₛ D s * σ s`. No upper bound
on `σ` is needed. -/
theorem IsFlow.sum_sum_le_sum_mul {σ : ZMod n → ℝ} (hx : IsFlow p D x) (h0 : ∀ s, 0 ≤ σ s)
    (hodd : ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i)) :
    ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤ ∑ s, D s * σ s := by
  have hshift : ∀ i : ℕ, ∑ s, x s i * σ (s + i) = ∑ s, x (s - i) i * σ s := fun i ↦
    Fintype.sum_equiv (Equiv.addRight (i : ZMod n)) _ _ fun s ↦ by simp
  calc ∑ s, ∑ i ∈ (range n).filter Odd, x s i
      ≤ ∑ s, ∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * σ s + σ (s + i)) * x s i :=
        sum_le_sum fun s _ ↦ sum_le_sum fun i hi ↦
          le_mul_of_one_le_left (hx.nonneg s i) (hodd s i hi)
    _ = ∑ i ∈ (range n).filter Odd, ∑ s, ((p : ℝ) ^ i * x s i * σ s + x s i * σ (s + i)) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ sum_congr rfl fun s _ ↦ by ring
    _ = ∑ i ∈ (range n).filter Odd, ∑ s, ((p : ℝ) ^ i * x s i + x (s - i) i) * σ s :=
        sum_congr rfl fun i _ ↦ by
          rw [sum_add_distrib, hshift i, ← sum_add_distrib]
          exact sum_congr rfl fun s _ ↦ by ring
    _ = ∑ s, (∑ i ∈ (range n).filter Odd, ((p : ℝ) ^ i * x s i + x (s - i) i)) * σ s := by
        rw [sum_comm]
        exact sum_congr rfl fun s _ ↦ (sum_mul ..).symm
    _ ≤ ∑ s, D s * σ s :=
        sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right (hx.sum_le s) (h0 s)

/-- The total of a flow is at most `∑ₛ D s / (p + 1)`: weak duality `IsFlow.sum_sum_le_sum_mul` for
the uniform radii `σ s = 1 / (p + 1)`, which satisfy `1 ≤ pⁱ σ s + σ (s + i)` since `p ≤ pⁱ`. -/
theorem IsFlow.sum_sum_le_div (hx : IsFlow p D x) :
    ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤ (∑ s, D s) / (p + 1) := by
  have hp : (0 : ℝ) < p + 1 := by positivity
  refine (hx.sum_sum_le_sum_mul (σ := fun _ ↦ 1 / (p + 1)) (fun _ ↦ by positivity)
    fun _ i hi ↦ ?_).trans_eq (by rw [← sum_mul, mul_one_div])
  have hpi : (p : ℝ) ≤ (p : ℝ) ^ i := by
    exact_mod_cast Nat.le_self_pow (mem_filter.mp hi).2.pos.ne' p
  rw [mul_one_div, ← add_div, le_div_iff₀ hp, one_mul]
  linarith

/-- The total of a flow is at most the supremum of the totals of all flows. -/
private theorem IsFlow.sum_sum_le_sSup (hx : IsFlow p D x) :
    ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤
      sSup {t : ℝ | ∃ x, IsFlow p D x ∧ t = ∑ s, ∑ i ∈ (range n).filter Odd, x s i} :=
  le_csSup ⟨(∑ s, D s) / (p + 1), by rintro _ ⟨y, hy, rfl⟩; exact hy.sum_sum_le_div⟩ ⟨x, hx, rfl⟩

/-- A flow `x` bounds the flow programme from above: `𝔉_p(D) ≤ γ_LT(p) ∑ₛ D s - ∑ₛ ∑ᵢ x s i`. -/
theorem flowProgramme_le_sub_of_isFlow (hx : IsFlow p D x) :
    flowProgramme p n D ≤
      (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s, D s - ∑ s, ∑ i ∈ (range n).filter Odd, x s i := by
  rw [flowProgramme_eq_sub_sSup]
  exact sub_le_sub_left hx.sum_sum_le_sSup _

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

/-! ### Linear-programming duality -/

/-- A *dual radius vector* for the flow programme at `p` on `ZMod n`: a vector `σ : ZMod n → ℝ`
with `0 ≤ σ s ≤ 1` for every `s`, and `1 ≤ pⁱ σ s + σ (s + i)` for every `s` and every odd
`i < n`. This is `Formalism.IncomingBounds.IsDual` of the reference. -/
def IsDualRadiusVector (p n : ℕ) (σ : ZMod n → ℝ) : Prop :=
  (∀ s, 0 ≤ σ s ∧ σ s ≤ 1) ∧
    ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i)

omit [NeZero n] in
/-- Characterization of dual radius vectors by their defining constraints. -/
theorem isDualRadiusVector_iff {σ : ZMod n → ℝ} :
    IsDualRadiusVector p n σ ↔ (∀ s, 0 ≤ σ s ∧ σ s ≤ 1) ∧
      ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i) :=
  Iff.rfl

omit [NeZero n] in
/-- The coordinates of a dual radius vector are nonnegative. -/
@[grind →]
theorem IsDualRadiusVector.nonneg {σ : ZMod n → ℝ} (hσ : IsDualRadiusVector p n σ) : 0 ≤ σ :=
  fun s ↦ (hσ.1 s).1

omit [NeZero n] in
/-- The coordinates of a dual radius vector are at most `1`. -/
@[grind →]
theorem IsDualRadiusVector.le_one {σ : ZMod n → ℝ} (hσ : IsDualRadiusVector p n σ) : σ ≤ 1 :=
  fun s ↦ (hσ.1 s).2

omit [NeZero n] in
/-- A dual radius vector satisfies `1 ≤ pⁱ σ s + σ (s + i)` for every letter `s` and every odd
shift `i < n`. -/
theorem IsDualRadiusVector.one_le {σ : ZMod n → ℝ} (hσ : IsDualRadiusVector p n σ) (s : ZMod n)
    (i : ℕ) (hi : i ∈ (range n).filter Odd) : 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i) :=
  hσ.2 s i hi

grind_pattern IsDualRadiusVector.one_le => IsDualRadiusVector p n σ, s + (i : ZMod n)

/-- For an even cycle length `n > 0`, a vector `σ ≥ 0` with `1 ≤ pⁱ σ s + σ (s + i)` for every odd
`i < n` satisfies it for every odd `i : ℕ`: the shift `i` reduces to `i % n`, which is odd. -/
theorem one_le_pow_mul_add_of_odd {σ : ZMod n → ℝ} (h0 : ∀ s, 0 ≤ σ s)
    (hodd : ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i))
    (hn : Even n) (s : ZMod n) {i : ℕ} (hi : Odd i) :
    1 ≤ (p : ℝ) ^ i * σ s + σ (s + i) := by
  have hmem : i % n ∈ (range n).filter Odd :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt i (Nat.pos_of_ne_zero (NeZero.ne n))),
      hi.mod_even hn⟩
  have hpow : (p : ℝ) ^ (i % n) ≤ (p : ℝ) ^ i := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [Nat.cast_zero, zero_pow (hi.mod_even hn).pos.ne', zero_pow hi.pos.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hp) (Nat.mod_le i n)
  calc (1 : ℝ) ≤ (p : ℝ) ^ (i % n) * σ s + σ (s + (i % n : ℕ)) := hodd s (i % n) hmem
    _ = (p : ℝ) ^ (i % n) * σ s + σ (s + i) := by rw [ZMod.natCast_mod]
    _ ≤ (p : ℝ) ^ i * σ s + σ (s + i) :=
      add_le_add (mul_le_mul_of_nonneg_right hpow (h0 s)) le_rfl

/-- **Weak duality** for the flow programme: every `σ ≥ 0` with `1 ≤ pⁱ σ s + σ (s + i)` for every
odd `i < n`, in particular every dual radius vector, bounds the flow programme of a nonnegative
demand `D` from below by the dual objective: `∑ₛ D s * (γ_LT(p) - σ s) ≤ 𝔉_p(D)`. -/
theorem sum_mul_sub_le_flowProgramme {σ : ZMod n → ℝ} (h0 : ∀ s, 0 ≤ σ s)
    (hodd : ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i))
    (hD : ∀ s, 0 ≤ D s) :
    ∑ s, D s * ((p : ℝ) / ((p : ℝ) ^ 2 - 1) - σ s) ≤ flowProgramme p n D := by
  rw [Finset.sum_mul_const_sub]
  exact sub_le_flowProgramme hD fun _ hx ↦ hx.sum_sum_le_sum_mul h0 hodd

omit [NeZero n] in
/-- Clamping a nonnegative dual certificate to `[0, 1]` gives a dual radius vector. -/
private theorem isDualRadiusVector_min_one {σ : ZMod n → ℝ} (h0 : ∀ s, 0 ≤ σ s)
    (hodd : ∀ s, ∀ i ∈ (range n).filter Odd, 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i)) :
    IsDualRadiusVector p n fun s ↦ min (σ s) 1 := by
  refine isDualRadiusVector_iff.mpr
    ⟨fun s ↦ ⟨le_min (h0 s) zero_le_one, min_le_right _ _⟩, fun s i hi ↦ ?_⟩
  have hpow : (p : ℝ) ^ i = 0 ∨ 1 ≤ (p : ℝ) ^ i := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact .inl (by simp [(mem_filter.mp hi).2.pos.ne'])
    · exact .inr (one_le_pow₀ (by exact_mod_cast hp))
  exact one_le_mul_min_one_add_min_one (h0 s) (h0 _) hpow (hodd s i hi)

/-- The column indices of the flow programme LP: a letter and an odd shift `i < n`. -/
private abbrev FlowIndex (n : ℕ) : Type := ZMod n × {i // i ∈ (range n).filter Odd}

omit [NeZero n] in
/-- The flow `x s i` of a vector `v` on the column indices, extended by zero to all shifts `i`. -/
private def flowOfVec (v : FlowIndex n → ℝ) (s : ZMod n) (i : ℕ) : ℝ :=
  if hi : i ∈ (range n).filter Odd then v (s, ⟨i, hi⟩) else 0

/-- The demand block of the flow programme LP: row `s` encodes `∑ᵢ (pⁱ x s i + x (s - i) i)`. -/
private def flowDemandMatrix (p n : ℕ) : Matrix (ZMod n) (FlowIndex n) ℝ :=
  fun s k ↦ (if k.1 = s then (p : ℝ) ^ (k.2 : ℕ) else 0) + (if k.1 = s - (k.2 : ℕ) then 1 else 0)

/-- Row evaluation of the demand block. -/
private theorem flowDemandMatrix_mulVec (v : FlowIndex n → ℝ) (s : ZMod n) :
    (flowDemandMatrix p n).mulVec v s = ∑ i ∈ (range n).filter Odd,
      ((p : ℝ) ^ i * flowOfVec v s i + flowOfVec v (s - i) i) := by
  simp only [Matrix.mulVec, dotProduct, flowDemandMatrix]
  rw [← Finset.sum_attach ((range n).filter Odd), Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [flowOfVec, add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, i.property, ↓reduceDIte]

/-- Column evaluation of the demand block. -/
private theorem vecMul_flowDemandMatrix (y : ZMod n → ℝ) (k : FlowIndex n) :
    Matrix.vecMul y (flowDemandMatrix p n) k = (p : ℝ) ^ (k.2 : ℕ) * y k.1 + y (k.1 + k.2) := by
  simp only [Matrix.vecMul, dotProduct, flowDemandMatrix, mul_add, mul_ite, mul_zero, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [eq_sub_iff_add_eq]
  rw [Fintype.sum_ite_eq, mul_comm]

/-- The total of the flow of a vector `v` is the sum of the entries of `v`. -/
private theorem sum_sum_flowOfVec (v : FlowIndex n → ℝ) :
    ∑ s, ∑ i ∈ (range n).filter Odd, flowOfVec v s i = ∑ k, v k := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← Finset.sum_attach ((range n).filter Odd)]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [flowOfVec, i.property]

/-- Farkas certificate for an upper bound `M` on the total of every flow for `D ≥ 0`: Farkas' lemma
`Matrix.forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq` applied to the flow programme LP gives
a nonnegative dual vector with `1 ≤ pⁱ σ s + σ (s + i)` for all odd `i < n` and `∑ₛ D s * σ s ≤ M`,
and clamping it to `[0, 1]` gives a dual radius vector `σ` with `∑ₛ D s * σ s ≤ M`. -/
private theorem exists_isDualRadiusVector_sum_mul_le {M : ℝ} (hD : ∀ s, 0 ≤ D s)
    (hM : ∀ x, IsFlow p D x → ∑ s, ∑ i ∈ (range n).filter Odd, x s i ≤ M) :
    ∃ σ : ZMod n → ℝ, IsDualRadiusVector p n σ ∧ ∑ s, D s * σ s ≤ M := by
  set A := Matrix.fromRows (flowDemandMatrix p n) (-1 : Matrix (FlowIndex n) (FlowIndex n) ℝ)
  have hfeas : ∃ v, A.mulVec v ≤ Sum.elim D 0 ∧ (0 : Matrix (Fin 0) (FlowIndex n) ℝ).mulVec v = 0 :=
    ⟨0, fun r ↦ by rcases r with s | k <;> simp [A, hD], by simp⟩
  have hvalid : ∀ v, A.mulVec v ≤ Sum.elim D 0 → (0 : Matrix (Fin 0) (FlowIndex n) ℝ).mulVec v = 0 →
      dotProduct 1 v ≤ M := fun v hv _ ↦ by
    have hx : IsFlow p D (flowOfVec v) := by
      refine ⟨fun s i ↦ ?_, fun s ↦ ?_⟩
      · unfold flowOfVec
        split_ifs with hi
        exacts [by simpa [A, Matrix.neg_mulVec] using hv (.inr (s, ⟨i, hi⟩)), le_rfl]
      · rw [← flowDemandMatrix_mulVec]
        simpa [A] using hv (.inl s)
    rw [show dotProduct 1 v = ∑ k, v k by simp [dotProduct], ← sum_sum_flowOfVec]
    exact hM _ hx
  obtain ⟨y, hy, _, hyA, hyb⟩ :=
    (Matrix.forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq A (Sum.elim D 0)
      (0 : Matrix (Fin 0) (FlowIndex n) ℝ) 0 1 M hfeas).mp hvalid
  simp only [A, Matrix.vecMul_fromRows, Matrix.vecMul_neg, Matrix.vecMul_one, Matrix.vecMul_zero,
    add_zero, dotProduct_zero] at hyA hyb
  refine ⟨_, isDualRadiusVector_min_one (fun s ↦ hy (.inl s)) fun s i hi ↦ ?_, ?_⟩
  · have h := congrFun hyA (s, ⟨i, hi⟩)
    simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, Pi.one_apply,
      vecMul_flowDemandMatrix] at h
    change 1 ≤ (p : ℝ) ^ i * y (.inl s) + y (.inl (s + i))
    linarith [show (0 : ℝ) ≤ y (.inr (s, ⟨i, hi⟩)) from hy _]
  · refine (sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (min_le_left _ _) (hD s)).trans
      (le_of_eq_of_le ?_ hyb)
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun s _ ↦ mul_comm _ _

/-- **Strong duality** for the flow programme: for a nonnegative demand `D`, the dual objective
`∑ₛ D s * (γ_LT(p) - σ s)` takes the value `𝔉_p(D)` at some dual radius vector `σ`. By weak duality
`sum_mul_sub_le_flowProgramme` this value is the maximum of the dual objective. -/
theorem exists_isDualRadiusVector_flowProgramme_eq (hD : ∀ s, 0 ≤ D s) :
    ∃ σ : ZMod n → ℝ, IsDualRadiusVector p n σ ∧
      flowProgramme p n D = ∑ s, D s * ((p : ℝ) / ((p : ℝ) ^ 2 - 1) - σ s) := by
  obtain ⟨σ, hσ, hsum⟩ := exists_isDualRadiusVector_sum_mul_le hD fun _ hx ↦ hx.sum_sum_le_sSup
  refine ⟨σ, hσ, le_antisymm ?_ (sum_mul_sub_le_flowProgramme hσ.nonneg hσ.one_le hD)⟩
  rw [flowProgramme_eq_sub_sSup, Finset.sum_mul_const_sub]
  exact sub_le_sub_left hsum _

/-- **Strong LP duality for the flow programme**: for even `n > 0` and a nonnegative demand `D`,
`𝔉_p(D)` is the maximum of the dual objective `∑ₛ D s * (γ_LT(p) - σ s)` over the dual radius
vectors `σ`: the objective is at most `𝔉_p(D)` at every dual radius vector, and equals it at one
that also satisfies `1 ≤ pⁱ σ s + σ (s + i)` for every odd `i : ℕ`, including `i ≥ n`. This is
`LemmaFa` of the reference. -/
theorem flowProgramme_duality (hn : Even n) (hD : ∀ s, 0 ≤ D s) :
    (∀ σ, IsDualRadiusVector p n σ →
        ∑ s, D s * ((p : ℝ) / ((p : ℝ) ^ 2 - 1) - σ s) ≤ flowProgramme p n D) ∧
      ∃ σ : ZMod n → ℝ, IsDualRadiusVector p n σ ∧
        (∀ s, ∀ i : ℕ, Odd i → 1 ≤ (p : ℝ) ^ i * σ s + σ (s + i)) ∧
        flowProgramme p n D = ∑ s, D s * ((p : ℝ) / ((p : ℝ) ^ 2 - 1) - σ s) := by
  refine ⟨fun σ hσ ↦ sum_mul_sub_le_flowProgramme hσ.nonneg hσ.one_le hD, ?_⟩
  obtain ⟨σ, hσ, heq⟩ := exists_isDualRadiusVector_flowProgramme_eq (p := p) hD
  exact ⟨σ, hσ, fun s _ hi ↦ one_le_pow_mul_add_of_odd hσ.nonneg hσ.one_le hn s hi, heq⟩

end TauCeti
