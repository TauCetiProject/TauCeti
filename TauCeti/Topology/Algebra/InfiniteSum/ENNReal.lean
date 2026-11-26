/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Sums of extended nonnegative series

A series in `ℝ≥0∞` with a finite sum has a convergent real-valued series obtained by applying
`ENNReal.toReal` termwise. The real sum is the `toReal` of the original sum. This converts
nonnegative mass series into real probability formulas without repeating the finiteness argument.

Summing the indicator of a set `s` with value one counts its elements: the sum is `s.encard`.
This is the indicator form of `ENNReal.tsum_set_one`.

Every `y : ℝ≥0∞` is bounded by the dyadic series `1 + ∑ₖ 2^k 1{2^k < y}`. Applied pointwise to
a nonnegative function and integrated, this bounds its integral by a weighted sum of the measures
of its dyadic level sets.

A finite product of infinite sums in `ℝ≥0∞` expands as the infinite sum over the dependent
product type of the products of terms (`ENNReal.prod_tsum`). Restricting a series over a set `A`
by a pointwise `ite` restricts the index to `{x ∈ A | p x}` (`ENNReal.tsum_subtype_ite`), and
a fiber-constant series over `A` regroups by fiber cardinalities (`ENNReal.tsum_encard_sep_eq_mul`).

## Main declarations

* `HasSum.toReal`: a series in `ℝ≥0∞` with finite sum has the termwise `toReal` sum.
* `ENNReal.tsum_indicator_one`: summing the indicator of `s` with value one gives `s.encard`.
* `ENNReal.le_one_add_tsum_pow_indicator`: `y ≤ 1 + ∑ₖ 2^k 1{2^k < y}`.
* `ENNReal.prod_tsum`: `∏ i, ∑' y, f i y = ∑' x : ∀ i, κ i, ∏ i, f i (x i)`.
* `ENNReal.tsum_subtype_ite`: restricting a `tsum` over `A` by `if p x.val then g x.val else 0`.
* `ENNReal.tsum_encard_sep_eq_mul`: regrouping a `tsum` over `A` by fiber `encard`.
-/

public section

open scoped ENNReal

/-- Applying `ENNReal.toReal` termwise preserves a series with finite sum. -/
theorem HasSum.toReal {ι : Type*} {f : ι → ℝ≥0∞} {s : ℝ≥0∞}
    (h : HasSum f s) (hs : s ≠ ∞) : HasSum (fun i ↦ (f i).toReal) s.toReal := by
  have hfin : ∑' i, f i ≠ ∞ := by rwa [h.tsum_eq]
  simpa only [← ENNReal.tsum_toReal_eq (_root_.ne_top_of_tsum_ne_top hfin), h.tsum_eq]
    using ENNReal.hasSum_toReal hfin

/-- Summing the indicator of a set with value one counts its elements. -/
theorem ENNReal.tsum_indicator_one {β : Type*} (s : Set β) :
    ∑' b, s.indicator (fun _ => (1 : ℝ≥0∞)) b = s.encard := by
  rw [← ENNReal.tsum_set_one, tsum_subtype _ fun _ => (1 : ℝ≥0∞)]

/-- A nonnegative extended real is at most `1 + ∑ₖ 2^k 1{2^k < y}`, with equality when `y` is a
power of two. -/
theorem ENNReal.le_one_add_tsum_pow_indicator (y : ℝ≥0∞) :
    y ≤ 1 + ∑' k : ℕ, if (2 : ℝ≥0∞) ^ k < y then 2 ^ k else 0 := by
  set t : ℕ → ℝ≥0∞ := fun k ↦ if 2 ^ k < y then 2 ^ k else 0
  by_contra! hy
  -- Each partial sum `1 + ∑ k < n, t k` is at most the full series, which is below `y`.
  have hpart (n : ℕ) : 1 + ∑ k ∈ Finset.range n, t k ≤ 1 + ∑' k, t k := by
    gcongr; exact sum_le_tsum _
  -- By induction `2 ^ n ≤ 1 + ∑ k < n, t k`: then `2 ^ n < y`, so `t n = 2 ^ n`.
  have hpow (n : ℕ) : (2 : ℝ≥0∞) ^ n ≤ 1 + ∑ k ∈ Finset.range n, t k := by
    induction n with
    | zero => simp
    | succ n ih =>
      have htn : t n = 2 ^ n := by simp [t, (ih.trans (hpart n)).trans_lt hy]
      rw [Finset.sum_range_succ, ← add_assoc, htn, pow_succ, mul_two]
      gcongr
  -- So the finite series dominates every `2 ^ n`, which is absurd.
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hy.ne_top
  have : (n : ℝ≥0∞) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  exact (hn.trans this).not_ge ((hpow n).trans (hpart n))

private theorem ENNReal.prod_tsum_fin :
    ∀ {m : ℕ} {κ : Fin m → Type*} (f : ∀ i, κ i → ℝ≥0∞),
      ∏ i, ∑' y : κ i, f i y = ∑' x : ∀ i, κ i, ∏ i, f i (x i)
  | 0, _, f => by simp
  | m + 1, κ, f => by
    rw [← (Fin.consEquiv κ).tsum_eq]
    simp_rw [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [tsum_prod' (f := fun p : κ 0 × (∀ i : Fin m, κ i.succ) ↦
      f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ← ENNReal.prod_tsum_fin fun i ↦ f i.succ]

/-- A finite product of infinite sums in `ℝ≥0∞` equals the infinite sum over the dependent
product type of the products of terms. -/
theorem ENNReal.prod_tsum {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (f : ∀ i, κ i → ℝ≥0∞) :
    ∏ i, ∑' y : κ i, f i y = ∑' x : ∀ i, κ i, ∏ i, f i (x i) := by
  -- Reindex `ι` by `Fin (Fintype.card ι)` in the product and, via `Equiv.piCongrLeft`, in the
  -- tuples.
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ENNReal.prod_tsum_fin, ← (Equiv.piCongrLeft κ e).tsum_eq]
  exact tsum_congr fun x ↦ Fintype.prod_equiv e _ _ fun j ↦ by rw [Equiv.piCongrLeft_apply_apply]

/-- Restricting an extended nonnegative series over a set `A` by `if p x.val then g x.val else 0`
equals the series over `{x ∈ A | p x}`. -/
theorem ENNReal.tsum_subtype_ite {α : Type*} (A : Set α) (p : α → Prop) [DecidablePred p]
    (g : α → ℝ≥0∞) :
    (∑' x : A, if p x.val then g x.val else 0) = ∑' x : {x ∈ A | p x}, g x.val := by
  refine Eq.trans ?_ ((_root_.tsum_subtype {x : A | p x.val} (fun x : A ↦ g x.val)).symm.trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ A) p).tsum_eq fun x ↦ g x.val))
  refine tsum_congr fun x ↦ ?_
  by_cases h : p x.val <;> simp [Set.indicator, h]

/-- Regrouping a fiber-constant extended nonnegative series over `A : Set α` by the extended
cardinality of each fiber `{x ∈ A | f x = j}`. -/
theorem ENNReal.tsum_encard_sep_eq_mul {α β : Type*} (A : Set α) (f : α → β)
    (w : β → ℝ≥0∞) :
    ∑' j : β, ({x ∈ A | f x = j}.encard : ℝ≥0∞) * w j = ∑' x : A, w (f x.val) := by
  rw [← tsum_fiberwise (fun x : A ↦ w (f x.val)) (fun x : A ↦ f x.val)]
  refine tsum_congr fun j ↦ ?_
  have hconst : ∀ x : (fun x : A ↦ f x.val) ⁻¹' {j}, w (f x.val.val) = w j :=
    fun x ↦ congrArg w x.property
  have heq : (∑' _ : (fun x : A ↦ f x.val) ⁻¹' {j}, w j) =
      ∑' _ : {x ∈ A | f x = j}, w j :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ A) fun x ↦ f x = j).tsum_eq fun _ ↦ w j
  rw [tsum_congr hconst, heq, ENNReal.tsum_set_const]
