/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet

/-!
# Major and minor arcs

The circle method for a problem of size `N` integrates a `1`-periodic function over a unit
interval and splits that interval into *major arcs*, short intervals around the rationals
`a / q` of small denominator `q ≤ Q`, and the complementary *minor arcs*. On the major arcs the
exponential sums are evaluated asymptotically; on the minor arcs they are bounded using a rational
approximation `a / q` of `α` whose denominator `q` is neither small nor large.

Following Davenport, we integrate over `[Q/N, 1 + Q/N]` rather than `[0, 1]`, so that, once
`2 Q² ≤ N`, every major arc `{α : |α - a/q| ≤ Q/N}` with `1 ≤ a ≤ q ≤ Q` and `gcd(a, q) = 1` lies
inside the interval without wrapping around. The parameters are a natural number `N` and a real
`Q`; in applications `Q = (log N)^B`.

## Main definitions

* `TauCeti.arcInterval N Q`: the interval `[Q/N, 1 + Q/N]`.
* `TauCeti.majorArcIndex Q`: the pairs `(q, a)` with `1 ≤ a ≤ q ≤ Q` and `gcd(a, q) = 1`.
* `TauCeti.majorArc N Q q a`: the points `α` of the interval with `|α - a/q| ≤ Q/N`.
* `TauCeti.majorArcs N Q` and `TauCeti.minorArcs N Q`: the union of the major arcs, and its
  complement in the interval.

## Main results

* `TauCeti.majorArc_eq_Icc`: when `2 Q² ≤ N`, each major arc is the full interval
  `[a/q - Q/N, a/q + Q/N]`.
* `TauCeti.pairwiseDisjoint_majorArc`: when `2 Q³ < N`, the major arcs are pairwise disjoint,
  since distinct fractions with denominators at most `Q` differ by at least `Q⁻²`.
* `TauCeti.exists_abs_sub_div_le_of_mem_minorArcs`: when `1 ≤ Q` and `2 Q² ≤ N`, every `α` on
  the minor arcs has a reduced approximation `|α - a/q| ≤ q⁻²` with `Q < q ≤ N/Q`. This is the
  input to the minor-arc bound for exponential sums over primes.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapter 26.
* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Chapter 3.
-/

public section

noncomputable section

open Set

namespace TauCeti

/-- The interval `[Q/N, 1 + Q/N]` of length one over which the circle method integrates. -/
def arcInterval (N : ℕ) (Q : ℝ) : Set ℝ :=
  Icc (Q / N) (1 + Q / N)

/-- The pairs `(q, a)` indexing the major arcs: `1 ≤ q ≤ Q`, `1 ≤ a ≤ q` and `gcd(a, q) = 1`. -/
def majorArcIndex (Q : ℝ) : Finset (ℕ × ℤ) :=
  (Finset.Icc 1 ⌊Q⌋₊ ×ˢ Finset.Icc (1 : ℤ) ⌊Q⌋₊).filter
    fun p => p.2 ≤ p.1 ∧ Int.gcd p.2 p.1 = 1

/-- The major arc `𝔐(q, a)`: the points `α ∈ [Q/N, 1 + Q/N]` with `|α - a/q| ≤ Q/N`. -/
def majorArc (N : ℕ) (Q : ℝ) (q : ℕ) (a : ℤ) : Set ℝ :=
  arcInterval N Q ∩ Icc (a / q - Q / N) (a / q + Q / N)

/-- The union `𝔐` of the major arcs `𝔐(q, a)` over the pairs of `majorArcIndex Q`. -/
def majorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  ⋃ p ∈ majorArcIndex Q, majorArc N Q p.1 p.2

/-- The minor arcs `𝔪`: the points of `[Q/N, 1 + Q/N]` on no major arc. -/
def minorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  arcInterval N Q \ majorArcs N Q

variable {N : ℕ} {Q α : ℝ}

theorem arcInterval_eq_Icc : arcInterval N Q = Icc (Q / N) (1 + Q / N) :=
  (rfl)

@[simp]
theorem mem_arcInterval : α ∈ arcInterval N Q ↔ Q / N ≤ α ∧ α ≤ 1 + Q / N :=
  Iff.rfl

@[simp]
theorem mem_majorArcIndex {p : ℕ × ℤ} :
    p ∈ majorArcIndex Q ↔
      1 ≤ p.1 ∧ (p.1 : ℝ) ≤ Q ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ Int.gcd p.2 p.1 = 1 := by
  obtain ⟨q, a⟩ := p
  simp only [majorArcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hq1, hqQ⟩, ha1, -⟩, haq, hgcd⟩
    exact ⟨hq1, (Nat.le_floor_iff' (by omega)).1 hqQ, ha1, haq, hgcd⟩
  · rintro ⟨hq1, hqQ, ha1, haq, hgcd⟩
    have hqQ' : q ≤ ⌊Q⌋₊ := (Nat.le_floor_iff' (by omega)).2 hqQ
    exact ⟨⟨⟨hq1, hqQ'⟩, ha1, haq.trans (by exact_mod_cast hqQ')⟩, haq, hgcd⟩

@[simp]
theorem mem_majorArc {q : ℕ} {a : ℤ} :
    α ∈ majorArc N Q q a ↔ α ∈ arcInterval N Q ∧ |α - a / q| ≤ Q / N := by
  simp only [majorArc, mem_inter_iff, mem_Icc, abs_sub_le_iff, tsub_le_iff_right]
  constructor <;> rintro ⟨h, h₁, h₂⟩ <;> exact ⟨h, by linarith, by linarith⟩

@[simp]
theorem mem_majorArcs :
    α ∈ majorArcs N Q ↔ ∃ p ∈ majorArcIndex Q, α ∈ majorArc N Q p.1 p.2 := by
  simp only [majorArcs, mem_iUnion, exists_prop]

@[simp]
theorem mem_minorArcs : α ∈ minorArcs N Q ↔ α ∈ arcInterval N Q ∧ α ∉ majorArcs N Q :=
  Iff.rfl

theorem majorArc_subset_arcInterval (q : ℕ) (a : ℤ) : majorArc N Q q a ⊆ arcInterval N Q :=
  inter_subset_left

theorem majorArcs_subset_arcInterval : majorArcs N Q ⊆ arcInterval N Q :=
  iUnion₂_subset fun _ _ => majorArc_subset_arcInterval _ _

theorem minorArcs_subset_arcInterval : minorArcs N Q ⊆ arcInterval N Q :=
  sdiff_subset

theorem majorArcs_union_minorArcs : majorArcs N Q ∪ minorArcs N Q = arcInterval N Q :=
  union_sdiff_cancel majorArcs_subset_arcInterval

theorem disjoint_majorArcs_minorArcs : Disjoint (majorArcs N Q) (minorArcs N Q) :=
  disjoint_sdiff_right

theorem measurableSet_arcInterval : MeasurableSet (arcInterval N Q) :=
  measurableSet_Icc

theorem measurableSet_majorArc (q : ℕ) (a : ℤ) : MeasurableSet (majorArc N Q q a) :=
  measurableSet_arcInterval.inter measurableSet_Icc

theorem measurableSet_majorArcs : MeasurableSet (majorArcs N Q) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_majorArc _ _

theorem measurableSet_minorArcs : MeasurableSet (minorArcs N Q) :=
  measurableSet_arcInterval.diff measurableSet_majorArcs

/-- If `2 Q² ≤ N`, then `2 Q/N ≤ 1/Q`: a fraction at distance `1/Q` from the boundary of the
interval keeps its whole major arc inside it. -/
private theorem two_mul_div_le_one_div (hQ : 0 < Q) (hN : 2 * Q ^ 2 ≤ N) :
    2 * (Q / N) ≤ 1 / Q := by
  have hN0 : (0 : ℝ) < N := by linarith [pow_pos hQ 2]
  rw [mul_div_assoc', div_le_div_iff₀ hN0 hQ]
  nlinarith

/-- When `2 Q² ≤ N`, a major arc lies inside `[Q/N, 1 + Q/N]` without truncation: it is the full
interval `[a/q - Q/N, a/q + Q/N]`. -/
theorem majorArc_eq_Icc (hN : 2 * Q ^ 2 ≤ N) {q : ℕ} {a : ℤ} (hp : (q, a) ∈ majorArcIndex Q) :
    majorArc N Q q a = Icc (a / q - Q / N) (a / q + Q / N) := by
  obtain ⟨hq1, hqQ, ha1, haq, -⟩ := mem_majorArcIndex.1 hp
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have haq' : (a : ℝ) ≤ q := by exact_mod_cast haq
  refine inter_eq_right.2 (Icc_subset_Icc ?_ ?_)
  · -- `a/q ≥ 1/Q ≥ 2Q/N`.
    have h1 : 1 / Q ≤ a / q := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith [two_mul_div_le_one_div (by linarith) hN]
  · have : (a : ℝ) / q ≤ 1 := (div_le_one (by linarith)).2 haq'
    linarith

/-- The fraction `a/q` determines a pair `(q, a)` of `majorArcIndex Q`. -/
private theorem eq_of_div_eq_div {p p' : ℕ × ℤ} (hp : p ∈ majorArcIndex Q)
    (hp' : p' ∈ majorArcIndex Q) (h : (p.2 : ℝ) / p.1 = p'.2 / p'.1) : p = p' := by
  obtain ⟨hq1, -, -, -, hgcd⟩ := mem_majorArcIndex.1 hp
  obtain ⟨hq1', -, -, -, hgcd'⟩ := mem_majorArcIndex.1 hp'
  rw [Int.gcd_eq_natAbs_gcd_natAbs, ← Nat.coprime_iff_gcd_eq_one] at hgcd hgcd'
  have hQ : ((p.2 : ℚ) / ((p.1 : ℤ) : ℚ)) = (p'.2 : ℚ) / ((p'.1 : ℤ) : ℚ) := by
    exact_mod_cast h
  obtain ⟨hnum, hden⟩ := Rat.div_int_inj (by omega) (by omega) hgcd hgcd' hQ
  exact Prod.ext (by exact_mod_cast hden) hnum

/-- When `2 Q³ < N`, the major arcs `𝔐(q, a)` are pairwise disjoint: distinct fractions with
denominators at most `Q` are at distance at least `Q⁻²`, which exceeds `2Q/N`. -/
theorem pairwiseDisjoint_majorArc (hN : 2 * Q ^ 3 < N) :
    (majorArcIndex Q : Set (ℕ × ℤ)).PairwiseDisjoint fun p => majorArc N Q p.1 p.2 := by
  intro p hp p' hp' hne
  rw [Function.onFun, disjoint_left]
  intro α h₁ h₂
  obtain ⟨hq1, hqQ, -, -, -⟩ := mem_majorArcIndex.1 hp
  obtain ⟨hq1', hqQ', -, -, -⟩ := mem_majorArcIndex.1 hp'
  have hq : (1 : ℝ) ≤ p.1 := by exact_mod_cast hq1
  have hQ : 1 ≤ Q := hq.trans hqQ
  have hN0 : (0 : ℝ) < N := by linarith [pow_pos (by linarith : (0 : ℝ) < Q) 3]
  have hsep : 1 / ((p.1 : ℝ) * p'.1) ≤ |(p.2 : ℝ) / p.1 - p'.2 / p'.1| := by
    have hne' : (p.2 : ℝ) / ((p.1 : ℤ) : ℝ) ≠ p'.2 / ((p'.1 : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast] using fun h => hne (eq_of_div_eq_div hp hp' h)
    simpa only [Int.cast_natCast] using
      one_div_mul_le_abs_div_sub_div (by omega) (by omega) hne'
  have hclose : |(p.2 : ℝ) / p.1 - p'.2 / p'.1| ≤ 2 * (Q / N) := by
    have h₁' := (mem_majorArc.1 h₁).2
    rw [abs_sub_comm] at h₁'
    exact (abs_sub_le _ α _).trans (by linarith [(mem_majorArc.1 h₂).2])
  -- `1/(q q') ≥ 1/Q² > 2Q/N`.
  have hQ2 : 1 / Q ^ 2 ≤ 1 / ((p.1 : ℝ) * p'.1) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hlt : 2 * (Q / N) < 1 / Q ^ 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hN0 (by positivity)]
    nlinarith
  linarith

/-- **Minor arcs.** When `1 ≤ Q` and `2 Q² ≤ N`, every `α` on the minor arcs has a reduced rational
approximation `|α - a/q| ≤ q⁻²` with `Q < q ≤ N/Q`. -/
theorem exists_abs_sub_div_le_of_mem_minorArcs (hQ : 1 ≤ Q) (hN : 2 * Q ^ 2 ≤ N)
    (hα : α ∈ minorArcs N Q) :
    ∃ (q : ℕ) (a : ℤ), Q < q ∧ (q : ℝ) ≤ N / Q ∧ Int.gcd a q = 1 ∧
      |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  -- Dirichlet's approximation theorem with bound `N/Q` gives a reduced fraction `a/q` with
  -- `q ≤ N/Q` and `|α - a/q| < 1/(q N/Q)`; a denominator `q ≤ Q` would put `α` on the major
  -- arc `𝔐(q, a)`.
  have hQ0 : 0 < Q := by linarith
  have hN0 : (0 : ℝ) < N := by linarith [pow_pos hQ0 2]
  obtain ⟨q, a, hq1, hgcd, hlt, hqN⟩ : ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ Int.gcd a q = 1 ∧
      |α - a / q| < 1 / (q * (N / Q)) ∧ (q : ℝ) ≤ N / Q := by
    obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_lt_and_den_le α
      ((one_le_div hQ0).2 (by nlinarith))
    refine ⟨r.den, r.num, r.den_pos, ?_, by rwa [Rat.cast_def] at hr, hden⟩
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact r.reduced.gcd_eq_one
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  refine ⟨q, a, ?_, hqN, hgcd, ?_⟩
  · by_contra hqQ
    rw [not_lt] at hqQ
    have hclose : |α - a / q| < Q / N := by
      refine hlt.trans_le ?_
      rw [← one_div_div (N : ℝ) Q]
      exact one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_left (by positivity) hq)
    have hαI := (mem_minorArcs.1 hα).1
    rw [mem_arcInterval] at hαI
    obtain ⟨hlo, hhi⟩ := abs_sub_lt_iff.1 hclose
    have ha1 : 1 ≤ a := by
      by_contra ha
      have ha0 : (a : ℝ) ≤ 0 := by exact_mod_cast (by omega : a ≤ 0)
      have : (a : ℝ) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha0 (by positivity)
      linarith
    have haq : a ≤ q := by
      by_contra ha
      have ha' : (q : ℝ) + 1 ≤ a := by exact_mod_cast not_le.1 ha
      -- `a/q ≥ 1 + 1/Q`, and `1/Q ≥ 2Q/N`.
      have h1 : 1 + 1 / Q ≤ (a : ℝ) / q := by
        have hQq : 1 / Q ≤ 1 / q := one_div_le_one_div_of_le (by linarith) hqQ
        have : 1 + 1 / (q : ℝ) ≤ a / q := by
          rw [one_add_div (by positivity), div_le_div_iff_of_pos_right (by positivity)]
          exact ha'
        linarith
      linarith [two_mul_div_le_one_div hQ0 hN]
    exact (mem_minorArcs.1 hα).2 (mem_majorArcs.2
      ⟨(q, a), mem_majorArcIndex.2 ⟨by exact_mod_cast hq, hqQ, ha1, haq, hgcd⟩,
        mem_majorArc.2 ⟨(mem_minorArcs.1 hα).1, hclose.le⟩⟩)
  · refine hlt.le.trans ?_
    rw [sq]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hqN (by positivity))

end TauCeti

end
