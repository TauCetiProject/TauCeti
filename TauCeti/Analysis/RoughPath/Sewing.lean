/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Sort

/-!
# The sewing lemma

A two-parameter map `Ξ : ℝ → ℝ → E` into a Banach space is a *germ* of an additive map when its
defect `Ξ s t - Ξ s u - Ξ u t` is small. The sewing lemma says that if the defect is bounded by
`C (t - s) ^ γ` on the simplex of `[a, b]` for some `γ > 1`, then there is exactly one additive
map within `O((t - s) ^ γ)` of `Ξ`, and it is the limit of the Riemann sums of `Ξ`. This is the
construction on which the Young integral and the rough integral rest.

The map is built as the limit of the dyadic Riemann sums `dyadicSum Ξ s t n`, which split
`[s, t]` into `2 ^ n` equal pieces. Refining a dyadic sum changes it by at most
`C (t - s) ^ γ 2 ^ (n (1 - γ))`, so the dyadic sums converge and their limit `sewing Ξ s t` is
within `C / (1 - 2 ^ (1 - γ)) * (t - s) ^ γ` of `Ξ s t`. Riemann sums along arbitrary partitions are
controlled by Young's point-removal argument: in a partition with `n` pieces some interior point has
neighbours at distance at most `2 (t - s) / (n - 1)`, and removing it costs a defect. This bounds
every Riemann sum of `Ξ` over `[s, t]` by `K (t - s) ^ γ` from `Ξ s t`, which shows that the
Riemann sums converge to `sewing Ξ s t` as the mesh tends to zero, and hence that `sewing Ξ` is
additive.

## Main declarations

* `TauCeti.dyadicSum`: the Riemann sum of `Ξ` over the dyadic partition of `[s, t]` into `2 ^ n`
  pieces; `TauCeti.dyadicSum_succ` splits it at the midpoint.
* `TauCeti.sewing`: the limit of the dyadic sums.
* `TauCeti.HasPartitionLimit`: Riemann sums along partitions converge as the mesh tends to zero;
  for `s ≤ t`, `TauCeti.HasPartitionLimit.tendsto_dyadicSum` and
  `TauCeti.HasPartitionLimit.sewing_eq`: a partition limit is the limit of the dyadic sums, so it is
  `sewing Ξ s t`, and `TauCeti.HasPartitionLimit.unique`: it is unique.
* `TauCeti.tendsto_dyadicSum_sewing`: the dyadic sums converge to `sewing Ξ s t`.
* `TauCeti.norm_sewing_sub_le`: `‖sewing Ξ s t - Ξ s t‖ ≤ C / (1 - 2 ^ (1 - γ)) * (t - s) ^ γ`.
* `TauCeti.hasPartitionLimit_sewing`: Riemann sums along partitions of vanishing mesh converge to
  `sewing Ξ s t`.
* `TauCeti.sewing_add_adjacent`: `sewing Ξ` is additive.
* `TauCeti.eq_sewing`: every additive map within `O((t - s) ^ γ)`, `γ > 1`, of `Ξ` is
  `sewing Ξ`.

## References

* P. K. Friz and M. Hairer, *A Course on Rough Paths*, 2nd ed., Springer, 2020, Lemma 4.2.
* P. K. Friz and N. B. Victoir, *Multidimensional Stochastic Processes as Rough Paths*, Cambridge
  University Press, 2010, Theorem 6.8 and its proof (the constant `1 / (1 - 2 ^ (1 - γ))`).
* L. C. Young, *An inequality of the Hölder type, connected with Stieltjes integration*,
  Acta Math. 67 (1936), for the point-removal argument.
* The Lean project CKMA (https://github.com/bjbraams/lean-CKMA, Apache 2.0) contains an earlier
  formalization of the Hölder form of the sewing lemma, `CKMA/Analysis/RoughPath/Sewing.lean`;
  this file was written independently of it.
-/

public section

noncomputable section

open Filter Topology Finset

namespace TauCeti

section Dyadic

variable {E : Type*} [AddCommMonoid E]

/-- The dyadic Riemann sum of a two-parameter map `Ξ` over `[s, t]` with `2 ^ n` pieces. -/
def dyadicSum (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) : E :=
  ∑ k ∈ range (2 ^ n), Ξ (s + k * (t - s) / 2 ^ n) (s + (k + 1) * (t - s) / 2 ^ n)

/-- `dyadicSum Ξ s t n` is the sum of `Ξ` over the `2 ^ n` consecutive dyadic pieces of `[s, t]`. -/
theorem dyadicSum_def (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) :
    dyadicSum Ξ s t n =
      ∑ k ∈ range (2 ^ n), Ξ (s + k * (t - s) / 2 ^ n) (s + (k + 1) * (t - s) / 2 ^ n) := by
  rw [dyadicSum]

/-- The dyadic sum at level `0` is the germ itself. -/
@[simp]
theorem dyadicSum_zero (Ξ : ℝ → ℝ → E) (s t : ℝ) : dyadicSum Ξ s t 0 = Ξ s t := by
  simp [dyadicSum]

/-- The dyadic sum at level `n + 1` is the sum of the dyadic sums at level `n` over the two
halves of the interval. -/
theorem dyadicSum_succ (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) :
    dyadicSum Ξ s t (n + 1) =
      dyadicSum Ξ s ((s + t) / 2) n + dyadicSum Ξ ((s + t) / 2) t n := by
  rw [dyadicSum, pow_succ, mul_two, sum_range_add]
  congr 1 <;> refine sum_congr rfl fun k _ ↦ ?_ <;> congr 1 <;> push_cast <;> field_simp <;> ring

/-- The sewing map: the limit of the dyadic Riemann sums of `Ξ` over `[s, t]`. It is a junk value
when the dyadic sums do not converge. -/
def sewing [TopologicalSpace E] (Ξ : ℝ → ℝ → E) (s t : ℝ) : E :=
  limUnder atTop (dyadicSum Ξ s t)

/-- `sewing Ξ s t` is the limit of the dyadic sums of `Ξ`, as a junk value if they diverge. -/
theorem sewing_def [TopologicalSpace E] (Ξ : ℝ → ℝ → E) (s t : ℝ) :
    sewing Ξ s t = limUnder atTop (dyadicSum Ξ s t) := by
  rw [sewing]

end Dyadic

variable {E : Type*} [NormedAddCommGroup E]

/-- Riemann sums of `Ξ` along partitions `s = u 0 ≤ ⋯ ≤ u n = t` of `[s, t]` tend to `I` as the
mesh tends to zero. When `t < s` there are no partitions and every `I` is a limit. -/
def HasPartitionLimit (Ξ : ℝ → ℝ → E) (s t : ℝ) (I : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u → u 0 = s →
    u (Fin.last n) = t → (∀ i : Fin n, u i.succ - u i.castSucc < δ) →
      ‖(∑ i : Fin n, Ξ (u i.castSucc) (u i.succ)) - I‖ < ε

/-- `HasPartitionLimit Ξ s t I` unfolded: for every `ε > 0` there is a mesh `δ > 0` below which
every Riemann sum of `Ξ` along a partition of `[s, t]` is within `ε` of `I`. -/
theorem hasPartitionLimit_iff {Ξ : ℝ → ℝ → E} {s t : ℝ} {I : E} :
    HasPartitionLimit Ξ s t I ↔
      ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u → u 0 = s →
        u (Fin.last n) = t → (∀ i : Fin n, u i.succ - u i.castSucc < δ) →
          ‖(∑ i : Fin n, Ξ (u i.castSucc) (u i.succ)) - I‖ < ε := by
  rw [HasPartitionLimit]

/-! ### Riemann sums along list partitions

A partition of `[s, t]` is represented in the proofs by a sorted list of reals beginning with `s`
and ending with `t`; repeated points are allowed, which makes common refinements easy to form by
merging. -/

section Partition

variable {F : Type*} [AddCommMonoid F]

/-- The Riemann sum of `Ξ` along the consecutive points of a list. -/
private def rsum (Ξ : ℝ → ℝ → F) : List ℝ → F
  | [] => 0
  | [_] => 0
  | x :: y :: l => Ξ x y + rsum Ξ (y :: l)

@[simp] private theorem rsum_nil (Ξ : ℝ → ℝ → F) : rsum Ξ [] = 0 := rfl

@[simp] private theorem rsum_singleton (Ξ : ℝ → ℝ → F) (x : ℝ) : rsum Ξ [x] = 0 := rfl

@[simp] private theorem rsum_cons_cons (Ξ : ℝ → ℝ → F) (x y : ℝ) (l : List ℝ) :
    rsum Ξ (x :: y :: l) = Ξ x y + rsum Ξ (y :: l) := rfl

private theorem rsum_append_cons (Ξ : ℝ → ℝ → F) (l₁ : List ℝ) (x : ℝ) (l₂ : List ℝ) :
    rsum Ξ (l₁ ++ x :: l₂) = rsum Ξ (l₁ ++ [x]) + rsum Ξ (x :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₁ with
    | nil => simp
    | cons b l₁ => simp only [List.cons_append, rsum_cons_cons] at ih ⊢; rw [ih, add_assoc]

private theorem rsum_ofFn (Ξ : ℝ → ℝ → F) {n : ℕ} (u : Fin (n + 1) → ℝ) :
    rsum Ξ (List.ofFn u) = ∑ i : Fin n, Ξ (u i.castSucc) (u i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    simp_rw [← Fin.succ_castSucc]
    rw [← ih (fun i ↦ u i.succ), List.ofFn_succ]
    simp

end Partition

/-- `l` is a partition of `[s, t]`: a sorted list beginning with `s` and ending with `t`. -/
private def IsPart (l : List ℝ) (s t : ℝ) : Prop :=
  l.Pairwise (· ≤ ·) ∧ l.head? = some s ∧ l.getLast? = some t

private theorem IsPart.mem_Icc {l : List ℝ} {s t z : ℝ} (hl : IsPart l s t) (hz : z ∈ l) :
    s ≤ z ∧ z ≤ t := by
  obtain ⟨hp, hs, ht⟩ := hl
  obtain ⟨l', rfl⟩ := List.head?_eq_some_iff.1 hs
  obtain ⟨l'', hl''⟩ := List.getLast?_eq_some_iff.1 ht
  constructor
  · rcases List.mem_cons.1 hz with rfl | hz
    · exact le_rfl
    · exact List.rel_of_pairwise_cons hp hz
  · rw [hl''] at hp hz
    rcases List.mem_append.1 hz with hz | hz
    · exact (List.pairwise_append.1 hp).2.2 z hz t (by simp)
    · simp_all

private theorem IsPart.le {l : List ℝ} {s t : ℝ} (hl : IsPart l s t) : s ≤ t := by
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.1 hl.2.2
  exact (hl.mem_Icc (z := t) (by simp [hl'])).1

private theorem IsPart.singleton_iff {x s t : ℝ} : IsPart [x] s t ↔ x = s ∧ x = t := by
  simp [IsPart]

/-- Dropping the first point of a partition of `[s, t]`, which is `s`. -/
private theorem IsPart.cons_cons {x y s t : ℝ} {l : List ℝ} (h : IsPart (x :: y :: l) s t) :
    x = s ∧ IsPart (y :: l) y t :=
  ⟨by simpa using h.2.1, h.1.of_cons, by simp, by simpa using h.2.2⟩

private theorem isPart_of_mem {l : List ℝ} {s t : ℝ} (hp : l.Pairwise (· ≤ ·)) (hs : s ∈ l)
    (ht : t ∈ l) (h : ∀ z ∈ l, s ≤ z ∧ z ≤ t) : IsPart l s t := by
  refine ⟨hp, ?_, ?_⟩
  · obtain _ | ⟨x, l'⟩ := l
    · simp at hs
    · have : x ≤ s := by
        rcases List.mem_cons.1 hs with rfl | hs
        · exact le_rfl
        · exact List.rel_of_pairwise_cons hp hs
      simp [le_antisymm this (h x (by simp)).1]
  · obtain rfl | ⟨l', x, rfl⟩ := List.eq_nil_or_concat l
    · simp at hs
    · simp only [List.concat_eq_append] at hp ht h ⊢
      have : t ≤ x := by
        rcases List.mem_append.1 ht with ht | ht
        · exact (List.pairwise_append.1 hp).2.2 t ht x (by simp)
        · simp_all
      simp [le_antisymm (h x (by simp)).2 this]

private theorem isPart_ofFn {n : ℕ} {u : Fin (n + 1) → ℝ} (hu : Monotone u) :
    IsPart (List.ofFn u) (u 0) (u (Fin.last n)) := by
  refine ⟨List.pairwise_ofFn.2 fun i j hij ↦ hu hij.le, by simp [List.ofFn_succ], ?_⟩
  rw [List.getLast?_eq_some_getLast (by simp), List.getLast_ofFn]
  exact congrArg _ (congrArg u (Fin.ext (by simp)))

/-- Gluing a partition of `[s, u]` to a partition of `[u, t]`. -/
private theorem IsPart.append {l₁ l₂ : List ℝ} {s u t : ℝ} (h₁ : IsPart (l₁ ++ [u]) s u)
    (h₂ : IsPart (u :: l₂) u t) : IsPart (l₁ ++ u :: l₂) s t := by
  refine isPart_of_mem ?_ ?_ ?_ ?_
  · rw [List.pairwise_append]
    refine ⟨(List.pairwise_append.1 h₁.1).1, h₂.1, fun x hx y hy ↦ ?_⟩
    exact ((h₁.mem_Icc (z := x) (by simp [hx])).2).trans (h₂.mem_Icc hy).1
  · have := List.mem_of_mem_head? h₁.2.1
    simp only [List.mem_append, List.mem_singleton] at this
    simp only [List.mem_append, List.mem_cons]
    tauto
  · exact List.mem_append_right _ (List.mem_of_mem_getLast? h₂.2.2)
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · have := h₁.mem_Icc (z := z) (by simp [hz])
      exact ⟨this.1, this.2.trans h₂.le⟩
    · have := h₂.mem_Icc hz
      exact ⟨h₁.le.trans this.1, this.2⟩

/-- The dyadic partition of `[s, t]` into `2 ^ n` pieces. -/
private def dyadicPart (s t : ℝ) (n : ℕ) : List ℝ :=
  List.ofFn fun k : Fin (2 ^ n + 1) ↦ s + k * (t - s) / 2 ^ n

private theorem monotone_dyadic {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    Monotone fun k : Fin (2 ^ n + 1) ↦ s + k * (t - s) / 2 ^ n := fun i j hij ↦ by
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  have : 0 ≤ t - s := by linarith
  dsimp only
  gcongr

private theorem dyadic_last (s t : ℝ) (n : ℕ) :
    s + ((Fin.last (2 ^ n) : ℕ) : ℝ) * (t - s) / 2 ^ n = t := by
  rw [Fin.val_last]
  push_cast
  field_simp
  ring

private theorem dyadic_zero (s t : ℝ) (n : ℕ) :
    s + (((0 : Fin (2 ^ n + 1)) : ℕ) : ℝ) * (t - s) / 2 ^ n = s := by
  simp

/-- Consecutive dyadic points of `[s, t]` at level `n` are `(t - s) / 2 ^ n` apart. -/
private theorem dyadic_gap (s t : ℝ) (n k : ℕ) :
    (s + ((k + 1 : ℕ) : ℝ) * (t - s) / 2 ^ n) - (s + (k : ℝ) * (t - s) / 2 ^ n) =
      (t - s) / 2 ^ n := by
  push_cast
  ring

private theorem isPart_dyadicPart {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    IsPart (dyadicPart s t n) s t := by
  simpa only [dyadicPart, dyadic_zero, dyadic_last] using isPart_ofFn (monotone_dyadic hst n)

private theorem rsum_dyadicPart {F : Type*} [AddCommMonoid F] (Ξ : ℝ → ℝ → F) (s t : ℝ)
    (n : ℕ) : rsum Ξ (dyadicPart s t n) = dyadicSum Ξ s t n := by
  rw [dyadicPart, rsum_ofFn, dyadicSum,
    ← Fin.sum_univ_eq_sum_range (fun k ↦ Ξ (s + k * (t - s) / 2 ^ n)
      (s + (k + 1) * (t - s) / 2 ^ n))]
  simp

private theorem isChain_dyadicPart (s t : ℝ) (n : ℕ) :
    (dyadicPart s t n).IsChain fun x y ↦ y - x ≤ (t - s) / 2 ^ n := by
  refine List.isChain_ofFn.2 fun i hi ↦ ?_
  simpa only [Fin.val_mk] using (dyadic_gap s t n i).le

/-! ### Young's point-removal bound -/

/-- The sum, over the interior points of a list, of the distance between the two neighbours of
the point. -/
private def gapSum : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | p :: y :: q :: l => (q - p) + gapSum (y :: q :: l)

private theorem gapSum_le {x y t : ℝ} {l : List ℝ} (hp : (x :: y :: l).Pairwise (· ≤ ·))
    (ht : (x :: y :: l).getLast? = some t) : gapSum (x :: y :: l) ≤ (t - x) + (t - y) := by
  induction l generalizing x y with
  | nil =>
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ht
    subst ht
    simp [gapSum, List.rel_of_pairwise_cons hp (List.mem_singleton_self y)]
  | cons q l ih =>
    have h := ih hp.of_cons (by simpa using ht)
    rw [gapSum]
    linarith

/-- Some interior point of a partition has neighbours at distance at most the average gap. -/
private theorem exists_gap_le (p y q : ℝ) (l : List ℝ) :
    ∃ A p' y' q' B, p :: y :: q :: l = A ++ p' :: y' :: q' :: B ∧
      (q' - p') * ((l.length : ℝ) + 1) ≤ gapSum (p :: y :: q :: l) := by
  induction l generalizing p y q with
  | nil => exact ⟨[], p, y, q, [], rfl, by simp [gapSum]⟩
  | cons r l ih =>
    obtain ⟨A, p', y', q', B, hl, hg⟩ := ih y q r
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hg ⊢
    rw [gapSum]
    set G := gapSum (y :: q :: r :: l)
    set m : ℝ := (l.length : ℝ) + 1
    by_cases h : (q - p) * (m + 1) ≤ q - p + G
    · exact ⟨[], p, y, q, r :: l, rfl, h⟩
    · refine ⟨p :: A, p', y', q', B, by simp [hl], ?_⟩
      have hm : 0 < m := by positivity
      have hlt : q' - p' < q - p := by
        by_contra hc
        push Not at hc
        nlinarith [mul_le_mul_of_nonneg_right hc hm.le]
      linarith

variable {a b γ C : ℝ} {Ξ : ℝ → ℝ → E}

private theorem eq_zero_of_defect (hγ : 0 < γ)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {x : ℝ} (ha : a ≤ x) (hb : x ≤ b) : Ξ x x = 0 := by
  simpa [Real.zero_rpow hγ.ne'] using hδ x x x ha le_rfl le_rfl hb

/-- Removing an interior point `y` from a partition, with neighbours `p` and `q`, changes its
Riemann sum by a defect of `Ξ`, at most `C (q - p) ^ γ`. -/
private theorem norm_rsum_erase_le
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {A B : List ℝ} {p y q s t : ℝ} (hl : IsPart (A ++ p :: y :: q :: B) s t) (ha : a ≤ s)
    (hb : t ≤ b) :
    IsPart (A ++ p :: q :: B) s t ∧
      ‖rsum Ξ (A ++ p :: y :: q :: B) - rsum Ξ (A ++ p :: q :: B)‖ ≤ C * (q - p) ^ γ := by
  have hsub : List.Sublist (A ++ p :: q :: B) (A ++ p :: y :: q :: B) :=
    List.Sublist.append_left (List.Sublist.cons_cons p (List.sublist_cons_self y _)) A
  refine ⟨⟨hl.1.sublist hsub, ?_, ?_⟩, ?_⟩
  · rw [← hl.2.1]; cases A <;> simp
  · rw [← hl.2.2]; simp
  have h3 := hl.1.sublist (List.sublist_append_right A _)
  have hpy : p ≤ y := List.rel_of_pairwise_cons h3 (by simp)
  have hyq : y ≤ q := List.rel_of_pairwise_cons h3.of_cons (by simp)
  have hp := hl.mem_Icc (z := p) (by simp)
  have hq := hl.mem_Icc (z := q) (by simp)
  have hdiff : rsum Ξ (A ++ p :: y :: q :: B) - rsum Ξ (A ++ p :: q :: B) =
      -(Ξ p q - Ξ p y - Ξ y q) := by
    rw [rsum_append_cons _ A p (y :: q :: B), rsum_append_cons _ A p (q :: B)]
    simp only [rsum_cons_cons]
    abel
  rw [hdiff, norm_neg]
  exact hδ p y q (ha.trans hp.1) hpy hyq (hq.2.trans hb)

/-- The cost of removing a point whose neighbours are at distance at most `2 (t - s) / (n + 1)`. -/
private theorem rpow_le_of_mul_le {n : ℕ} {p q s t : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) (hpq : p ≤ q)
    (hst : s ≤ t) (h : (q - p) * ((n : ℝ) + 1) ≤ 2 * (t - s)) :
    C * (q - p) ^ γ ≤ C * 2 ^ γ * (t - s) ^ γ * (((n : ℝ) + 1) ^ γ)⁻¹ := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hqp : q - p ≤ 2 * (t - s) / ((n : ℝ) + 1) := by rwa [le_div_iff₀ hn]
  calc C * (q - p) ^ γ ≤ C * (2 * (t - s) / ((n : ℝ) + 1)) ^ γ := by gcongr
    _ = C * 2 ^ γ * (t - s) ^ γ * (((n : ℝ) + 1) ^ γ)⁻¹ := by
        rw [Real.div_rpow (by linarith) hn.le, Real.mul_rpow (by norm_num) (by linarith)]
        ring

private theorem norm_rsum_sub_le_aux (hγ : 0 < γ) (hC : 0 ≤ C)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    (n : ℕ) : ∀ (l : List ℝ) (s t : ℝ), l.length = n + 2 → IsPart l s t → a ≤ s → t ≤ b →
      ‖rsum Ξ l - Ξ s t‖ ≤
        C * 2 ^ γ * (t - s) ^ γ * ∑ k ∈ range n, (((k : ℝ) + 1) ^ γ)⁻¹ := by
  induction n with
  | zero =>
    rintro (_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩) s t hlen hl ha hb <;> simp at hlen
    obtain ⟨rfl, hy⟩ := hl.cons_cons
    obtain ⟨-, rfl⟩ := IsPart.singleton_iff.1 hy
    simp
  | succ n ih =>
    rintro (_ | ⟨p₀, _ | ⟨y₀, _ | ⟨q₀, l₀⟩⟩⟩) s t hlen hl ha hb
    · simp at hlen
    · simp at hlen
    · simp at hlen
    replace hlen : l₀.length = n := by simpa using hlen
    obtain ⟨A, p, y, q, B, hl', hg⟩ := exists_gap_le p₀ y₀ q₀ l₀
    have hgap := gapSum_le hl.1 (hl.2.2)
    have hs : p₀ = s := hl.cons_cons.1
    have hy₀ : s ≤ y₀ := (hl.mem_Icc (z := y₀) (by simp)).1
    rw [hlen] at hg
    rw [hl'] at hl ⊢
    -- remove the interior point `y`
    obtain ⟨hl₂, hrem₁⟩ := norm_rsum_erase_le hδ hl ha hb
    have hlen₂ : (A ++ p :: q :: B).length = n + 2 := by
      have := congrArg List.length hl'
      simp only [List.length_cons, List.length_append] at this hlen ⊢
      omega
    have hrem := ih _ s t hlen₂ hl₂ ha hb
    have hpq : p ≤ q :=
      List.rel_of_pairwise_cons (hl.1.sublist (List.sublist_append_right A _)) (by simp)
    have hstep := hrem₁.trans (rpow_le_of_mul_le hγ hC hpq hl₂.le (by linarith))
    calc ‖rsum Ξ (A ++ p :: y :: q :: B) - Ξ s t‖
        ≤ ‖rsum Ξ (A ++ p :: y :: q :: B) - rsum Ξ (A ++ p :: q :: B)‖ +
            ‖rsum Ξ (A ++ p :: q :: B) - Ξ s t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * 2 ^ γ * (t - s) ^ γ * (((n : ℝ) + 1) ^ γ)⁻¹ +
            C * 2 ^ γ * (t - s) ^ γ * ∑ k ∈ range n, (((k : ℝ) + 1) ^ γ)⁻¹ :=
          add_le_add hstep hrem
      _ = C * 2 ^ γ * (t - s) ^ γ * ∑ k ∈ range (n + 1), (((k : ℝ) + 1) ^ γ)⁻¹ := by
          rw [sum_range_succ]
          ring

/-- The constant of Young's maximal inequality: `C 2 ^ γ ζ(γ)`. -/
private def youngConst (C γ : ℝ) : ℝ :=
  C * 2 ^ γ * ∑' k : ℕ, (((k : ℝ) + 1) ^ γ)⁻¹

private theorem summable_youngConst {γ : ℝ} (hγ : 1 < γ) :
    Summable fun k : ℕ ↦ (((k : ℝ) + 1) ^ γ)⁻¹ := by
  simpa using (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hγ)

private theorem youngConst_nonneg (hC : 0 ≤ C) : 0 ≤ youngConst C γ := by
  unfold youngConst
  have : 0 ≤ ∑' k : ℕ, (((k : ℝ) + 1) ^ γ)⁻¹ := tsum_nonneg fun k ↦ by positivity
  positivity

/-- **Young's maximal inequality**: every Riemann sum of `Ξ` over `[s, t]` is within
`K (t - s) ^ γ` of `Ξ s t`. -/
private theorem norm_rsum_sub_le (hγ : 1 < γ) (hC : 0 ≤ C)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {l : List ℝ} {s t : ℝ} (hl : IsPart l s t) (ha : a ≤ s) (hb : t ≤ b) :
    ‖rsum Ξ l - Ξ s t‖ ≤ youngConst C γ * (t - s) ^ γ := by
  obtain _ | ⟨x, _ | ⟨y, l⟩⟩ := l
  · simp [IsPart] at hl
  · obtain ⟨rfl, rfl⟩ := IsPart.singleton_iff.1 hl
    rw [rsum_singleton, eq_zero_of_defect (by linarith) hδ ha hb]
    simp only [sub_self, norm_zero]
    exact mul_nonneg (youngConst_nonneg hC) (Real.rpow_nonneg le_rfl _)
  · refine (norm_rsum_sub_le_aux (by linarith) hC hδ l.length _ s t (by simp) hl ha hb).trans ?_
    rw [youngConst, mul_right_comm]
    have := hl.le
    gcongr
    exact (summable_youngConst hγ).sum_le_tsum _ fun k _ ↦ by positivity

/-- Refining a partition `P` to `Q` changes its Riemann sum by at most `K ∑ (Δ P) ^ γ`. -/
private theorem norm_rsum_sub_rsum_le (hγ : 1 < γ) (hC : 0 ≤ C)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {P : List ℝ} : ∀ {Q : List ℝ} {s t : ℝ}, IsPart P s t → IsPart Q s t → List.Sublist P Q →
      a ≤ s → t ≤ b →
      ‖rsum Ξ Q - rsum Ξ P‖ ≤ youngConst C γ * rsum (fun x y ↦ (y - x) ^ γ) P := by
  induction P with
  | nil => intro Q s t hP; simp [IsPart] at hP
  | cons x P ih =>
    intro Q s t hP hQ hPQ ha hb
    obtain _ | ⟨y, P⟩ := P
    · obtain ⟨rfl, rfl⟩ := IsPart.singleton_iff.1 hP
      have := norm_rsum_sub_le hγ hC hδ hQ ha hb
      rw [eq_zero_of_defect (by linarith) hδ ha hb, sub_self,
        Real.zero_rpow (by linarith), mul_zero] at this
      simpa using this
    · obtain ⟨rfl, hyP⟩ := hP.cons_cons
      obtain ⟨Q', rfl⟩ := List.head?_eq_some_iff.1 hQ.2.1
      obtain ⟨r₁, r₂, rfl, hy, hP'⟩ := List.cons_sublist_iff.1 (List.cons_sublist_cons.1 hPQ)
      obtain ⟨Q₁, Q₂, rfl⟩ := List.append_of_mem hy
      have hP₂ : List.Sublist (y :: P) (y :: (Q₂ ++ r₂)) :=
        (hP'.trans (List.sublist_append_right Q₂ r₂)).cons_cons y
      have hQ' : x :: (Q₁ ++ y :: Q₂ ++ r₂) = (x :: Q₁) ++ y :: (Q₂ ++ r₂) := by simp
      rw [hQ'] at hQ ⊢
      have hA : IsPart (x :: Q₁ ++ [y]) x y := by
        refine ⟨hQ.1.sublist ?_, by simp, List.getLast?_concat⟩
        exact List.Sublist.append_left (List.singleton_sublist.2 (by simp)) _
      have hB : IsPart (y :: (Q₂ ++ r₂)) y t := by
        refine ⟨hQ.1.sublist (List.sublist_append_right _ _), by simp, ?_⟩
        rw [← hQ.2.2, List.getLast?_append, List.getLast?_cons, Option.some_or]
      have hxy := hA.le
      have h₁ := norm_rsum_sub_le hγ hC hδ hA ha (hyP.le.trans hb)
      have h₂ := ih hyP hB hP₂ (ha.trans hxy) hb
      rw [rsum_append_cons, rsum_cons_cons, rsum_cons_cons]
      calc ‖rsum Ξ (x :: Q₁ ++ [y]) + rsum Ξ (y :: (Q₂ ++ r₂)) - (Ξ x y + rsum Ξ (y :: P))‖
          = ‖(rsum Ξ (x :: Q₁ ++ [y]) - Ξ x y) + (rsum Ξ (y :: (Q₂ ++ r₂)) - rsum Ξ (y :: P))‖ := by
            congr 1
            abel
        _ ≤ youngConst C γ * (y - x) ^ γ +
              youngConst C γ * rsum (fun x y ↦ (y - x) ^ γ) (y :: P) :=
            (norm_add_le _ _).trans (add_le_add h₁ h₂)
        _ = _ := by ring

/-- The sum of `(Δ l) ^ γ` over a partition of mesh at most `δ` is at most `δ ^ (γ - 1) (t - s)`. -/
private theorem rsum_rpow_le {δ : ℝ} (hγ : 1 ≤ γ) {l : List ℝ} :
    ∀ {s t : ℝ}, IsPart l s t → (l.IsChain fun x y ↦ y - x ≤ δ) →
      rsum (fun x y ↦ (y - x) ^ γ) l ≤ δ ^ (γ - 1) * (t - s) := by
  induction l with
  | nil => intro s t hl; simp [IsPart] at hl
  | cons x l ih =>
    intro s t hl hc
    obtain _ | ⟨y, l⟩ := l
    · obtain ⟨rfl, rfl⟩ := IsPart.singleton_iff.1 hl
      simp
    · obtain ⟨rfl, hyl⟩ := hl.cons_cons
      have hxy : x ≤ y := List.rel_of_pairwise_cons hl.1 (List.mem_cons_self ..)
      have hgap : y - x ≤ δ := (List.isChain_cons_cons.1 hc).1
      have h := ih hyl (List.isChain_cons_cons.1 hc).2
      have hpow : (y - x) ^ γ ≤ δ ^ (γ - 1) * (y - x) := by
        have hd : 0 ≤ y - x := by linarith
        calc (y - x) ^ γ = (y - x) ^ (γ - 1) * (y - x) := by
              rw [← Real.rpow_add_one' hd (by linarith)]
              ring_nf
          _ ≤ δ ^ (γ - 1) * (y - x) := by gcongr
      rw [rsum_cons_cons]
      linarith

/-! ### Dyadic sums and the sewing map -/

/-- A quantity that splits at the midpoint decays geometrically along the dyadic levels. -/
private theorem norm_le_of_halves {K : ℝ} {G : ℕ → ℝ → ℝ → E}
    (h0 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖G 0 s t‖ ≤ K * (t - s) ^ γ)
    (hsucc : ∀ n s t, a ≤ s → s ≤ t → t ≤ b →
      G (n + 1) s t = G n s ((s + t) / 2) + G n ((s + t) / 2) t)
    (n : ℕ) : ∀ {s t : ℝ}, a ≤ s → s ≤ t → t ≤ b →
      ‖G n s t‖ ≤ K * (t - s) ^ γ * (2 ^ (1 - γ)) ^ n := by
  induction n with
  | zero => intro s t hs hst ht; simpa using h0 s t hs hst ht
  | succ n ih =>
    intro s t hs hst ht
    rw [hsucc n s t hs hst ht]
    have h₁ := ih hs (by linarith) (by linarith : (s + t) / 2 ≤ b)
    have h₂ := ih (by linarith : a ≤ (s + t) / 2) (by linarith) ht
    rw [show (s + t) / 2 - s = (t - s) / 2 by ring] at h₁
    rw [show t - (s + t) / 2 = (t - s) / 2 by ring] at h₂
    have hsplit : 2 * ((t - s) / 2) ^ γ = (t - s) ^ γ * 2 ^ (1 - γ) := by
      rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one]
      field_simp
    calc ‖G n s ((s + t) / 2) + G n ((s + t) / 2) t‖
        ≤ K * ((t - s) / 2) ^ γ * (2 ^ (1 - γ)) ^ n + K * ((t - s) / 2) ^ γ * (2 ^ (1 - γ)) ^ n :=
          (norm_add_le _ _).trans (add_le_add h₁ h₂)
      _ = K * (2 * ((t - s) / 2) ^ γ) * (2 ^ (1 - γ)) ^ n := by ring
      _ = K * (t - s) ^ γ * (2 ^ (1 - γ)) ^ (n + 1) := by rw [hsplit, pow_succ]; ring

private theorem norm_dyadicSum_succ_sub_le
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    (n : ℕ) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖dyadicSum Ξ s t (n + 1) - dyadicSum Ξ s t n‖ ≤ C * (t - s) ^ γ * (2 ^ (1 - γ)) ^ n := by
  refine norm_le_of_halves (G := fun n s t ↦ dyadicSum Ξ s t (n + 1) - dyadicSum Ξ s t n)
    (fun s t hs hst ht ↦ ?_) (fun n s t _ _ _ ↦ ?_) n hs hst ht
  · have h := hδ s ((s + t) / 2) t hs (by linarith) (by linarith) ht
    simp only [zero_add, dyadicSum_succ, dyadicSum_zero]
    rw [← norm_neg]
    convert h using 2
    abel
  · rw [dyadicSum_succ Ξ s t (n + 1), dyadicSum_succ Ξ s t n]
    abel

private theorem defect_le_max
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ) :
    ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ max C 0 * (t - s) ^ γ :=
  fun s u t hs hsu hut ht ↦ (hδ s u t hs hsu hut ht).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))

private theorem two_rpow_one_sub_lt_one (hγ : 1 < γ) : (2 : ℝ) ^ (1 - γ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)

private theorem tendsto_div_two_pow (c : ℝ) : Tendsto (fun n : ℕ ↦ c / 2 ^ n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

private theorem tendsto_rpow_div_pow (hγ : 1 < γ) (c : ℝ) :
    Tendsto (fun n : ℕ ↦ (c / 2 ^ n) ^ (γ - 1)) atTop (𝓝 0) := by
  simpa [Function.comp_def, Real.zero_rpow (by linarith : γ - 1 ≠ 0)] using
    (Real.continuousAt_rpow_const 0 (γ - 1) (Or.inr (by linarith))).tendsto.comp
      (tendsto_div_two_pow c)

/-- If the defect of `Ξ` is bounded by `C (t - s) ^ γ` with `γ > 1`, the dyadic sums of `Ξ`
converge to `sewing Ξ s t`. -/
theorem tendsto_dyadicSum_sewing [CompleteSpace E] (hγ : 1 < γ)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Tendsto (dyadicSum Ξ s t) atTop (𝓝 (sewing Ξ s t)) := by
  have hr := two_rpow_one_sub_lt_one hγ
  have : CauchySeq (dyadicSum Ξ s t) :=
    cauchySeq_of_le_geometric _ (C * (t - s) ^ γ) hr fun n ↦ by
      rw [dist_comm, dist_eq_norm]
      exact norm_dyadicSum_succ_sub_le hδ n hs hst ht
  rw [sewing_def]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete this)

/-- **The sewing lemma**, error bound: if the defect of `Ξ` is bounded by `C (t - s) ^ γ` with
`γ > 1`, then `sewing Ξ s t` is within `C / (1 - 2 ^ (1 - γ)) * (t - s) ^ γ` of `Ξ s t`. -/
theorem norm_sewing_sub_le [CompleteSpace E] (hγ : 1 < γ)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖sewing Ξ s t - Ξ s t‖ ≤ C / (1 - 2 ^ (1 - γ)) * (t - s) ^ γ := by
  have hr := two_rpow_one_sub_lt_one hγ
  have h := dist_le_of_le_geometric_of_tendsto₀ _ (C * (t - s) ^ γ) hr (fun n ↦ by
      rw [dist_comm, dist_eq_norm]
      exact norm_dyadicSum_succ_sub_le hδ n hs hst ht)
    (tendsto_dyadicSum_sewing hγ hδ hs hst ht)
  rw [dyadicSum_zero, dist_comm, dist_eq_norm] at h
  exact h.trans_eq (by ring)

/-- A Riemann sum of `Ξ` along a partition of `[s, t]` of mesh at most `δ` is close to the dyadic
sums of `Ξ`: compare both with their common refinement. -/
private theorem norm_rsum_sub_dyadicSum_le (hγ : 1 < γ) (hC : 0 ≤ C)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {δ : ℝ} {l : List ℝ} {s t : ℝ} (hl : IsPart l s t) (hmesh : l.IsChain fun x y ↦ y - x ≤ δ)
    (ha : a ≤ s) (hb : t ≤ b) (n : ℕ) :
    ‖rsum Ξ l - dyadicSum Ξ s t n‖ ≤ youngConst C γ * (δ ^ (γ - 1) * (t - s)) +
      youngConst C γ * (((t - s) / 2 ^ n) ^ (γ - 1) * (t - s)) := by
  have hK := youngConst_nonneg (γ := γ) hC
  have hD := isPart_dyadicPart hl.le n
  set M := (l ++ dyadicPart s t n).mergeSort fun x y ↦ decide (x ≤ y)
  have hsub : ∀ {P : List ℝ}, P.Pairwise (· ≤ ·) → List.Sublist P (l ++ dyadicPart s t n) →
      List.Sublist P M := fun hP h ↦
    List.sublist_mergeSort (fun _ _ _ ↦ by simpa using le_trans)
      (fun x y ↦ by simpa using le_total x y) (by simpa using hP) h
  have hM : IsPart M s t := by
    refine isPart_of_mem (by simpa using List.pairwise_mergeSort' (· ≤ ·) _) ?_ ?_
      fun z hz ↦ ?_
    · exact List.mem_mergeSort.2 (List.mem_append_left _ (List.mem_of_mem_head? hl.2.1))
    · exact List.mem_mergeSort.2 (List.mem_append_left _ (List.mem_of_mem_getLast? hl.2.2))
    · rcases List.mem_append.1 (List.mem_mergeSort.1 hz) with hz | hz
      · exact hl.mem_Icc hz
      · exact hD.mem_Icc hz
  have h₁ := norm_rsum_sub_rsum_le hγ hC hδ hl hM (hsub hl.1 (List.sublist_append_left _ _)) ha hb
  have h₂ := norm_rsum_sub_rsum_le hγ hC hδ hD hM (hsub hD.1 (List.sublist_append_right _ _))
    ha hb
  rw [rsum_dyadicPart] at h₂
  calc ‖rsum Ξ l - dyadicSum Ξ s t n‖
      = ‖-(rsum Ξ M - rsum Ξ l) + (rsum Ξ M - dyadicSum Ξ s t n)‖ := by congr 1; abel
    _ ≤ ‖rsum Ξ M - rsum Ξ l‖ + ‖rsum Ξ M - dyadicSum Ξ s t n‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ _ := by
        gcongr
        · exact h₁.trans (mul_le_mul_of_nonneg_left (rsum_rpow_le hγ.le hl hmesh) hK)
        · exact h₂.trans (mul_le_mul_of_nonneg_left
            (rsum_rpow_le hγ.le hD (isChain_dyadicPart s t n)) hK)

/-- A Riemann sum of `Ξ` along a partition of `[s, t]` of mesh at most `δ` is within
`K δ ^ (γ - 1) (t - s)` of `sewing Ξ s t`. -/
private theorem norm_rsum_sub_sewing_le [CompleteSpace E] (hγ : 1 < γ) (hC : 0 ≤ C)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {δ : ℝ} {l : List ℝ} {s t : ℝ} (hl : IsPart l s t) (hmesh : l.IsChain fun x y ↦ y - x ≤ δ)
    (ha : a ≤ s) (hb : t ≤ b) :
    ‖rsum Ξ l - sewing Ξ s t‖ ≤ youngConst C γ * (δ ^ (γ - 1) * (t - s)) := by
  have hle : ∀ n : ℕ, ‖rsum Ξ l - sewing Ξ s t‖ ≤ youngConst C γ * (δ ^ (γ - 1) * (t - s)) +
      youngConst C γ * (((t - s) / 2 ^ n) ^ (γ - 1) * (t - s)) +
      ‖dyadicSum Ξ s t n - sewing Ξ s t‖ := fun n ↦
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (norm_rsum_sub_dyadicSum_le hγ hC hδ hl hmesh ha hb n) le_rfl)
  have hlim : Tendsto (fun n : ℕ ↦ youngConst C γ * (δ ^ (γ - 1) * (t - s)) +
      youngConst C γ * (((t - s) / 2 ^ n) ^ (γ - 1) * (t - s)) +
      ‖dyadicSum Ξ s t n - sewing Ξ s t‖) atTop
      (𝓝 (youngConst C γ * (δ ^ (γ - 1) * (t - s)) + youngConst C γ * (0 * (t - s)) + 0)) :=
    (tendsto_const_nhds.add (((tendsto_rpow_div_pow hγ _).mul_const _).const_mul _)).add
      (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_dyadicSum_sewing hγ hδ ha hl.le hb))
  simpa using ge_of_tendsto' hlim hle

/-- **The sewing lemma**, partition sums: if the defect of `Ξ` is bounded by `C (t - s) ^ γ` with
`γ > 1`, the Riemann sums of `Ξ` along partitions of `[s, t]` converge to `sewing Ξ s t` as the
mesh tends to zero. -/
theorem hasPartitionLimit_sewing [CompleteSpace E] (hγ : 1 < γ)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) : HasPartitionLimit Ξ s t (sewing Ξ s t) := by
  intro ε hε
  have hcont : Tendsto (fun δ : ℝ ↦ youngConst (max C 0) γ * (δ ^ (γ - 1) * (t - s)))
      (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (γ - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    simpa using ((tendsto_nhdsWithin_of_tendsto_nhds this).mul_const (t - s)).const_mul
      (youngConst (max C 0) γ)
  obtain ⟨δ, hδε, hδpos⟩ := ((hcont.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδpos, fun n u hu hu0 hun hmesh ↦ ?_⟩
  have hl := isPart_ofFn hu
  rw [hu0, hun] at hl
  have hc : (List.ofFn u).IsChain fun x y ↦ y - x ≤ δ :=
    List.isChain_ofFn.2 fun i hi ↦ by
      have h := hmesh ⟨i, by omega⟩
      rw [Fin.succ_mk, Fin.castSucc_mk] at h
      exact h.le
  rw [← rsum_ofFn]
  exact (norm_rsum_sub_sewing_le hγ (le_max_right _ _) (defect_le_max hδ) hl hc hs ht).trans_lt
    hδε

/-- **The sewing lemma**, additivity: if the defect of `Ξ` is bounded by `C (t - s) ^ γ` with
`γ > 1`, then `sewing Ξ s u + sewing Ξ u t = sewing Ξ s t` for `a ≤ s ≤ u ≤ t ≤ b`. -/
theorem sewing_add_adjacent [CompleteSpace E] (hγ : 1 < γ)
    (hδ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → ‖Ξ s t - Ξ s u - Ξ u t‖ ≤ C * (t - s) ^ γ)
    {s u t : ℝ} (hs : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≤ b) :
    sewing Ξ s u + sewing Ξ u t = sewing Ξ s t := by
  have hbound : ∀ n : ℕ, ‖(dyadicSum Ξ s u n + dyadicSum Ξ u t n) - sewing Ξ s t‖ ≤
      youngConst (max C 0) γ * (((t - s) / 2 ^ n) ^ (γ - 1) * (t - s)) := by
    intro n
    have h₁ := isPart_dyadicPart hsu n
    have h₂ := isPart_dyadicPart hut n
    have hc₁ := isChain_dyadicPart s u n
    have hc₂ := isChain_dyadicPart u t n
    obtain ⟨L₁, hL₁⟩ := List.getLast?_eq_some_iff.1 h₁.2.2
    obtain ⟨L₂, hL₂⟩ := List.head?_eq_some_iff.1 h₂.2.1
    rw [← rsum_dyadicPart, ← rsum_dyadicPart, hL₁, hL₂, ← rsum_append_cons]
    rw [hL₁] at h₁ hc₁
    rw [hL₂] at h₂ hc₂
    have hc₁' : (L₁ ++ [u]).IsChain fun x y ↦ y - x ≤ (t - s) / 2 ^ n :=
      hc₁.imp fun x y h ↦ h.trans (by gcongr)
    have hc₂' : ([u] ++ L₂).IsChain fun x y ↦ y - x ≤ (t - s) / 2 ^ n :=
      hc₂.imp fun x y h ↦ h.trans (by gcongr)
    have hmesh : (L₁ ++ u :: L₂).IsChain fun x y ↦ y - x ≤ (t - s) / 2 ^ n := by
      simpa using hc₁'.append_overlap hc₂' (List.cons_ne_nil _ _)
    exact norm_rsum_sub_sewing_le hγ (le_max_right _ _) (defect_le_max hδ) (h₁.append h₂) hmesh
      hs ht
  have hlim : Tendsto (fun n ↦ dyadicSum Ξ s u n + dyadicSum Ξ u t n) atTop
      (𝓝 (sewing Ξ s t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
    simpa using ((tendsto_rpow_div_pow hγ (t - s)).mul_const (t - s)).const_mul
      (youngConst (max C 0) γ)
  exact tendsto_nhds_unique ((tendsto_dyadicSum_sewing hγ hδ hs hsu (hut.trans ht)).add
    (tendsto_dyadicSum_sewing hγ hδ (hs.trans hsu) hut ht)) hlim

/-- **The sewing lemma**, uniqueness: an additive map `I` on the simplex of `[a, b]` within
`K (t - s) ^ γ` of `Ξ`, for some `γ > 1`, agrees with `sewing Ξ` there. No bound on the defect of
`Ξ` is needed: the dyadic sums of `Ξ` converge to `I s t`. -/
theorem eq_sewing {I : ℝ → ℝ → E} {K : ℝ} (hγ : 1 < γ)
    (hI : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t)
    (hIΞ : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖I s t - Ξ s t‖ ≤ K * (t - s) ^ γ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) : I s t = sewing Ξ s t := by
  have hbound := fun n ↦ norm_le_of_halves (G := fun n s t ↦ I s t - dyadicSum Ξ s t n)
    (by simpa using hIΞ) (fun n s t hs hst ht ↦ by
      rw [hI s ((s + t) / 2) t hs (by linarith) (by linarith) ht, dyadicSum_succ]
      abel) n hs hst ht
  have hr := two_rpow_one_sub_lt_one hγ
  have hlim : Tendsto (dyadicSum Ξ s t) atTop (𝓝 (I s t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ K * (t - s) ^ γ * (2 ^ (1 - γ)) ^ n)
      (fun n ↦ norm_nonneg _) (fun n ↦ by rw [norm_sub_rev]; exact hbound n) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).const_mul
      (K * (t - s) ^ γ)
  rw [sewing_def]
  exact tendsto_nhds_unique hlim (tendsto_nhds_limUnder ⟨_, hlim⟩)

/-- For `s ≤ t`, a partition limit `I` of `Ξ` over `[s, t]` is the limit of the dyadic sums of
`Ξ`, since dyadic partitions have vanishing mesh. -/
theorem HasPartitionLimit.tendsto_dyadicSum {s t : ℝ} {I : E} (hst : s ≤ t)
    (h : HasPartitionLimit Ξ s t I) : Tendsto (dyadicSum Ξ s t) atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hI⟩ := h ε hε
  filter_upwards [(tendsto_div_two_pow (t - s)).eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_eq_norm, ← rsum_dyadicPart, dyadicPart, rsum_ofFn]
  refine hI _ _ (monotone_dyadic hst n) (dyadic_zero s t n) (dyadic_last s t n) fun i ↦ ?_
  rw [Fin.val_succ, Fin.val_castSucc, dyadic_gap]
  exact hn

/-- For `s ≤ t`, a partition limit of `Ξ` over `[s, t]` is `sewing Ξ s t`. -/
theorem HasPartitionLimit.sewing_eq {s t : ℝ} {I : E} (hst : s ≤ t)
    (h : HasPartitionLimit Ξ s t I) : sewing Ξ s t = I := by
  rw [sewing_def]
  exact (h.tendsto_dyadicSum hst).limUnder_eq

/-- For `s ≤ t`, partition limits are unique. -/
theorem HasPartitionLimit.unique {s t : ℝ} {I J : E} (hst : s ≤ t)
    (hI : HasPartitionLimit Ξ s t I) (hJ : HasPartitionLimit Ξ s t J) : I = J :=
  tendsto_nhds_unique (hI.tendsto_dyadicSum hst) (hJ.tendsto_dyadicSum hst)

end TauCeti
