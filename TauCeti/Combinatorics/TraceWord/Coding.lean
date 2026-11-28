/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Finset
import TauCeti.Data.Fin.Basic

/-!
# Füredi–Komlós coding of trace words

The moment method for the largest eigenvalue of a Wigner matrix needs the number of closed walks of
growing length `L` that traverse each of their edges at least twice. Such a walk visits at most
`L / 2 + 1` vertices. When `L = 2 * m > 0`, the walks visiting `m + 1` vertices, that is with
`2 * t = L + 2` for `t` vertices, are the double traversals of trees. They number at most
`n ^ (m + 1) * 2 ^ L` on `n` vertices. Each vertex fewer costs only a factor polynomial in `L`.

This file proves the weighted form of this enumeration. For `0 ≤ γ ≤ 1`, a finite type `α` of
cardinality `n`, and the closed walks `w : Fin L → α` traversing each edge at least twice,
`∑ γ ^ (2 * (L + 2 - 2 * t w)) / n ^ (t w) ≤ (2 + L * γ) ^ L`, where `t w` is the number of
vertices `w` visits. The left side weights each walk by `n⁻ᵗ`, damped by the factor
`γ ^ (2 * (L + 2 - 2 * t))`. For `0 ≤ γ < 1` this factor is `1` exactly for the walks attaining
the tree bound `2 * t = L + 2`. At `γ = 1` every walk has damping factor `1`.

The proof codes a walk by its first vertex and one symbol per step. Each step goes to a new vertex,
or closes the only open discovery edge at the current vertex, or *jumps*. A step is a discovery
when it goes to a new vertex. A discovery edge is open while it has been traversed only once. A
discovery step records its new vertex, a closing step records nothing, and a jump records an
earlier time at which its target was visited. The walk is recovered step by step from the code.

A walk traversing each edge at least twice closes every discovery edge. So with `N` discoveries,
at most `L - 2 * N` steps neither discover nor close. A degree potential on the open discovery
edges shows that the remaining jumps, which close an edge at a vertex carrying at least two open
discovery edges, are no more numerous. Hence at most `2 * (L - 2 * N)` steps jump, and
`t = N + 1`. Weighting a discovery by `n⁻¹`, a closing step by `1`, and a jump to each of the `L`
times by `γ` bounds the left side by the total weight `(2 + L * γ) ^ L` of all codes.

The same coding bounds the walks that visit a prescribed set `A t` of vertices at each time `t`,
with any weight `m ≥ 0` in place of `n`: a discovery at step `t` then chooses among the
`#(A (t + 1))` vertices allowed next. The closed bipartite words of sample covariance matrices are
such walks, alternating between rows and columns.

## Main results

* `TauCeti.sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge`: the weighted enumeration
  bound for walks with prescribed vertex sets, `#(A 0) / m * ∏ t, (#(A (t + 1)) / m + 1 + L * γ)`.
* `TauCeti.sum_pow_div_pow_card_image_le_of_no_singleton_edge`: the weighted enumeration bound
  `(2 + L * γ) ^ L` for all closed walks on `n` vertices.
* `TauCeti.sum_piFinset_pow_div_pow_card_image_le_of_nonbacktracking`: the weighted bound for
  walks that are non-backtracking within prescribed blocks, with each discovery weight bounded
  by a ratio of successive values of a bounded scale.

## References

* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.6, the Füredi–Komlós enumeration (Lemma 2.1.23).
-/

public section

open Finset

namespace TauCeti

variable {α : Type*}

section Path

/-- The edge traversed by step `s` of the path `p`. -/
private def edge (p : ℕ → α) (s : ℕ) : Sym2 α := s(p s, p (s + 1))

/-- Paths agreeing up to time `l` traverse the same edges before time `l`. -/
private theorem edge_congr {p q : ℕ → α} {l t : ℕ} (h : ∀ j ≤ l, p j = q j) (ht : t < l) :
    edge p t = edge q t := by
  rw [edge, edge, h t ht.le, h (t + 1) ht]

variable [DecidableEq α]

/-- Step `i` of the path `p` discovers a vertex not visited at the times `0, …, i`. -/
private def IsNew (p : ℕ → α) (i : ℕ) : Prop :=
  p (i + 1) ∉ (range (i + 1)).image p

/-- At time `l`, the discovery step `s` is *open*: it happened before `l`, and no other step
before `l` traverses its edge. -/
private def IsOpen (p : ℕ → α) (l s : ℕ) : Prop :=
  s < l ∧ IsNew p s ∧ ∀ s' < l, edge p s' = edge p s → s' = s

open Classical in
/-- The number of open discovery edges at time `l` containing the vertex `x`. -/
private noncomputable def openDeg (p : ℕ → α) (l : ℕ) (x : α) : ℕ :=
  #{s ∈ range l | IsOpen p l s ∧ x ∈ edge p s}

/-- Step `l` traverses an open discovery edge, for the second time. -/
private def Closes (p : ℕ → α) (l : ℕ) : Prop :=
  ∃ s, IsOpen p l s ∧ edge p s = edge p l

/-- Step `l` closes the only open discovery edge at its starting vertex. -/
private def Forced (p : ℕ → α) (l : ℕ) : Prop :=
  Closes p l ∧ openDeg p l (p l) = 1

variable {p q : ℕ → α}

/-- A discovered vertex lies on no earlier edge. -/
private theorem notMem_edge_of_isNew {l s : ℕ} (hl : IsNew p l) (hs : s < l) :
    p (l + 1) ∉ edge p s := by
  intro h
  rcases Sym2.mem_iff.mp h with h | h
  · exact hl (mem_image.mpr ⟨s, mem_range.mpr (by omega), h.symm⟩)
  · exact hl (mem_image.mpr ⟨s + 1, mem_range.mpr (by omega), h.symm⟩)

private theorem edge_ne_of_isNew {l s : ℕ} (hl : IsNew p l) (hs : s < l) :
    edge p s ≠ edge p l := fun h ↦
  notMem_edge_of_isNew hl hs (h ▸ Sym2.mem_mk_right _ _)

private theorem ne_of_isNew {l : ℕ} (hl : IsNew p l) : p l ≠ p (l + 1) :=
  fun h ↦ hl (mem_image.mpr ⟨l, mem_range.mpr (by omega), h⟩)

private theorem not_isNew_of_closes {l : ℕ} (h : Closes p l) : ¬ IsNew p l := by
  obtain ⟨s, hs, he⟩ := h
  exact fun hl ↦ edge_ne_of_isNew hl hs.1 he

private theorem ne_of_closes {l : ℕ} (h : Closes p l) : p l ≠ p (l + 1) := by
  obtain ⟨s, hs, he⟩ := h
  intro hl
  have hdiag : (edge p l).IsDiag := Sym2.mk_isDiag_iff.mpr hl
  rw [← he, edge, Sym2.mk_isDiag_iff] at hdiag
  exact ne_of_isNew hs.2.1 hdiag

/-- A closing step immediately after a discovery returns along the discovery edge. -/
private theorem eq_of_isNew_of_closes_succ {l : ℕ} (hnew : IsNew p l)
    (hclose : Closes p (l + 1)) : p l = p (l + 2) := by
  obtain ⟨s, hs, he⟩ := hclose
  have hs' : s = l := by
    by_contra h
    have hlt : s < l := by have := hs.1; omega
    exact notMem_edge_of_isNew hnew hlt (he ▸ Sym2.mem_mk_left _ _)
  subst s
  rw [edge, edge, Sym2.eq_swap (a := p l)] at he
  exact Sym2.congr_right.mp he

private theorem isOpen_succ_iff {l s : ℕ} :
    IsOpen p (l + 1) s ↔ (IsOpen p l s ∧ edge p s ≠ edge p l) ∨ (s = l ∧ IsNew p l) := by
  constructor
  · rintro ⟨hs, hnew, huniq⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · refine Or.inl ⟨⟨hs, hnew, fun s' hs' h ↦ huniq s' (by omega) h⟩, fun h ↦ ?_⟩
      have := huniq l (by omega) h.symm
      omega
    · exact Or.inr ⟨hs, hs ▸ hnew⟩
  · rintro (⟨⟨hs, hnew, huniq⟩, hne⟩ | ⟨rfl, hnew⟩)
    · refine ⟨by omega, hnew, fun s' hs' h ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hs' | rfl
      · exact huniq s' hs' h
      · exact absurd h.symm hne
    · refine ⟨by omega, hnew, fun s' hs' h ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hs' | rfl
      · exact absurd h (edge_ne_of_isNew hnew hs')
      · rfl

open Classical in
/-- The open discovery edges at a vertex, counted before and after step `l`: a closing step
removes its edge, and a discovery adds its edge. -/
private theorem openDeg_succ_add (l : ℕ) (x : α) :
    openDeg p (l + 1) x + (if Closes p l ∧ x ∈ edge p l then 1 else 0) =
      openDeg p l x + (if IsNew p l ∧ x ∈ edge p l then 1 else 0) := by
  simp only [openDeg, card_filter, sum_range_succ]
  have hll : IsOpen p (l + 1) l ↔ IsNew p l := by
    rw [isOpen_succ_iff]
    exact ⟨fun h ↦ h.elim (fun h ↦ absurd h.1.1 (lt_irrefl l)) And.right,
      fun h ↦ Or.inr ⟨rfl, h⟩⟩
  -- Split each earlier step according to whether its edge is the edge of step `l`.
  have hsplit : ∀ s ∈ range l, (if IsOpen p l s ∧ x ∈ edge p s then 1 else 0) =
      (if IsOpen p (l + 1) s ∧ x ∈ edge p s then 1 else 0) +
        (if IsOpen p l s ∧ edge p s = edge p l ∧ x ∈ edge p l then 1 else 0) := by
    intro s hs
    have hsl : s ≠ l := (mem_range.mp hs).ne
    have hiff : IsOpen p (l + 1) s ↔ IsOpen p l s ∧ edge p s ≠ edge p l := by
      rw [isOpen_succ_iff]
      exact ⟨fun h ↦ h.resolve_right fun h ↦ hsl h.1, Or.inl⟩
    by_cases he : edge p s = edge p l
    · rw [he]
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  have hcloses : ∑ s ∈ range l, (if IsOpen p l s ∧ edge p s = edge p l ∧ x ∈ edge p l
      then 1 else 0) = if Closes p l ∧ x ∈ edge p l then 1 else 0 := by
    by_cases hc : Closes p l
    · obtain ⟨s₀, hs₀, he₀⟩ := hc
      have hc : Closes p l := ⟨s₀, hs₀, he₀⟩
      rw [sum_eq_single_of_mem s₀ (mem_range.mpr hs₀.1)]
      · simp only [hs₀, he₀, hc, true_and]
      · intro s _ hs
        exact ite_eq_right fun h ↦ hs (hs₀.2.2 s h.1.1 (h.2.1.trans he₀.symm))
    · rw [ite_eq_right fun h ↦ hc h.1]
      exact sum_eq_zero fun s _ ↦ ite_eq_right fun h ↦ hc ⟨s, h.1, h.2.1⟩
  simp only [hll]
  rw [sum_congr rfl hsplit, sum_add_distrib, hcloses]
  ring

/-- The degree of `x` in the open discovery edges, together with the two ends of the path. -/
private noncomputable def potentialDeg (p : ℕ → α) (l : ℕ) (x : α) : ℕ :=
  openDeg p l x + (if x = p 0 then 1 else 0) + (if x = p l then 1 else 0)

/-- The excess of the degrees `potentialDeg` over `2`. It starts at `0`, is unchanged by
discoveries, drops at a closing step whose vertex carries another open edge, and rises by at most
one at any other step. -/
private noncomputable def potential [Fintype α] (p : ℕ → α) (l : ℕ) : ℕ :=
  ∑ x, (potentialDeg p l x - 2)

open Classical in
private theorem potential_zero [Fintype α] : potential p 0 = 0 := by
  refine sum_eq_zero fun x _ ↦ ?_
  simp only [potentialDeg, openDeg, range_zero, filter_empty, card_empty, zero_add]
  split_ifs <;> omega

open Classical in
private theorem openDeg_eq_zero_of_isNew {l : ℕ} (hl : IsNew p l) :
    openDeg p l (p (l + 1)) = 0 :=
  card_eq_zero.mpr (filter_eq_empty_iff.mpr fun _ hs h ↦
    notMem_edge_of_isNew hl (mem_range.mp hs) h.2)

open Classical in
private theorem one_le_openDeg_of_closes {l : ℕ} (h : Closes p l) : 1 ≤ openDeg p l (p l) := by
  obtain ⟨s, hs, he⟩ := h
  refine card_pos.mpr ⟨s, mem_filter.mpr ⟨mem_range.mpr hs.1, hs, ?_⟩⟩
  rw [he]
  exact Sym2.mem_mk_left _ _

open Classical in
/-- A discovery leaves every degree excess unchanged. -/
private theorem potential_succ_le_of_isNew [Fintype α] {l : ℕ} (hnew : IsNew p l) :
    potential p (l + 1) ≤ potential p l := by
  have hc : ¬ Closes p l := fun h ↦ not_isNew_of_closes h hnew
  have hne := ne_of_isNew hnew
  have h0 : p (l + 1) ≠ p 0 := fun h ↦
    hnew (mem_image.mpr ⟨0, mem_range.mpr (by omega), h.symm⟩)
  have hu := openDeg_eq_zero_of_isNew hnew
  refine sum_le_sum fun x _ ↦ ?_
  have hx := openDeg_succ_add (p := p) l x
  simp only [edge, Sym2.mem_iff] at hx
  rw [ite_eq_right fun h ↦ hc h.1] at hx
  simp only [potentialDeg]
  by_cases hxu : x = p (l + 1)
  · subst hxu
    rw [ite_eq_left ⟨hnew, Or.inr rfl⟩] at hx
    rw [ite_eq_right h0, ite_eq_right hne.symm, ite_eq_left rfl, hu]
    omega
  · by_cases hxc : x = p l
    · subst hxc
      rw [ite_eq_left ⟨hnew, Or.inl rfl⟩] at hx
      rw [ite_eq_right hne, ite_eq_left rfl]
      omega
    · rw [ite_eq_right fun h ↦ h.2.elim hxc hxu] at hx
      rw [ite_eq_right hxu, ite_eq_right hxc]
      omega

open Classical in
/-- A closing step lowers the degree of its starting vertex by two, so it lowers the excess when
that vertex carries another open discovery edge. -/
private theorem potential_succ_add_le_of_closes [Fintype α] {l : ℕ} (hc : Closes p l) :
    potential p (l + 1) + (if 2 ≤ openDeg p l (p l) then 1 else 0) ≤ potential p l := by
  have hnew := not_isNew_of_closes hc
  have hne := ne_of_closes hc
  have hle (x : α) : potentialDeg p (l + 1) x + (if x = p l then 2 else 0) =
      potentialDeg p l x := by
    have hx := openDeg_succ_add (p := p) l x
    simp only [edge, Sym2.mem_iff] at hx
    have hN : (if IsNew p l ∧ (x = p l ∨ x = p (l + 1)) then 1 else 0) = 0 :=
      ite_eq_right fun h ↦ hnew h.1
    rw [hN, add_zero] at hx
    simp only [potentialDeg]
    by_cases hxc : x = p l
    · subst hxc
      rw [ite_eq_left ⟨hc, Or.inl rfl⟩] at hx
      rw [ite_eq_right hne, ite_eq_left rfl, ite_eq_left rfl]
      omega
    · by_cases hxu : x = p (l + 1)
      · subst hxu
        rw [ite_eq_left ⟨hc, Or.inr rfl⟩] at hx
        simp only [hxc, ↓reduceIte]
        omega
      · rw [ite_eq_right fun h ↦ h.2.elim hxc hxu] at hx
        simp only [hxu, hxc, ↓reduceIte]
        omega
  split_ifs with h2
  · have hlt : potential p (l + 1) < potential p l := by
      refine sum_lt_sum (fun x _ ↦ ?_) ⟨p l, mem_univ _, ?_⟩
      · have := hle x
        split_ifs at this <;> omega
      · have := hle (p l)
        rw [ite_eq_left rfl] at this
        have : 3 ≤ potentialDeg p l (p l) := by
          simp only [potentialDeg, ↓reduceIte]
          omega
        omega
    omega
  · refine (sum_le_sum fun x _ ↦ ?_).trans_eq (add_zero _).symm
    have := hle x
    split_ifs at this <;> omega

open Classical in
/-- A step raises the excess by at most one: a discovery or a closing step does not raise it, and
any other step moves one end of the path. -/
private theorem potential_succ_le_add_one [Fintype α] (l : ℕ) :
    potential p (l + 1) ≤ potential p l + 1 := by
  by_cases hnew : IsNew p l
  · exact (potential_succ_le_of_isNew hnew).trans (Nat.le_succ _)
  by_cases hc : Closes p l
  · exact ((Nat.le_add_right _ _).trans (potential_succ_add_le_of_closes hc)).trans (Nat.le_succ _)
  calc potential p (l + 1)
      ≤ ∑ x, ((potentialDeg p l x - 2) + if x = p (l + 1) then 1 else 0) := by
        refine sum_le_sum fun x _ ↦ ?_
        have hx := openDeg_succ_add (p := p) l x
        rw [ite_eq_right fun h ↦ hc h.1, ite_eq_right fun h ↦ hnew h.1] at hx
        simp only [potentialDeg]
        split_ifs <;> omega
    _ = potential p l + 1 := by
        rw [sum_add_distrib, sum_ite_eq']
        simp only [mem_univ, ite_eq_left, potential]

open Classical in
/-- One step of the potential argument. -/
private theorem potential_succ_add_le [Fintype α] (l : ℕ) :
    potential p (l + 1) + (if Closes p l ∧ 2 ≤ openDeg p l (p l) then 1 else 0) ≤
      potential p l + (if ¬ IsNew p l ∧ ¬ Closes p l then 1 else 0) := by
  by_cases hnew : IsNew p l
  · have hc : ¬ Closes p l := fun h ↦ not_isNew_of_closes h hnew
    have hA : (if Closes p l ∧ 2 ≤ openDeg p l (p l) then 1 else 0) = 0 :=
      ite_eq_right fun h ↦ hc h.1
    have hT : (if ¬ IsNew p l ∧ ¬ Closes p l then 1 else 0) = 0 :=
      ite_eq_right fun h ↦ h.1 hnew
    rw [hA, hT]
    exact potential_succ_le_of_isNew hnew
  by_cases hc : Closes p l
  · have hT : (if ¬ IsNew p l ∧ ¬ Closes p l then 1 else 0) = 0 := ite_eq_right fun h ↦ h.2 hc
    rw [hT, add_zero]
    simpa only [hc, true_and] using potential_succ_add_le_of_closes hc
  · have hA : (if Closes p l ∧ 2 ≤ openDeg p l (p l) then 1 else 0) = 0 :=
      ite_eq_right fun h ↦ hc h.1
    have hT : (if ¬ IsNew p l ∧ ¬ Closes p l then 1 else 0) = 1 := ite_eq_left ⟨hnew, hc⟩
    rw [hA, hT, add_zero]
    exact potential_succ_le_add_one l

open Classical in
/-- Closing steps at a vertex carrying at least two open discovery edges are no more numerous
than the steps that neither discover nor close. -/
private theorem card_closes_two_le_openDeg_le [Finite α] (m : ℕ) :
    #{l ∈ range m | Closes p l ∧ 2 ≤ openDeg p l (p l)} ≤
      #{l ∈ range m | ¬ IsNew p l ∧ ¬ Closes p l} := by
  have := Fintype.ofFinite α
  suffices h : potential p m + #{l ∈ range m | Closes p l ∧ 2 ≤ openDeg p l (p l)} ≤
      #{l ∈ range m | ¬ IsNew p l ∧ ¬ Closes p l} by omega
  induction m with
  | zero => simp [potential_zero]
  | succ m ih =>
    simp only [card_filter, sum_range_succ] at ih ⊢
    have := potential_succ_add_le (p := p) m
    omega

open Classical in
/-- A path of `m` steps visits one vertex more than its number of discoveries. -/
private theorem card_image_range_eq (m : ℕ) :
    #((range (m + 1)).image p) = #{i ∈ range m | IsNew p i} + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hf : #{i ∈ range (m + 1) | IsNew p i} =
        #{i ∈ range m | IsNew p i} + if IsNew p m then 1 else 0 := by
      simp only [card_filter, sum_range_succ]
    rw [hf, range_add_one, image_insert]
    by_cases hm : IsNew p m
    · rw [card_insert_of_notMem hm, ih, ite_eq_left hm]
    · have hm' : p (m + 1) ∈ (range (m + 1)).image p := by
        unfold IsNew at hm
        exact not_not.mp hm
      rw [insert_eq_of_mem hm', ih, ite_eq_right hm]

open Classical in
/-- If every step of a path of `L` steps shares its edge with another step, every discovery edge
is closed later, so there are at least as many closing steps as discoveries. -/
private theorem card_isNew_le_card_closes {L : ℕ}
    (hSF : ∀ i < L, ∃ j < L, j ≠ i ∧ edge p j = edge p i) :
    #{i ∈ range L | IsNew p i} ≤ #{l ∈ range L | Closes p l} := by
  have hex (i : ℕ) (hi : i < L) (hnew : IsNew p i) :
      ∃ j, i < j ∧ j < L ∧ edge p j = edge p i := by
    obtain ⟨j, hj, hji, he⟩ := hSF i hi
    rcases lt_or_gt_of_ne hji with h | h
    · exact absurd he (edge_ne_of_isNew hnew h)
    · exact ⟨j, h, hj, he⟩
  let f (i : ℕ) : ℕ := if h : ∃ j, i < j ∧ j < L ∧ edge p j = edge p i then Nat.find h else 0
  have hf (i : ℕ) (hi : i < L) (hnew : IsNew p i) :
      i < f i ∧ f i < L ∧ edge p (f i) = edge p i ∧
        ∀ j, i < j → j < f i → edge p j ≠ edge p i := by
    have h := hex i hi hnew
    simp only [f, dite_eq_left h]
    obtain ⟨h₁, h₂, h₃⟩ := Nat.find_spec h
    exact ⟨h₁, h₂, h₃, fun j hij hj he ↦ Nat.find_min h hj ⟨hij, by omega, he⟩⟩
  refine card_le_card_of_injOn f (fun i hi ↦ ?_) (fun i hi i' hi' hii' ↦ ?_)
  · obtain ⟨hi, hnew⟩ := mem_filter.mp (mem_coe.mp hi)
    have hi := mem_range.mp hi
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hf i hi hnew
    refine mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr h₂, i, ⟨h₁, hnew, fun s hs he ↦ ?_⟩,
      h₃.symm⟩)
    rcases lt_trichotomy s i with hsi | rfl | hsi
    · exact absurd he (edge_ne_of_isNew hnew hsi)
    · rfl
    · exact absurd he (h₄ s hsi hs)
  · obtain ⟨hi, hnew⟩ := mem_filter.mp (mem_coe.mp hi)
    obtain ⟨hi', hnew'⟩ := mem_filter.mp (mem_coe.mp hi')
    have he : edge p i = edge p i' := by
      rw [← (hf i (mem_range.mp hi) hnew).2.2.1, ← (hf i' (mem_range.mp hi') hnew').2.2.1, hii']
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd he (edge_ne_of_isNew hnew' h)
    · exact h
    · exact absurd he.symm (edge_ne_of_isNew hnew h)

open Classical in
/-- If every step of a path of `L` steps shares its edge with another step, the steps that neither
discover a vertex nor are forced number at most twice the excess `L - 2 * N` of the `N`
discoveries. -/
private theorem card_jump_add_four_mul_card_isNew_le [Finite α] {L : ℕ}
    (hSF : ∀ i < L, ∃ j < L, j ≠ i ∧ edge p j = edge p i) :
    #{l ∈ range L | ¬ IsNew p l ∧ ¬ Forced p l} + 4 * #{i ∈ range L | IsNew p i} ≤ 2 * L := by
  have hN := card_isNew_le_card_closes hSF
  have hA := card_closes_two_le_openDeg_le (p := p) L
  -- The steps split into discoveries, closing steps and the remaining steps.
  have h₁ : Disjoint {i ∈ range L | IsNew p i} {l ∈ range L | Closes p l} :=
    disjoint_filter.mpr fun l _ hl hc ↦ not_isNew_of_closes hc hl
  have h₂ : Disjoint ({i ∈ range L | IsNew p i} ∪ {l ∈ range L | Closes p l})
      {l ∈ range L | ¬ IsNew p l ∧ ¬ Closes p l} :=
    disjoint_union_left.mpr ⟨disjoint_filter.mpr fun _ _ h h' ↦ h'.1 h,
      disjoint_filter.mpr fun _ _ h h' ↦ h'.2 h⟩
  have hpart : #{i ∈ range L | IsNew p i} + #{l ∈ range L | Closes p l} +
      #{l ∈ range L | ¬ IsNew p l ∧ ¬ Closes p l} ≤ L := by
    rw [← card_union_of_disjoint h₁, ← card_union_of_disjoint h₂]
    simpa using card_le_card (union_subset (union_subset (filter_subset _ _)
      (filter_subset _ _)) (filter_subset _ (range L)))
  -- A step that is neither a discovery nor forced either neither discovers nor closes, or
  -- closes at a vertex with two open discovery edges.
  have hjump : #{l ∈ range L | ¬ IsNew p l ∧ ¬ Forced p l} ≤
      #{l ∈ range L | ¬ IsNew p l ∧ ¬ Closes p l} +
        #{l ∈ range L | Closes p l ∧ 2 ≤ openDeg p l (p l)} := by
    refine (card_le_card fun l hl ↦ ?_).trans (card_union_le _ _)
    obtain ⟨hl, hnew, hforced⟩ := mem_filter.mp hl
    by_cases hc : Closes p l
    · have := one_le_openDeg_of_closes hc
      have : openDeg p l (p l) ≠ 1 := fun h ↦ hforced ⟨hc, h⟩
      exact mem_union_right _ (mem_filter.mpr ⟨hl, hc, by omega⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hl, hnew, hc⟩)
  omega

/-- Paths agreeing up to time `l` have the same open discovery steps at time `l`. -/
private theorem isOpen_congr {l s : ℕ} (h : ∀ j ≤ l, p j = q j) :
    IsOpen p l s ↔ IsOpen q l s := by
  have hnew {s' : ℕ} (hs' : s' < l) : IsNew p s' ↔ IsNew q s' := by
    have himage : (range (s' + 1)).image p = (range (s' + 1)).image q :=
      image_congr fun j hj ↦ h j (by have := mem_range.mp hj; omega)
    rw [IsNew, IsNew, himage, h (s' + 1) hs']
  constructor
  · rintro ⟨hs, hn, hu⟩
    exact ⟨hs, (hnew hs).mp hn, fun s' hs' he ↦
      hu s' hs' (by rwa [edge_congr h hs', edge_congr h hs])⟩
  · rintro ⟨hs, hn, hu⟩
    exact ⟨hs, (hnew hs).mpr hn, fun s' hs' he ↦
      hu s' hs' (by rwa [← edge_congr h hs', ← edge_congr h hs])⟩

open Classical in
/-- A forced step is determined by the path up to its starting time. -/
private theorem eq_of_forced {l : ℕ} (h : ∀ j ≤ l, p j = q j) (hp : Forced p l)
    (hq : Forced q l) : p (l + 1) = q (l + 1) := by
  obtain ⟨⟨s, hs, he⟩, hdeg⟩ := hp
  obtain ⟨⟨s', hs', he'⟩, -⟩ := hq
  have hs'p : IsOpen p l s' := (isOpen_congr h).mpr hs'
  -- Both open steps carry the starting vertex, which has a single open discovery edge.
  have hss' : s = s' := by
    have hdeg' : #{t ∈ range l | IsOpen p l t ∧ p l ∈ edge p t} ≤ 1 := hdeg.le
    refine card_le_one.mp hdeg' s (mem_filter.mpr ⟨mem_range.mpr hs.1, hs, ?_⟩) s'
      (mem_filter.mpr ⟨mem_range.mpr hs'.1, hs'p, ?_⟩)
    · rw [he]
      exact Sym2.mem_mk_left _ _
    · rw [edge_congr h hs'.1, he', h l le_rfl]
      exact Sym2.mem_mk_left _ _
  subst hss'
  have : s(p l, p (l + 1)) = s(p l, q (l + 1)) := by
    have := he.symm.trans ((edge_congr h hs.1).trans he')
    rwa [edge, edge, ← h l le_rfl] at this
  exact Sym2.congr_right.mp this

end Path

section Weight

variable {L : ℕ}

/-- The weight of a code symbol: `n⁻¹` for a discovery, `1` for a forced step, and `γ` for a
jump. -/
private noncomputable def symbolWeight (n γ : ℝ) : Option (α ⊕ Fin L) → ℝ
  | none => 1
  | some (.inl _) => n⁻¹
  | some (.inr _) => γ

private theorem symbolWeight_nonneg {n γ : ℝ} (hn : 0 ≤ n) (hγ : 0 ≤ γ)
    (c : Option (α ⊕ Fin L)) : 0 ≤ symbolWeight n γ c := by
  rcases c with _ | _ | _
  · exact zero_le_one
  · exact inv_nonneg.mpr hn
  · exact hγ

/-- The code symbols allowed at a step whose target lies in `B`: a forced step, the discovery of a
vertex of `B`, or a jump to one of the `L` times. -/
private def allowedSymbols (B : Finset α) : Finset (Option (α ⊕ Fin L)) :=
  insertNone (B.disjSum univ)

private theorem sum_allowedSymbols_symbolWeight (n γ : ℝ) (B : Finset α) :
    ∑ c ∈ allowedSymbols (L := L) B, symbolWeight n γ c = #B / n + 1 + L * γ := by
  simp only [allowedSymbols, sum_insertNone, sum_disjSum, symbolWeight, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A discovery symbol records a new vertex. -/
private def isDiscovery : Option (α ⊕ Fin L) → Bool
  | some (.inl _) => true
  | _ => false

/-- In a block of code symbols, a discovery may be followed by a discovery or a jump.
The input flag records whether the step just before the block was a discovery. -/
private def AllowsCode : {k : ℕ} → Bool → (Fin k → Option (α ⊕ Fin L)) → Prop
  | 0, _, _ => True
  | _ + 1, d, c => (d = true → c 0 ≠ none) ∧ AllowsCode (isDiscovery (c 0)) (Fin.tail c)

private theorem allowsCode_of_adjacent {k : ℕ} (c : Fin k → Option (α ⊕ Fin L))
    (h : ∀ i j : Fin k, i.val + 1 = j.val → isDiscovery (c i) = true → c j ≠ none) :
    AllowsCode false c := by
  suffices ∀ (d : Bool), (∀ i : Fin k, i.val = 0 → d = true → c i ≠ none) → AllowsCode d c
    from this false (by simp)
  induction k with
  | zero => simp [AllowsCode]
  | succ k ih =>
    intro d hd
    refine ⟨hd 0 rfl, ih (Fin.tail c) (fun i j hij ↦ h i.succ j.succ (by simpa using hij))
      _ (fun i hi ↦ h 0 i.succ (by simp [hi]))⟩

open Classical in
/-- Codes through the prescribed vertex sets, with no forced step after a discovery. -/
private noncomputable def blockCodes {k : ℕ} (A : Fin k → Finset α) (d : Bool) :
    Finset (Fin k → Option (α ⊕ Fin L)) :=
  (Fintype.piFinset fun i ↦ allowedSymbols (A i)).filter (AllowsCode d)

/-- Total weight of the codes in a block with prescribed discovery sets. -/
private noncomputable def blockWeight {k : ℕ} (A : Fin k → Finset α) (d : Bool) (m γ : ℝ) : ℝ :=
  ∑ c ∈ blockCodes (L := L) A d, ∏ i, symbolWeight m γ (c i)

private theorem blockWeight_nonneg {k : ℕ} (A : Fin k → Finset α) (d : Bool) {m γ : ℝ}
    (hm : 0 ≤ m) (hγ : 0 ≤ γ) : 0 ≤ blockWeight (L := L) A d m γ :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun _ _ ↦ symbolWeight_nonneg hm hγ _

private theorem blockWeight_zero (A : Fin 0 → Finset α) (d : Bool) (m γ : ℝ) :
    blockWeight (L := L) A d m γ = 1 := by
  classical
  simp [blockWeight, blockCodes, AllowsCode]

/-- Split the weight by the first symbol. A jump resets the flag and a discovery sets it. -/
private theorem blockWeight_succ {k : ℕ} (A : Fin (k + 1) → Finset α) (d : Bool) (m γ : ℝ) :
    blockWeight (L := L) A d m γ =
      (if d then 0 else blockWeight (L := L) (Fin.tail A) false m γ) +
        (#(A 0) / m * blockWeight (L := L) (Fin.tail A) true m γ +
          (L * γ) * blockWeight (L := L) (Fin.tail A) false m γ) := by
  classical
  let S (i : Fin (k + 1)) := allowedSymbols (L := L) (A i)
  have hsplit : Fintype.piFinset S =
      (S 0 ×ˢ Fintype.piFinset (Fin.tail S)).map (Fin.consEquiv _).toEmbedding := by
    simpa using filter_piFinset_eq_map_consEquiv S (fun _ ↦ True)
  rw [blockWeight, blockCodes, sum_filter, hsplit, sum_map, sum_product]
  have hs (c : Option (α ⊕ Fin L)) : (∑ x ∈ Fintype.piFinset (Fin.tail S),
      if AllowsCode d (Fin.cons c x) then
        ∏ i, symbolWeight m γ (Fin.cons (α := fun _ ↦ Option (α ⊕ Fin L)) c x i) else 0) =
        if d = true ∧ c = none then 0
        else symbolWeight m γ c * blockWeight (L := L) (Fin.tail A) (isDiscovery c) m γ := by
    rw [blockWeight, blockCodes, sum_filter, mul_sum]
    by_cases h : d = true ∧ c = none
    · simp [AllowsCode, h.1, h.2]
    · simp only [AllowsCode, Fin.cons_zero, Fin.tail_cons, ite_eq_right h]
      have hc : d = true → c ≠ none := fun hd hc ↦ h ⟨hd, hc⟩
      simp only [eq_true hc, true_and, Fin.prod_univ_succ, Fin.cons_succ]
      exact sum_congr rfl fun x _ ↦ by split_ifs <;> simp
  calc
    _ = ∑ c ∈ S 0, if d = true ∧ c = none then 0 else
        symbolWeight m γ c * blockWeight (L := L) (Fin.tail A) (isDiscovery c) m γ :=
      sum_congr rfl fun c _ ↦ hs c
    _ = _ := by
      simp only [S, allowedSymbols, sum_insertNone, sum_disjSum, reduceCtorEq, and_false,
        ite_false, symbolWeight, isDiscovery, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, and_true, one_mul, div_eq_mul_inv]
      ring

/-- Inductive bounds for a suffix of a block. The discovery weight at a step is bounded by
the ratio of consecutive values of `q`. Multiplying the restricted weight by the current
value of `q` makes these ratios cancel. -/
private theorem blockWeight_le {M k : ℕ} (hk : k ≤ M) (A : Fin k → Finset α)
    {m γ R : ℝ} (hm : 0 < m) (hγ : 0 ≤ γ) (q : Fin (k + 1) → ℝ)
    (hq : ∀ i, 1 ≤ q i ∧ q i ≤ R) (hA : ∀ i : Fin k, #(A i) / m ≤ q i.succ / q i.castSucc) :
    let Q := 1 + ((M : ℝ) + 1) * R * (L * γ)
    blockWeight (L := L) A false m γ ≤ ((k : ℝ) + 1) * R * Q ^ k ∧
      q 0 * blockWeight (L := L) A true m γ ≤ R * Q ^ k := by
  let J := (L : ℝ) * γ
  let Q := 1 + ((M : ℝ) + 1) * R * J
  have hR : 1 ≤ R := (hq 0).1.trans (hq 0).2
  have hJ : 0 ≤ J := mul_nonneg (Nat.cast_nonneg L) hγ
  have hQ : 1 ≤ Q := le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg M) zero_le_one)
      (zero_le_one.trans hR)) hJ)
  induction k with
  | zero => simpa [blockWeight_zero, Q] using And.intro hR (hq 0).2
  | succ k ih =>
    obtain ⟨hF, hD⟩ := ih (by omega) (Fin.tail A) (Fin.tail q) (fun i ↦ hq i.succ)
      (fun i ↦ hA i.succ)
    have hq₀ : 0 < q 0 := zero_lt_one.trans_le (hq 0).1
    have hR₀ : 0 ≤ R := zero_le_one.trans hR
    have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
    have hQk : 0 ≤ Q ^ k := pow_nonneg hQ₀ _
    have hRJ : 0 ≤ R * J := mul_nonneg hR₀ hJ
    have hkR : 0 ≤ ((k : ℝ) + 1) * R :=
      mul_nonneg (add_nonneg (Nat.cast_nonneg k) zero_le_one) hR₀
    have hhead : q 0 * (#(A 0) / m) ≤ q (Fin.succ 0) := by
      rw [mul_comm, ← le_div_iff₀ hq₀]
      exact hA 0
    have hnext : q 0 * blockWeight (L := L) A true m γ ≤ R * Q ^ (k + 1) := by
      rw [blockWeight_succ, ite_eq_left rfl, zero_add, mul_add,
        ← mul_assoc, ← mul_assoc]
      calc _ ≤ R * Q ^ k + R * J * (((k : ℝ) + 1) * R * Q ^ k) := by
            refine add_le_add ((mul_le_mul_of_nonneg_right hhead ?_).trans hD) ?_
            · exact blockWeight_nonneg _ _ hm.le hγ
            · exact mul_le_mul (mul_le_mul_of_nonneg_right (hq 0).2 hJ) hF
                (blockWeight_nonneg _ _ hm.le hγ) (mul_nonneg hR₀ hJ)
        _ ≤ R * Q ^ k + R * J * (((M : ℝ) + 1) * R * Q ^ k) := by
            have hkM : (k : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_succ_le hk)
            gcongr
        _ = R * Q ^ (k + 1) := by rw [pow_succ]; dsimp [Q]; ring
    have hD' : blockWeight (L := L) A true m γ ≤ R * Q ^ (k + 1) :=
      (le_mul_of_one_le_left (blockWeight_nonneg _ _ hm.le hγ) (hq 0).1).trans hnext
    refine ⟨?_, hnext⟩
    have hsplit := blockWeight_succ (L := L) A true m γ
    rw [ite_eq_left rfl, zero_add] at hsplit
    rw [blockWeight_succ, ite_eq_right Bool.false_ne_true, ← hsplit]
    have hpow : Q ^ k ≤ Q ^ (k + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right hQk hQ
    calc _ ≤ ((k : ℝ) + 1) * R * Q ^ (k + 1) + R * Q ^ (k + 1) := by
          exact add_le_add (hF.trans (mul_le_mul_of_nonneg_left hpow hkR)) hD'
      _ = (((k + 1 : ℕ) : ℝ) + 1) * R * Q ^ (k + 1) := by push_cast; ring

end Weight

section Code

variable {L : ℕ} [NeZero L]

/-- The path running through a cyclic word `w : Fin L → α` and returning to its start. -/
private def cyclicPath (w : Fin L → α) (i : ℕ) : α := w (Fin.ofNat L i)

private theorem cyclicPath_val (w : Fin L → α) (t : Fin L) : cyclicPath w t.val = w t := by
  simp [cyclicPath]

private theorem edge_cyclicPath (w : Fin L → α) (i : ℕ) :
    edge (cyclicPath w) i =
      s(w (Fin.ofNat L i), w (finRotate L (Fin.ofNat L i))) := by
  rw [edge, cyclicPath, cyclicPath, Fin.finRotate_ofNat]

variable [DecidableEq α]

open Classical in
/-- The symbol coding step `l` of a path: the new vertex for a discovery, nothing for a forced
step, and otherwise the first time its target was visited. -/
private noncomputable def symbol (p : ℕ → α) (L l : ℕ) [NeZero L] : Option (α ⊕ Fin L) :=
  if IsNew p l then some (.inl (p (l + 1)))
  else if Forced p l then none
  else some (.inr (Fin.ofNat L (Nat.find (⟨l + 1, rfl⟩ : ∃ s, p s = p (l + 1)))))

/-- The Füredi–Komlós code of a cyclic word: its first vertex and the symbols of its steps. -/
private noncomputable def code (w : Fin L → α) : α × (Fin L → Option (α ⊕ Fin L)) :=
  (w 0, fun l ↦ symbol (cyclicPath w) L l.val)

private theorem find_le_of_not_isNew {p : ℕ → α} {l : ℕ} (h : ¬ IsNew p l) :
    Nat.find (⟨l + 1, rfl⟩ : ∃ s, p s = p (l + 1)) ≤ l := by
  rw [IsNew, not_not, mem_image] at h
  obtain ⟨s, hs, hps⟩ := h
  exact (Nat.find_min' _ hps).trans (by have := mem_range.mp hs; omega)

/-- A cyclic word is recovered from its code. -/
private theorem code_injective : Function.Injective (code : (Fin L → α) → _) := by
  intro w w' hww'
  simp only [code, Prod.mk.injEq] at hww'
  obtain ⟨h0, hsym⟩ := hww'
  have hprefix : ∀ i < L, ∀ j ≤ i, cyclicPath w j = cyclicPath w' j := by
    intro i hi
    induction i with
    | zero =>
      intro j hj
      obtain rfl := Nat.le_zero.mp hj
      simpa [cyclicPath] using h0
    | succ i ih =>
      have ih := ih (by omega)
      intro j hj
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact ih j (by omega)
      have hs := congrFun hsym ⟨i, by omega⟩
      simp only [symbol] at hs
      split_ifs at hs <;>
        simp only [Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hs
      · exact hs
      · exact eq_of_forced ih ‹_› ‹_›
      · -- Both steps jump to the same earlier time.
        have hpa := Nat.find_spec (⟨i + 1, rfl⟩ : ∃ s, cyclicPath w s = cyclicPath w (i + 1))
        have hpb := Nat.find_spec (⟨i + 1, rfl⟩ : ∃ s, cyclicPath w' s = cyclicPath w' (i + 1))
        have hfind := find_le_of_not_isNew (p := cyclicPath w) (l := i) ‹_›
        have hfind' := find_le_of_not_isNew (p := cyclicPath w') (l := i) ‹_›
        generalize Nat.find (⟨i + 1, rfl⟩ : ∃ s, cyclicPath w s = cyclicPath w (i + 1)) = a
          at hpa hfind hs
        generalize Nat.find (⟨i + 1, rfl⟩ : ∃ s, cyclicPath w' s = cyclicPath w' (i + 1)) = b
          at hpb hfind' hs
        have heq := congrArg Fin.val hs
        rw [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : a < L),
          Nat.mod_eq_of_lt (by omega : b < L)] at heq
        rw [← hpa, ← hpb, ← heq]
        exact ih a hfind
  funext t
  rw [← cyclicPath_val w t, ← cyclicPath_val w' t]
  exact hprefix t.val t.isLt t.val le_rfl

open Classical in
private theorem prod_symbolWeight (n γ : ℝ) (p : ℕ → α) :
    ∏ l : Fin L, symbolWeight n γ (symbol p L l.val) =
      n⁻¹ ^ #{i ∈ range L | IsNew p i} * γ ^ #{l ∈ range L | ¬ IsNew p l ∧ ¬ Forced p l} := by
  have hw (l : ℕ) : symbolWeight n γ (symbol p L l) =
      if IsNew p l then n⁻¹ else if Forced p l then 1 else γ := by
    simp only [symbol]
    split_ifs <;> rfl
  rw [Fin.prod_univ_eq_prod_range (fun l ↦ symbolWeight n γ (symbol p L l)) L]
  simp only [hw, prod_ite, prod_const_one, prod_const, one_mul, filter_filter]

private theorem image_range_cyclicPath (w : Fin L → α) :
    (range (L + 1)).image (cyclicPath w) = univ.image w :=
  Fin.image_range_ofNat_eq_image_univ w (Nat.le_succ L)

open Classical in
/-- A cyclic word traversing each edge at least twice is bounded by `n⁻¹` times the weight of its
code, for every `n > 0`: it has `t - 1` discoveries and at most `2 * (L + 2 - 2 * t)` jumps. -/
private theorem pow_div_pow_card_image_le_inv_mul_prod_symbolWeight [Finite α] {n γ : ℝ}
    (hn : 0 < n) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (w : Fin L → α)
    (hw : ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t))) :
    γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / n ^ #(univ.image w) ≤
      n⁻¹ * ∏ l, symbolWeight n γ ((code w).2 l) := by
  set p := cyclicPath w
  have hSF : ∀ i < L, ∃ j < L, j ≠ i ∧ edge p j = edge p i := by
    intro i hi
    obtain ⟨s, hs, he⟩ := hw (Fin.ofNat L i)
    refine ⟨s.val, s.isLt, fun h ↦ hs (Fin.ext (by simp [h, Nat.mod_eq_of_lt hi])), ?_⟩
    simpa [p, edge_cyclicPath] using he
  have hcard := card_image_range_eq (p := p) L
  rw [image_range_cyclicPath] at hcard
  have hjump := card_jump_add_four_mul_card_isNew_le hSF
  simp only [code]
  rw [prod_symbolWeight n γ p, hcard]
  set N := #{i ∈ range L | IsNew p i}
  set J := #{l ∈ range L | ¬ IsNew p l ∧ ¬ Forced p l}
  have hexp : J ≤ 2 * (L + 2 - 2 * (N + 1)) := by omega
  calc γ ^ (2 * (L + 2 - 2 * (N + 1))) / n ^ (N + 1) ≤ γ ^ J / n ^ (N + 1) :=
        div_le_div_of_nonneg_right (pow_le_pow_of_le_one hγ₀ hγ₁ hexp) (pow_pos hn _).le
    _ = n⁻¹ * (n⁻¹ ^ N * γ ^ J) := by rw [div_eq_mul_inv, ← inv_pow, pow_succ]; ring

/-- The code of a walk visiting `A t` at each time `t` starts in `A 0`, and its symbol at step `t`
is allowed for the target set `A (finRotate L t)`. -/
private theorem code_mem_of_mem_piFinset {A : Fin L → Finset α} {w : Fin L → α}
    (hw : w ∈ Fintype.piFinset A) :
    code w ∈ A 0 ×ˢ Fintype.piFinset fun t ↦ allowedSymbols (A (finRotate L t)) := by
  rw [Fintype.mem_piFinset] at hw
  refine mem_product.mpr ⟨hw 0, Fintype.mem_piFinset.mpr fun t ↦ ?_⟩
  simp only [code, symbol]
  split_ifs
  · have : cyclicPath w (t.val + 1) = w (finRotate L t) := by
      rw [cyclicPath, ← Fin.finRotate_ofNat]
      exact congrArg (w ∘ finRotate L) (Fin.ext (by simp))
    simpa [allowedSymbols, this] using hw (finRotate L t)
  · simp [allowedSymbols]
  · simp [allowedSymbols]

private theorem code_not_forced_after_discovery {w : Fin L → α} {i j : Fin L}
    (hij : i.val + 1 = j.val) (h : w i ≠ w (finRotate L j))
    (hd : isDiscovery ((code w).2 i) = true) : (code w).2 j ≠ none := by
  have hnew : IsNew (cyclicPath w) i.val := by
    simp only [code, symbol] at hd
    split_ifs at hd <;> simp_all [isDiscovery]
  have hnc : ¬ Closes (cyclicPath w) j.val := by
    intro hc
    rw [← hij] at hc
    have he := eq_of_isNew_of_closes_succ hnew hc
    have hnext : i.val + 2 = j.val + 1 := by omega
    rw [cyclicPath_val, cyclicPath, hnext, ← Fin.finRotate_ofNat] at he
    exact h (by simpa using he)
  simp only [code, symbol]
  split_ifs with _ hf
  · simp
  · exact (hnc hf.1).elim
  · simp

end Code

/-- The restriction of a word's code to a non-backtracking block is admissible, with no
restriction on the step before that block. -/
private theorem code_mem_blockCodes [DecidableEq α] {B M : ℕ} [NeZero (B * M)]
    {A : Fin (B * M) → Finset α} {w : Fin (B * M) → α} (hw : w ∈ Fintype.piFinset A)
    (b : Fin B) (hn : ∀ i j : Fin M, i.val + 1 = j.val →
      w (finProdFinEquiv (b, i)) ≠ w (finRotate _ (finProdFinEquiv (b, j)))) :
    (fun i ↦ (code w).2 (finProdFinEquiv (b, i))) ∈
      blockCodes (fun i ↦ A (finRotate _ (finProdFinEquiv (b, i)))) false := by
  classical
  have hsymbols := (mem_product.mp (code_mem_of_mem_piFinset hw)).2
  refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦
    Fintype.mem_piFinset.mp hsymbols (finProdFinEquiv (b, i)), ?_⟩
  refine allowsCode_of_adjacent _ fun i j hij ↦ code_not_forced_after_discovery ?_ (hn i j hij)
  simpa only [finProdFinEquiv_apply_val, Nat.add_right_comm] using
    congrArg (· + M * b.val) hij

/-- The weighted enumeration of `sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge`
for a finite vertex type. -/
private theorem sum_piFinset_pow_div_pow_card_image_le_of_finite [DecidableEq α] [Finite α]
    {L : ℕ} [NeZero L] {γ m : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hm : 0 ≤ m)
    (A : Fin L → Finset α) :
    ∑ w ∈ Fintype.piFinset A with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
      γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w) ≤
        #(A 0) / m * ∏ t, (#(A (finRotate L t)) / m + 1 + L * γ) := by
  classical
  -- For `m = 0` both sides vanish, since every walk visits a vertex.
  rcases hm.eq_or_lt with rfl | hm
  · have : Nonempty (Fin L) := ⟨0⟩
    rw [div_zero, zero_mul]
    exact (sum_eq_zero fun w _ ↦ by
      rw [zero_pow (card_pos.mpr (univ_nonempty.image w)).ne', div_zero]).le
  let F : α × (Fin L → Option (α ⊕ Fin L)) → ℝ := fun c ↦ ∏ l, symbolWeight m γ (c.2 l)
  have hF (c) : 0 ≤ F c := prod_nonneg fun l _ ↦ symbolWeight_nonneg hm.le hγ₀ _
  let W := (Fintype.piFinset A).filter fun w : Fin L → α ↦
    ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t))
  calc _ ≤ ∑ w ∈ W, m⁻¹ * F (code w) := sum_le_sum fun w hw ↦
        pow_div_pow_card_image_le_inv_mul_prod_symbolWeight hm hγ₀ hγ₁ w (mem_filter.mp hw).2
    _ = m⁻¹ * ∑ c ∈ W.image code, F c := by
      rw [mul_sum, sum_image fun w _ w' _ h ↦ code_injective h]
    _ ≤ m⁻¹ * ∑ c ∈ A 0 ×ˢ Fintype.piFinset fun t ↦ allowedSymbols (A (finRotate L t)), F c := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ ↦ hF c)
        (inv_nonneg.mpr hm.le)
      intro c hc
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hc
      exact code_mem_of_mem_piFinset (mem_filter.mp hw).1
    _ = _ := by
      -- The weight of a code is a product over its steps of the weights of its symbols.
      simp only [F, sum_product, sum_const, nsmul_eq_mul]
      rw [← prod_univ_sum]
      simp only [sum_allowedSymbols_symbolWeight]
      ring

/-- Restricting to the union of the prescribed vertex sets preserves their cardinalities and
the weighted sum of words with repeated edges and an additional condition on the projected word. -/
private theorem exists_sum_piFinset_traceWord_weight_eq_subtype [DecidableEq α] {L : ℕ} {γ m : ℝ}
    (A : Fin L → Finset α)
    (P : (Fin L → α) → Prop) [DecidablePred P] :
    ∃ (S : Finset α) (A' : Fin L → Finset S), (∀ t, #(A' t) = #(A t)) ∧
      (∑ w ∈ Fintype.piFinset A with
          (∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t))) ∧ P w,
        γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w)) =
      ∑ w ∈ Fintype.piFinset A' with
          (∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t))) ∧
            P (Subtype.val ∘ w),
        γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w) := by
  let S := univ.biUnion A
  have hS (t : Fin L) : A t ⊆ S := fun x hx ↦ mem_biUnion.mpr ⟨t, mem_univ _, hx⟩
  let A' (t : Fin L) : Finset S := (A t).subtype (· ∈ S)
  refine ⟨S, A', fun t ↦ ?_, ?_⟩
  · rw [card_subtype, filter_true_of_mem (hS t)]
  have hA : (fun t ↦ (A' t).image Subtype.val) = A := funext fun t ↦ by
    rw [← Function.Embedding.coe_subtype, ← map_eq_image, subtype_map_of_mem (hS t)]
  have hpi : Fintype.piFinset A = (Fintype.piFinset A').image (Subtype.val ∘ ·) := by
    rw [← hA]
    exact Fintype.piFinset_image (fun _ ↦ Subtype.val) A'
  rw [hpi, filter_image, sum_image Subtype.val_injective.comp_left.injOn]
  refine sum_congr (filter_congr fun w _ ↦ ?_) fun w _ ↦ ?_
  · -- The projection is injective on edges, so it preserves the repeated edges.
    simp only [Function.comp_apply, ← Sym2.map_mk,
      (Sym2.map.injective Subtype.val_injective).eq_iff]
  · -- The projected walk visits as many vertices as the walk itself.
    rw [← image_image, card_image_of_injective _ Subtype.val_injective]

/-- **Weighted Füredi–Komlós enumeration with prescribed vertex sets.** Let `L ≠ 0`, `m ≥ 0`
and `0 ≤ γ ≤ 1`, and prescribe a finite set `A t` of vertices for each time `t` of a closed walk
of length `L`. Over the closed walks `w` with `w t ∈ A t` for every `t` that traverse each of their
edges `s(w t, w (t + 1))` at least twice, the sum of `γ ^ (2 * (L + 2 - 2 * t)) / m ^ t`, where `t`
is the number of vertices visited by `w`, is at most
`#(A 0) / m * ∏ t, (#(A (t + 1)) / m + 1 + L * γ)`, the times `t + 1` being read cyclically.

The factor of step `t` is the total weight of its possible code symbols: a discovery of one of the
`#(A (t + 1))` vertices allowed next, weighted `m⁻¹`, a forced step, or a jump to one of the `L`
times, weighted `γ`. For the closed bipartite words of sample covariance matrices, the sets
`A t` alternate between rows and columns. -/
theorem sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge [DecidableEq α] {L : ℕ}
    [NeZero L] {γ m : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hm : 0 ≤ m) (A : Fin L → Finset α) :
    ∑ w ∈ Fintype.piFinset A with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
      γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w) ≤
        #(A 0) / m * ∏ t, (#(A (finRotate L t)) / m + 1 + L * γ) := by
  classical
  obtain ⟨S, A', hcard, hsum⟩ :=
    exists_sum_piFinset_traceWord_weight_eq_subtype (γ := γ) (m := m) A (fun _ ↦ True)
  simp only [and_true] at hsum
  rw [hsum]
  have key := sum_piFinset_pow_div_pow_card_image_le_of_finite hγ₀ hγ₁ hm A'
  simpa only [hcard] using key

/-- **Weighted Füredi–Komlós enumeration.** Let `α` be a finite type of cardinality `n` and let
`0 ≤ γ ≤ 1`. Over the closed walks `w : Fin L → α` traversing each of their edges
`s(w t, w (t + 1))` at least twice, the sum of `γ ^ (2 * (L + 2 - 2 * t)) / n ^ t`, where `t` is
the number of vertices visited by `w`, is at most `(2 + L * γ) ^ L`.

When `L = 2 * m > 0`, the walks visiting `m + 1` vertices, the most possible, have weight `n⁻ᵗ`,
and every vertex fewer adds the factor `γ ^ 4`. In particular, for `0 < γ ≤ 1` there are at most
`n ^ t * (2 + L * γ) ^ L / γ ^ (2 * (L + 2 - 2 * t))` such walks visiting `t` vertices. -/
theorem sum_pow_div_pow_card_image_le_of_no_singleton_edge [DecidableEq α] [Fintype α] {L : ℕ}
    {γ : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    ∑ w : Fin L → α with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
      γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / (Fintype.card α : ℝ) ^ #(univ.image w) ≤
        (2 + L * γ) ^ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simpa using pow_le_one₀ hγ₀ hγ₁
  have : NeZero L := ⟨hL.ne'⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · have : IsEmpty (Fin L → α) := inferInstance
    simpa using pow_nonneg (add_nonneg zero_le_two (mul_nonneg (Nat.cast_nonneg L) hγ₀)) L
  have hn : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have key := sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge (L := L) hγ₀ hγ₁ hn.le
    fun _ ↦ (univ : Finset α)
  rw [Fintype.piFinset_univ] at key
  simp only [card_univ, div_self hn.ne', one_mul, prod_const, Fintype.card_fin] at key
  calc _ ≤ (1 + 1 + L * γ) ^ L := key
    _ = (2 + L * γ) ^ L := by norm_num

/-- The blockwise non-backtracking enumeration on a finite vertex type. -/
private theorem sum_piFinset_pow_div_pow_card_image_le_of_nonbacktracking_of_finite
    [DecidableEq α] [Finite α]
    {B M : ℕ} [NeZero (B * M)] {γ m R : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hm : 0 ≤ m)
    (A : Fin (B * M) → Finset α) (q : Fin B → Fin (M + 1) → ℝ)
    (hq : ∀ b i, 1 ≤ q b i ∧ q b i ≤ R)
    (hA : ∀ (b : Fin B) (i : Fin M),
      #(A (finRotate (B * M) (finProdFinEquiv (b, i)))) / m ≤ q b i.succ / q b i.castSucc) :
    ∑ w ∈ Fintype.piFinset A with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (B * M) s)) = s(w t, w (finRotate (B * M) t))) ∧
        (∀ (b : Fin B) (i j : Fin M), i.val + 1 = j.val →
          w (finProdFinEquiv (b, i)) ≠ w (finRotate (B * M) (finProdFinEquiv (b, j)))),
      γ ^ (2 * (B * M + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w) ≤
        #(A 0) / m * (((M : ℝ) + 1) * R * (1 + ((M : ℝ) + 1) * R * ((B * M : ℕ) * γ)) ^ M) ^ B := by
  classical
  rcases hm.eq_or_lt with rfl | hm
  · have : Nonempty (Fin (B * M)) := ⟨0⟩
    rw [div_zero, zero_mul]
    exact (sum_eq_zero fun w _ ↦ by
      rw [zero_pow (card_pos.mpr (univ_nonempty.image w)).ne', div_zero]).le
  let S (b : Fin B) (i : Fin M) := A (finRotate (B * M) (finProdFinEquiv (b, i)))
  let E (w : Fin (B * M) → α) := ((code w).1, fun b i ↦ (code w).2 (finProdFinEquiv (b, i)))
  let F (c : Fin B → Fin M → Option (α ⊕ Fin (B * M))) :=
    ∏ b, ∏ i, symbolWeight m γ (c b i)
  let C := A 0 ×ˢ Fintype.piFinset fun b ↦ blockCodes (L := B * M) (S b) false
  have hE : Function.Injective E := by
    intro w v h
    refine code_injective (Prod.ext (congrArg (fun x ↦ x.1) h) ?_)
    funext t
    obtain ⟨⟨b, i⟩, rfl⟩ := finProdFinEquiv.surjective t
    exact congrFun (congrFun (congrArg Prod.snd h) b) i
  have hprod (w : Fin (B * M) → α) : F (E w).2 = ∏ t, symbolWeight m γ ((code w).2 t) := by
    rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  let W := (Fintype.piFinset A).filter fun w ↦
    (∀ t, ∃ s ≠ t, s(w s, w (finRotate (B * M) s)) = s(w t, w (finRotate (B * M) t))) ∧
    (∀ (b : Fin B) (i j : Fin M), i.val + 1 = j.val →
      w (finProdFinEquiv (b, i)) ≠ w (finRotate (B * M) (finProdFinEquiv (b, j))))
  calc _ ≤ ∑ w ∈ W, m⁻¹ * F (E w).2 := sum_le_sum fun w hw ↦ by
        rw [hprod]
        exact pow_div_pow_card_image_le_inv_mul_prod_symbolWeight hm hγ₀ hγ₁ w
          (mem_filter.mp hw).2.1
    _ = m⁻¹ * ∑ c ∈ W.image E, F c.2 := by
      rw [mul_sum, sum_image hE.injOn]
    _ ≤ m⁻¹ * ∑ c ∈ C, F c.2 := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ ↦
        prod_nonneg fun _ _ ↦ prod_nonneg fun _ _ ↦ symbolWeight_nonneg hm.le hγ₀ _)
        (inv_nonneg.mpr hm.le)
      intro c hc
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hc
      obtain ⟨hw, -, hnb⟩ := mem_filter.mp hw
      exact mem_product.mpr ⟨(mem_product.mp (code_mem_of_mem_piFinset hw)).1,
        Fintype.mem_piFinset.mpr fun b ↦ code_mem_blockCodes hw b (hnb b)⟩
    _ = #(A 0) / m * ∏ b, blockWeight (L := B * M) (S b) false m γ := by
      simp only [C, F, sum_product, sum_const, nsmul_eq_mul, blockWeight]
      rw [prod_univ_sum _ (fun b (c : Fin M → Option (α ⊕ Fin (B * M))) ↦
        ∏ i, symbolWeight m γ (c i)), div_eq_mul_inv, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) hm.le)
      simpa only [prod_const, card_univ, Fintype.card_fin] using
        (prod_le_prod₀ (s := (univ : Finset (Fin B)))
          (fun b _ ↦ blockWeight_nonneg (L := B * M) (S b) false hm.le hγ₀)
          (fun b _ ↦ (blockWeight_le le_rfl (S b) hm hγ₀ (q b) (hq b) (hA b)).1))

/-- **Weighted enumeration of closed words that are non-backtracking within each block.**
Split the `B * M` steps into `B` successive blocks of length `M`. Consecutive steps within a
block use different edges. A reversal is allowed at any join. Restrict the vertex at time `t`
to the finite set `A t` and require each edge to occur at least twice.

For `0 ≤ γ ≤ 1` and `m ≥ 0`, the weight of a word visiting `v` vertices is
`γ ^ (2 * (B * M + 2 - 2 * v)) / m ^ v`.
If each discovery weight `#(A (t + 1)) / m` is bounded by the ratio of successive values of
`q` in the block, with `1 ≤ q ≤ R`, the total weight is bounded by `#(A 0) / m` times
`((M + 1) * R * (1 + (M + 1) * R * (B * M * γ)) ^ M) ^ B`.
The ratios allow the two alternating discovery weights of bipartite words to cancel. -/
theorem sum_piFinset_pow_div_pow_card_image_le_of_nonbacktracking [DecidableEq α]
    {B M : ℕ} [NeZero (B * M)] {γ m R : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hm : 0 ≤ m)
    (A : Fin (B * M) → Finset α) (q : Fin B → Fin (M + 1) → ℝ)
    (hq : ∀ b i, 1 ≤ q b i ∧ q b i ≤ R)
    (hA : ∀ (b : Fin B) (i : Fin M),
      #(A (finRotate (B * M) (finProdFinEquiv (b, i)))) / m ≤ q b i.succ / q b i.castSucc) :
    ∑ w ∈ Fintype.piFinset A with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (B * M) s)) = s(w t, w (finRotate (B * M) t))) ∧
        (∀ (b : Fin B) (i j : Fin M), i.val + 1 = j.val →
          w (finProdFinEquiv (b, i)) ≠ w (finRotate (B * M) (finProdFinEquiv (b, j)))),
      γ ^ (2 * (B * M + 2 - 2 * #(univ.image w))) / m ^ #(univ.image w) ≤
        #(A 0) / m * (((M : ℝ) + 1) * R * (1 + ((M : ℝ) + 1) * R * ((B * M : ℕ) * γ)) ^ M) ^ B := by
  classical
  obtain ⟨S, A', hcard, hsum⟩ :=
    exists_sum_piFinset_traceWord_weight_eq_subtype (γ := γ) (m := m) A (fun w ↦
      ∀ (b : Fin B) (i j : Fin M), i.val + 1 = j.val →
        w (finProdFinEquiv (b, i)) ≠ w (finRotate (B * M) (finProdFinEquiv (b, j))))
  rw [hsum]
  have key := sum_piFinset_pow_div_pow_card_image_le_of_nonbacktracking_of_finite
    hγ₀ hγ₁ hm A' q hq (by simpa only [hcard] using hA)
  simpa only [hcard, Function.comp_apply, ne_eq, Subtype.val_inj] using key

end TauCeti
