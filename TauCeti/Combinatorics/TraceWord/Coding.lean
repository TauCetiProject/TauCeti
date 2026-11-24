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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

## Main result

* `TauCeti.sum_pow_div_pow_card_image_le_of_no_singleton_edge`: the weighted enumeration bound.

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

end Code

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
  classical
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simpa using pow_le_one₀ hγ₀ hγ₁
  have : NeZero L := ⟨hL.ne'⟩
  have hbase : 0 ≤ 2 + L * γ := add_nonneg zero_le_two (mul_nonneg (Nat.cast_nonneg _) hγ₀)
  rcases isEmpty_or_nonempty α with hα | hα
  · have : IsEmpty (Fin L → α) := inferInstance
    simpa using pow_nonneg hbase L
  set n : ℝ := ((Fintype.card α : ℕ) : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let F : α × (Fin L → Option (α ⊕ Fin L)) → ℝ := fun c ↦ ∏ l, symbolWeight n γ (c.2 l)
  have hF (c) : 0 ≤ F c := prod_nonneg fun l _ ↦ symbolWeight_nonneg hn.le hγ₀ _
  calc _ ≤ ∑ w : Fin L → α with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
        n⁻¹ * F (code w) := sum_le_sum fun w hw ↦
      pow_div_pow_card_image_le_inv_mul_prod_symbolWeight hn hγ₀ hγ₁ w (mem_filter.mp hw).2
    _ = n⁻¹ * ∑ c ∈ (univ.filter fun w : Fin L → α ↦
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t))).image
          code, F c := by
      rw [mul_sum, sum_image fun w _ w' _ h ↦ code_injective h]
    _ ≤ n⁻¹ * ∑ c, F c :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _)
        fun c _ _ ↦ hF c) (inv_nonneg.mpr hn.le)
    _ = (∑ c : Option (α ⊕ Fin L), symbolWeight n γ c) ^ L := by
      rw [Fintype.sum_prod_type, Fintype.sum_pow]
      simp only [F, sum_const, card_univ, nsmul_eq_mul]
      rw [← hn_def, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    _ = _ := by
      congr 1
      rw [Fintype.sum_option, Fintype.sum_sum_type]
      simp only [symbolWeight, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← hn_def, mul_inv_cancel₀ hn.ne']
      ring

end TauCeti
