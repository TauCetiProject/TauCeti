/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Basic
public import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.Order.Interval.Finset.Nat

/-!
# Slope presentations of convex height sequences

A nonempty convex polygon is determined by its first point and the slopes of its unit
edges. This file gives the two one-sided presentations of that kind.

* `FiniteSlopeData Γ`: a starting index, an initial height, a horizontal length `d` and
  nondecreasing slopes indexed by `Fin d`. Length zero is a singleton polygon; the empty
  polygon has no presentation.
* `InfiniteSlopeData Γ`: a starting index, an initial height and a nondecreasing sequence
  of slopes indexed by `ℕ`, describing a polygon whose finite domain is a half-line.

The slopes and the initial height lie in an ordered additive group `Γ`, such as `ℚ` or `ℝ`,
rather than in a type containing slope sentinels. The represented heights are cumulative
sums on the finite domain and `⊤` outside it, so every actual edge has horizontal length one.

## Main results

* `FiniteSlopeData.heights_injective`, `InfiniteSlopeData.heights_injective`: slope data is
  determined by the heights it represents.
* `FiniteSlopeData.heights_map`, `InfiniteSlopeData.heights_map`: compatibility with
  order-preserving additive maps of value groups, such as `ℚ → ℝ`.
* `FiniteSlopeData.isConvexSeq_heights`, `FiniteSlopeData.unitSlope_heights`: real slope
  data represents a convex height sequence whose unit slopes are the given ones.
* `FiniteSlopeData.ofIsConvexSeq`, `FiniteSlopeData.heights_ofIsConvexSeq`,
  `FiniteSlopeData.ofIsConvexSeq_heights`: extraction of slope data from a convex height
  sequence with a specified finite domain, and both round trips.
* `FiniteSlopeData.exists_heights_eq_iff`: a height sequence has finite real slope data
  exactly when it is convex with nonempty finite domain.
* The corresponding `InfiniteSlopeData` statements, for convex height sequences with
  infinite domain.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
* A cumulative-sum construction of heights from monotone slopes also appears in William
  Coram's `PhD/Main/NewtonPolygons/OfSlopes.lean` at revision
  `eefb3d91f34b27d0bc7822140fa85fecae029884`.
-/

public section

open Finset

namespace TauCeti

variable {Γ Γ' : Type*} [AddCommGroup Γ] [Preorder Γ] [AddCommGroup Γ'] [Preorder Γ']

/-! ### Finite slope data -/

/-- The unit-slope presentation of a nonempty convex polygon with finite domain
`[start, start + length]`. The edge from `start + i` to `start + i + 1` has slope `slope i`.
Length zero represents a singleton polygon and carries no slopes. -/
structure FiniteSlopeData (Γ : Type*) [AddCommGroup Γ] [Preorder Γ] where
  /-- The first index of the finite domain. -/
  start : ℕ
  /-- The height at the first index. -/
  initialHeight : Γ
  /-- The horizontal length of the polygon, which is also its number of unit edges. -/
  length : ℕ
  /-- The slope of the `i`-th unit edge, counted from the left. -/
  slope : Fin length → Γ
  /-- Slopes are nondecreasing from left to right. -/
  monotone : Monotone slope

namespace FiniteSlopeData

variable (d : FiniteSlopeData Γ)

/-- The sum of the slopes of the first `k` unit edges. It is constant for `k ≥ d.length`. -/
def partialSum (k : ℕ) : Γ :=
  ∑ i ∈ univ.filter (fun i : Fin d.length => (i : ℕ) < k), d.slope i

/-- The empty partial sum vanishes. -/
@[simp]
theorem partialSum_zero : d.partialSum 0 = 0 := by
  simp [partialSum]

/-- Each further unit edge adds its slope to the partial sum. -/
theorem partialSum_succ {k : ℕ} (hk : k < d.length) :
    d.partialSum (k + 1) = d.partialSum k + d.slope ⟨k, hk⟩ := by
  have hfilter : univ.filter (fun i : Fin d.length => (i : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin d.length => (i : ℕ) < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [partialSum, partialSum, hfilter, sum_insert (by simp), add_comm]

/-- The partial sum over all unit edges is the total slope sum. -/
theorem partialSum_of_length_le {k : ℕ} (hk : d.length ≤ k) :
    d.partialSum k = ∑ i, d.slope i := by
  rw [partialSum, filter_true_of_mem fun i _ => i.2.trans_le hk]

/-- The heights represented by finite slope data: cumulative slope sums on
`[start, start + length]` and `⊤` elsewhere. -/
def heights (n : ℕ) : WithTop Γ :=
  if d.start ≤ n ∧ n ≤ d.start + d.length then
    ((d.initialHeight + d.partialSum (n - d.start) : Γ) : WithTop Γ)
  else ⊤

/-- The represented heights are finite exactly on `[start, start + length]`. -/
theorem heights_ne_top_iff {n : ℕ} :
    d.heights n ≠ ⊤ ↔ d.start ≤ n ∧ n ≤ d.start + d.length := by
  unfold heights
  split_ifs with h <;> simp [h]

/-- The represented heights are infinite exactly outside `[start, start + length]`. -/
theorem heights_eq_top_iff {n : ℕ} :
    d.heights n = ⊤ ↔ n < d.start ∨ d.start + d.length < n := by
  rw [← not_iff_not, ← ne_eq, heights_ne_top_iff]
  omega

/-- The finite domain of the represented heights is `[start, start + length]`. -/
theorem setOf_heights_ne_top :
    {n | d.heights n ≠ ⊤} = Set.Icc d.start (d.start + d.length) := by
  ext n
  exact d.heights_ne_top_iff

/-- On the finite domain, the height is the initial height plus a partial slope sum. -/
@[simp]
theorem heights_start_add {k : ℕ} (hk : k ≤ d.length) :
    d.heights (d.start + k) = ((d.initialHeight + d.partialSum k : Γ) : WithTop Γ) := by
  have hk' : d.start ≤ d.start + k ∧ d.start + k ≤ d.start + d.length := ⟨by omega, by omega⟩
  simp only [heights, hk', and_self, ite_true, Nat.add_sub_cancel_left]

/-- The height at the first index is the initial height. -/
@[simp]
theorem heights_start : d.heights d.start = (d.initialHeight : WithTop Γ) := by
  simpa using d.heights_start_add (Nat.zero_le _)

/-- The height at the right endpoint exceeds the initial height by the sum of all slopes. -/
theorem heights_start_add_length :
    d.heights (d.start + d.length) = ((d.initialHeight + ∑ i, d.slope i : Γ) : WithTop Γ) := by
  rw [heights_start_add _ le_rfl, partialSum_of_length_le _ le_rfl]

/-- Finite slope data is determined by the heights it represents: the starting index, the
initial height, the length and every slope agree. -/
theorem heights_injective :
    Function.Injective (heights : FiniteSlopeData Γ → ℕ → WithTop Γ) := by
  intro d e hde
  have hdom (n : ℕ) :
      (d.start ≤ n ∧ n ≤ d.start + d.length) ↔ (e.start ≤ n ∧ n ≤ e.start + e.length) := by
    rw [← heights_ne_top_iff, ← heights_ne_top_iff, hde]
  have hs : d.start = e.start := le_antisymm ((hdom e.start).2 ⟨le_rfl, by omega⟩).1
    ((hdom d.start).1 ⟨le_rfl, by omega⟩).1
  have hl : d.length = e.length := by
    have := (hdom (d.start + d.length)).1 ⟨by omega, le_rfl⟩
    have := (hdom (e.start + e.length)).2 ⟨by omega, le_rfl⟩
    omega
  have hsum (k : ℕ) (hk : k ≤ d.length) :
      d.initialHeight + d.partialSum k = e.initialHeight + e.partialSum k := by
    have := congr_fun hde (d.start + k)
    rw [heights_start_add _ hk, hs, heights_start_add _ (hl ▸ hk)] at this
    exact WithTop.coe_injective this
  have hy : d.initialHeight = e.initialHeight := by simpa using hsum 0 (Nat.zero_le _)
  obtain ⟨s, y, l, f, hf⟩ := d
  obtain ⟨s', y', l', f', hf'⟩ := e
  dsimp only at hs hl hy hsum
  subst hs hl hy
  have hf : f = f' := by
    funext i
    have h1 := hsum (i + 1) i.2
    have h0 := hsum i i.2.le
    rw [partialSum_succ _ i.2, partialSum_succ _ i.2, ← add_assoc, ← add_assoc, h0] at h1
    exact add_left_cancel h1
  subst hf
  rfl

/-- Transport finite slope data along an order-preserving additive map of value groups. -/
def map (f : Γ →+o Γ') : FiniteSlopeData Γ' where
  start := d.start
  initialHeight := f d.initialHeight
  length := d.length
  slope i := f (d.slope i)
  monotone := f.monotone'.comp d.monotone

@[simp]
theorem map_start (f : Γ →+o Γ') : (d.map f).start = d.start := (rfl)

@[simp]
theorem map_initialHeight (f : Γ →+o Γ') : (d.map f).initialHeight = f d.initialHeight := (rfl)

@[simp]
theorem map_length (f : Γ →+o Γ') : (d.map f).length = d.length := (rfl)

@[simp]
theorem map_slope (f : Γ →+o Γ') (i : Fin (d.map f).length) :
    (d.map f).slope i = f (d.slope (i.cast (d.map_length f))) := (rfl)

/-- Partial sums of transported slope data are the transported partial sums. -/
@[simp]
theorem partialSum_map (f : Γ →+o Γ') (k : ℕ) :
    (d.map f).partialSum k = f (d.partialSum k) := by
  simp only [partialSum, map_sum]
  -- `d.map f` has length `d.length` and slopes `f ∘ d.slope` by definition, so the two
  -- filtered sums run over the same index set.
  rfl

/-- The heights of transported slope data are the transported heights. -/
@[simp]
theorem heights_map (f : Γ →+o Γ') (n : ℕ) :
    (d.map f).heights n = WithTop.map f (d.heights n) := by
  rw [heights, heights, map_start, map_length, partialSum_map]
  split_ifs <;> simp

end FiniteSlopeData

/-! ### Infinite slope data -/

/-- The unit-slope presentation of a convex polygon whose finite domain is the half-line
`[start, ∞)`. The edge from `start + i` to `start + i + 1` has slope `slope i`. A terminal
ray is an eventually constant slope sequence; no slope is infinite. -/
structure InfiniteSlopeData (Γ : Type*) [AddCommGroup Γ] [Preorder Γ] where
  /-- The first index of the finite domain. -/
  start : ℕ
  /-- The height at the first index. -/
  initialHeight : Γ
  /-- The slope of the `i`-th unit edge, counted from the left. -/
  slope : ℕ → Γ
  /-- Slopes are nondecreasing from left to right. -/
  monotone : Monotone slope

namespace InfiniteSlopeData

variable (d : InfiniteSlopeData Γ)

/-- The heights represented by infinite slope data: cumulative slope sums from `start`
onwards and `⊤` before it. -/
def heights (n : ℕ) : WithTop Γ :=
  if d.start ≤ n then
    ((d.initialHeight + ∑ i ∈ range (n - d.start), d.slope i : Γ) : WithTop Γ)
  else ⊤

/-- The represented heights are finite exactly on `[start, ∞)`. -/
theorem heights_ne_top_iff {n : ℕ} : d.heights n ≠ ⊤ ↔ d.start ≤ n := by
  unfold heights
  split_ifs with h <;> simp [h]

/-- The represented heights are infinite exactly before `start`. -/
theorem heights_eq_top_iff {n : ℕ} : d.heights n = ⊤ ↔ n < d.start := by
  rw [← not_iff_not, ← ne_eq, heights_ne_top_iff, not_lt]

/-- The finite domain of the represented heights is `[start, ∞)`. -/
theorem setOf_heights_ne_top : {n | d.heights n ≠ ⊤} = Set.Ici d.start := by
  ext n
  exact d.heights_ne_top_iff

/-- On the finite domain, the height is the initial height plus a partial slope sum. -/
@[simp]
theorem heights_start_add (k : ℕ) :
    d.heights (d.start + k) =
      ((d.initialHeight + ∑ i ∈ range k, d.slope i : Γ) : WithTop Γ) := by
  simp only [heights, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]

/-- The height at the first index is the initial height. -/
@[simp]
theorem heights_start : d.heights d.start = (d.initialHeight : WithTop Γ) := by
  simpa using d.heights_start_add 0

/-- Infinite slope data is determined by the heights it represents: the starting index, the
initial height and every slope agree. -/
theorem heights_injective :
    Function.Injective (heights : InfiniteSlopeData Γ → ℕ → WithTop Γ) := by
  intro d e hde
  have hdom (n : ℕ) : d.start ≤ n ↔ e.start ≤ n := by
    rw [← heights_ne_top_iff, ← heights_ne_top_iff, hde]
  have hs : d.start = e.start :=
    le_antisymm ((hdom e.start).2 le_rfl) ((hdom d.start).1 le_rfl)
  have hsum (k : ℕ) :
      d.initialHeight + ∑ i ∈ range k, d.slope i =
        e.initialHeight + ∑ i ∈ range k, e.slope i := by
    have := congr_fun hde (d.start + k)
    rw [heights_start_add, hs, heights_start_add] at this
    exact WithTop.coe_injective this
  have hy : d.initialHeight = e.initialHeight := by simpa using hsum 0
  obtain ⟨s, y, f, hf⟩ := d
  obtain ⟨s', y', f', hf'⟩ := e
  dsimp only at hs hy hsum
  subst hs hy
  have hf : f = f' := by
    funext i
    have h1 := hsum (i + 1)
    rw [sum_range_succ, sum_range_succ, ← add_assoc, ← add_assoc, hsum i] at h1
    exact add_left_cancel h1
  subst hf
  rfl

/-- Transport infinite slope data along an order-preserving additive map of value groups. -/
def map (f : Γ →+o Γ') : InfiniteSlopeData Γ' where
  start := d.start
  initialHeight := f d.initialHeight
  slope i := f (d.slope i)
  monotone := f.monotone'.comp d.monotone

@[simp]
theorem map_start (f : Γ →+o Γ') : (d.map f).start = d.start := (rfl)

@[simp]
theorem map_initialHeight (f : Γ →+o Γ') : (d.map f).initialHeight = f d.initialHeight := (rfl)

@[simp]
theorem map_slope (f : Γ →+o Γ') (i : ℕ) : (d.map f).slope i = f (d.slope i) := (rfl)

/-- The heights of transported slope data are the transported heights. -/
@[simp]
theorem heights_map (f : Γ →+o Γ') (n : ℕ) :
    (d.map f).heights n = WithTop.map f (d.heights n) := by
  simp only [heights, map_start, map_initialHeight, map_slope]
  split_ifs <;> simp [map_sum]

end InfiniteSlopeData

/-! ### Real slope data and convex height sequences -/

namespace FiniteSlopeData

variable (d : FiniteSlopeData ℝ)

/-- The unit slopes of the represented heights are the given slopes. -/
theorem unitSlope_heights (i : Fin d.length) :
    unitSlope d.heights (d.start + i) = d.slope i := by
  rw [unitSlope_def, Nat.add_assoc, heights_start_add _ i.2, heights_start_add _ i.2.le,
    WithTop.untop₀_coe, WithTop.untop₀_coe, partialSum_succ _ i.2]
  simp

/-- Real finite slope data represents a convex height sequence. -/
theorem isConvexSeq_heights : IsConvexSeq d.heights := by
  refine ⟨?_, ?_⟩
  · rw [setOf_heights_ne_top]
    exact Set.ordConnected_Icc
  · intro i hi j hj hij
    rw [mem_finiteEdges, heights_ne_top_iff, heights_ne_top_iff] at hi hj
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi.1.1
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hj.1.1
    have ha : a < d.length := by omega
    have hb : b < d.length := by omega
    calc unitSlope d.heights (d.start + a) = d.slope ⟨a, ha⟩ := d.unitSlope_heights ⟨a, ha⟩
      _ ≤ d.slope ⟨b, hb⟩ := d.monotone (Fin.mk_le_mk.mpr (by omega))
      _ = unitSlope d.heights (d.start + b) := (d.unitSlope_heights ⟨b, hb⟩).symm

/-- The finite slope data of a convex height sequence whose finite domain is `[l, l + k]`. -/
noncomputable def ofIsConvexSeq {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {l k : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ l + k) : FiniteSlopeData ℝ where
  start := l
  initialHeight := (h l).untop₀
  length := k
  slope i := unitSlope h (l + i)
  monotone i j hij := by
    have hi := i.2
    have hj := j.2
    have hij' : (i : ℕ) ≤ j := hij
    exact hh.monotoneOn
      (mem_finiteEdges.2 ⟨(hdom _).2 ⟨by omega, by omega⟩, (hdom _).2 ⟨by omega, by omega⟩⟩)
      (mem_finiteEdges.2 ⟨(hdom _).2 ⟨by omega, by omega⟩, (hdom _).2 ⟨by omega, by omega⟩⟩)
      (by omega)

variable {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {l k : ℕ}
  (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ l + k)

@[simp]
theorem ofIsConvexSeq_start : (ofIsConvexSeq hh hdom).start = l := (rfl)

@[simp]
theorem ofIsConvexSeq_initialHeight :
    (ofIsConvexSeq hh hdom).initialHeight = (h l).untop₀ := (rfl)

@[simp]
theorem ofIsConvexSeq_length : (ofIsConvexSeq hh hdom).length = k := (rfl)

@[simp]
theorem ofIsConvexSeq_slope (i : Fin (ofIsConvexSeq hh hdom).length) :
    (ofIsConvexSeq hh hdom).slope i = unitSlope h (l + i) := (rfl)

private theorem partialSum_ofIsConvexSeq {m : ℕ} (hm : m ≤ k) :
    (ofIsConvexSeq hh hdom).partialSum m = ∑ i ∈ range m, unitSlope h (l + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [partialSum_succ _ (by simpa using hm), ih (by omega), sum_range_succ,
      ofIsConvexSeq_slope]

/-- Extracting slope data and reconstructing heights recovers the height sequence. -/
theorem heights_ofIsConvexSeq : (ofIsConvexSeq hh hdom).heights = h := by
  funext n
  by_cases hn : l ≤ n ∧ n ≤ l + k
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn.1
    have hm : m ≤ k := by omega
    have := heights_start_add (ofIsConvexSeq hh hdom) (k := m) (by simpa using hm)
    rw [ofIsConvexSeq_start] at this
    rw [this, eq_coe_add_sum_unitSlope ((hdom _).2 hn) (Nat.le_add_right l m),
      partialSum_ofIsConvexSeq hh hdom hm, ofIsConvexSeq_initialHeight,
      sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  · have hd := (ofIsConvexSeq hh hdom).heights_ne_top_iff (n := n)
    simp only [ofIsConvexSeq_start, ofIsConvexSeq_length] at hd
    rw [not_ne_iff.mp (hd.not.mpr hn), not_ne_iff.mp ((hdom n).not.mpr hn)]

/-- Reconstructing heights and extracting slope data recovers the slope data. -/
@[simp]
theorem ofIsConvexSeq_heights :
    ofIsConvexSeq d.isConvexSeq_heights (fun _ => d.heights_ne_top_iff) = d :=
  heights_injective (heights_ofIsConvexSeq _ _)

/-- A real height sequence is represented by finite slope data exactly when it is convex
and its finite domain is nonempty and finite. -/
theorem exists_heights_eq_iff {h : ℕ → WithTop ℝ} :
    (∃ d : FiniteSlopeData ℝ, d.heights = h) ↔
      IsConvexSeq h ∧ {n | h n ≠ ⊤}.Nonempty ∧ {n | h n ≠ ⊤}.Finite := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [setOf_heights_ne_top]
    exact ⟨d.isConvexSeq_heights, Set.nonempty_Icc.mpr (Nat.le_add_right _ _),
      Set.finite_Icc _ _⟩
  · rintro ⟨hh, hne, hfin⟩
    have hS := (hne.ordConnected_iff_of_bdd (OrderBot.bddBelow _) hfin.bddAbove).1
      hh.ordConnected
    obtain ⟨x, hx⟩ := hne
    have hx' := hS ▸ hx
    have hdom (n : ℕ) : h n ≠ ⊤ ↔ sInf {n | h n ≠ ⊤} ≤ n ∧
        n ≤ sInf {n | h n ≠ ⊤} + (sSup {n | h n ≠ ⊤} - sInf {n | h n ≠ ⊤}) := by
      rw [Nat.add_sub_cancel' (hx'.1.trans hx'.2)]
      exact Set.ext_iff.mp hS n
    exact ⟨ofIsConvexSeq hh hdom, heights_ofIsConvexSeq hh hdom⟩

end FiniteSlopeData

namespace InfiniteSlopeData

variable (d : InfiniteSlopeData ℝ)

/-- The unit slopes of the represented heights are the given slopes. -/
theorem unitSlope_heights (i : ℕ) : unitSlope d.heights (d.start + i) = d.slope i := by
  rw [unitSlope_def, Nat.add_assoc, heights_start_add, heights_start_add, WithTop.untop₀_coe,
    WithTop.untop₀_coe, sum_range_succ, ← add_assoc, add_sub_cancel_left]

/-- Real infinite slope data represents a convex height sequence. -/
theorem isConvexSeq_heights : IsConvexSeq d.heights := by
  refine ⟨?_, ?_⟩
  · rw [setOf_heights_ne_top]
    exact Set.ordConnected_Ici
  · intro i hi j hj hij
    rw [mem_finiteEdges, heights_ne_top_iff, heights_ne_top_iff] at hi hj
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi.1
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hj.1
    rw [unitSlope_heights, unitSlope_heights]
    exact d.monotone (by omega)

/-- The infinite slope data of a convex height sequence whose finite domain is `[l, ∞)`. -/
noncomputable def ofIsConvexSeq {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {l : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n) : InfiniteSlopeData ℝ where
  start := l
  initialHeight := (h l).untop₀
  slope i := unitSlope h (l + i)
  monotone i j hij :=
    hh.monotoneOn (mem_finiteEdges.2 ⟨(hdom _).2 (by omega), (hdom _).2 (by omega)⟩)
      (mem_finiteEdges.2 ⟨(hdom _).2 (by omega), (hdom _).2 (by omega)⟩) (by omega)

variable {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {l : ℕ} (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n)

@[simp]
theorem ofIsConvexSeq_start : (ofIsConvexSeq hh hdom).start = l := (rfl)

@[simp]
theorem ofIsConvexSeq_initialHeight :
    (ofIsConvexSeq hh hdom).initialHeight = (h l).untop₀ := (rfl)

@[simp]
theorem ofIsConvexSeq_slope (i : ℕ) : (ofIsConvexSeq hh hdom).slope i = unitSlope h (l + i) :=
  (rfl)

/-- Extracting slope data and reconstructing heights recovers the height sequence. -/
theorem heights_ofIsConvexSeq : (ofIsConvexSeq hh hdom).heights = h := by
  funext n
  by_cases hn : l ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := heights_start_add (ofIsConvexSeq hh hdom) m
    simp only [ofIsConvexSeq_start, ofIsConvexSeq_initialHeight, ofIsConvexSeq_slope] at this
    rw [this, eq_coe_add_sum_unitSlope ((hdom _).2 hn) (Nat.le_add_right l m),
      sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  · have hd := (ofIsConvexSeq hh hdom).heights_ne_top_iff (n := n)
    rw [ofIsConvexSeq_start] at hd
    rw [not_ne_iff.mp (hd.not.mpr hn), not_ne_iff.mp ((hdom n).not.mpr hn)]

/-- Reconstructing heights and extracting slope data recovers the slope data. -/
@[simp]
theorem ofIsConvexSeq_heights :
    ofIsConvexSeq d.isConvexSeq_heights (fun _ => d.heights_ne_top_iff) = d :=
  heights_injective (heights_ofIsConvexSeq _ _)

/-- A real height sequence is represented by infinite slope data exactly when it is convex
and its finite domain is infinite. -/
theorem exists_heights_eq_iff {h : ℕ → WithTop ℝ} :
    (∃ d : InfiniteSlopeData ℝ, d.heights = h) ↔
      IsConvexSeq h ∧ {n | h n ≠ ⊤}.Infinite := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [setOf_heights_ne_top]
    exact ⟨d.isConvexSeq_heights, Set.Ici_infinite _⟩
  · rintro ⟨hh, hinf⟩
    have hmem := Nat.sInf_mem hinf.nonempty
    have hdom (n : ℕ) : h n ≠ ⊤ ↔ sInf {n | h n ≠ ⊤} ≤ n := by
      refine ⟨fun hn => Nat.sInf_le hn, fun hn => ?_⟩
      obtain ⟨m, hm, hnm⟩ := not_bddAbove_iff.mp hinf.not_bddAbove n
      exact hh.ordConnected.out hmem hm ⟨hn, hnm.le⟩
    exact ⟨ofIsConvexSeq hh hdom, heights_ofIsConvexSeq hh hdom⟩

end InfiniteSlopeData

end TauCeti
