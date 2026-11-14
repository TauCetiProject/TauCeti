/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Fin.VecNotation
public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Transporting a closed section

The derived transformation D2 of Makanin's process (Kharlampovich–Myasnikov, §5.2) cuts a closed
section out of a generalised equation `Ω`, with its bases and boundary connections, and puts it
between two other closed sections or at the end. For closed boundaries `i ≤ j ≤ m`,
`TauCeti.GenEq.moveSection` moves the items of `[i, j]` behind the items of `[j, m]`: the items
`0, …, i - 1` and `m, …` keep their place, the items of `[j, m]` move down by `j - i`, and the
items of `[i, j]` move up by `m - j`. No base crosses a closed boundary, so every base lies in
one of the four blocks and moves with it. Moving a section to the left is moving the block before
it to the right. When `i ≤ j ≤ m` fails, nothing moves (`TauCeti.GenEq.moveSection_eq_self`).

The result has the same number of items, its equations are the equations of `Ω` with the items
renamed, its bases, items and boundaries are those of `Ω` moved, the renaming induces an
`F(A)`-isomorphism of coordinate groups (`TauCeti.GenEq.moveSectionHom`), and the solutions
correspond, with the words permuted (`TauCeti.GenEq.solutionEquivMoveSection`). Moving the block
`[i, i + (m - j)]` of the result back behind `[i + (m - j), m]` restores `Ω`.

## Main definitions

* `TauCeti.GenEq.moveItem`, `TauCeti.GenEq.moveBoundary`: the permutations of the items and of the
  boundaries moving the block `[i, j]` behind the block `[j, m]`.
* `TauCeti.GenEq.moveSection`: the generalised equation with the block `[i, j]` moved behind the
  block `[j, m]`.
* `TauCeti.GenEq.moveSectionHom`: the `F(A)`-homomorphism of coordinate groups induced by the
  permutation of the items.
* `TauCeti.GenEq.solutionEquivMoveSection`: the bijection between the solutions.

## Main results

* `TauCeti.GenEq.equations_moveSection`: the equations of the moved equation are the equations
  of `Ω` with the items renamed.
* `TauCeti.GenEq.isClosedBoundary_moveSection_iff`: a boundary of the moved equation is closed
  exactly when the boundary it comes from is; likewise for crossing, open boundaries, the items
  of a base, constant and free items, and the degree.
* `TauCeti.GenEq.moveSection_moveSection`: moving the section back restores `Ω`.
* `TauCeti.GenEq.isFormallyConsistent_moveSection_iff`: the moved equation is formally consistent
  exactly when `Ω` is.
* `TauCeti.GenEq.comp_moveItem_mem_V_iff`: the group solutions correspond.
* `TauCeti.GenEq.moveSectionHom_bijective`: the coordinate groups are isomorphic.
* `TauCeti.GenEq.toHom_comp_moveSectionHom_eq_iff`: a solution of `Ω` factors through the
  isomorphism exactly through the corresponding solution of the moved equation.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D2.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars)

variable {A : Type*} (Ω : GenEq A)

/-! ### Moving a block of places -/

/-- The new place of the item (or of the left end-point of a base) `k` when the block `[i, j]` is
moved behind the block `[j, m]`: the places before `i` and from `m` on are fixed, those of
`[i, j]` move up by `m - j` and those of `[j, m]` move down by `j - i`. When `i ≤ j ≤ m` fails,
every place is fixed (`TauCeti.GenEq.moveIdx_eq_id`). -/
def moveIdx (i j m k : ℕ) : ℕ :=
  if k < i then k else if k < j then k + (m - j) else if k < m then k - (j - i) else k

@[grind =]
theorem moveIdx_def (i j m k : ℕ) : moveIdx i j m k =
    if k < i then k else if k < j then k + (m - j) else if k < m then k - (j - i) else k :=
  (rfl)

/-- The places before the block `[i, j]` are fixed. -/
theorem moveIdx_eq_self_of_lt {i j m k : ℕ} (hk : k < i) : moveIdx i j m k = k := by
  grind

/-- The places of the block `[i, j]` move up by `m - j`. -/
theorem moveIdx_eq_add_of_le_of_lt {i j m k : ℕ} (hi : i ≤ k) (hj : k < j) :
    moveIdx i j m k = k + (m - j) := by
  grind

/-- The places of the block `[j, m]` move down by `j - i`. -/
theorem moveIdx_eq_sub_of_le_of_lt {i j m k : ℕ} (hj : j ≤ k) (hm : k < m) :
    moveIdx i j m k = k - (j - i) := by
  grind

/-- The places from `m` on are fixed. -/
theorem moveIdx_eq_self_of_le {i j m k : ℕ} (hk : m ≤ k) : moveIdx i j m k = k := by
  grind

/-- Moving an empty block, or moving a block behind an empty block, fixes every place; in
particular nothing moves when `i ≤ j ≤ m` fails. -/
theorem moveIdx_eq_id {i j m : ℕ} (h : j ≤ i ∨ m ≤ j) : moveIdx i j m = id :=
  funext fun _ => by grind

/-- Moving blocks inside `[0, n]` keeps the places below `n`. -/
theorem moveIdx_lt {i j m n k : ℕ} (hm : m ≤ n) (hk : k < n) : moveIdx i j m k < n := by
  grind

/-- Moving the block `[i, j]` behind `[j, m]` and then the block `[i, i + (m - j)]` behind
`[i + (m - j), m]` restores every place. -/
@[simp]
theorem moveIdx_moveIdx {i j m k : ℕ} : moveIdx i (i + (m - j)) m (moveIdx i j m k) = k := by
  grind

/-- Moving the block `[i, i + (m - j)]` behind `[i + (m - j), m]` and then the block `[i, j]`
behind `[j, m]` restores every place. -/
@[simp]
theorem moveIdx_moveIdx_add_sub {i j m k : ℕ} :
    moveIdx i j m (moveIdx i (i + (m - j)) m k) = k := by
  grind

/-- `moveIdx i j m` is injective. -/
theorem moveIdx_injective {i j m : ℕ} : Function.Injective (moveIdx i j m) :=
  Function.LeftInverse.injective fun _ => moveIdx_moveIdx

/-- `moveIdx i j m` is a bijection of `ℕ`. -/
theorem moveIdx_bijective {i j m : ℕ} : Function.Bijective (moveIdx i j m) :=
  ⟨moveIdx_injective, Function.RightInverse.surjective fun _ => moveIdx_moveIdx_add_sub⟩

/-- Disjoint intervals `[a, b]`, `[c, d]` that none of the boundaries `i`, `j`, `m` cuts stay
disjoint when the blocks are moved. -/
private theorem moveIdx_disjoint {i j m a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (hi : (i ≤ a ∨ b ≤ i) ∧ (i ≤ c ∨ d ≤ i)) (hj : (j ≤ a ∨ b ≤ j) ∧ (j ≤ c ∨ d ≤ j))
    (hm : (m ≤ a ∨ b ≤ m) ∧ (m ≤ c ∨ d ≤ m)) (h : b ≤ c ∨ d ≤ a) :
    moveIdx i j m a + (b - a) ≤ moveIdx i j m c ∨
      moveIdx i j m c + (d - c) ≤ moveIdx i j m a := by
  unfold moveIdx
  split_ifs <;> lia

/-- A block `[a, a + d]` that none of the boundaries `i`, `j`, `m` cuts moves as a whole. -/
theorem moveIdx_add {i j m a d t : ℕ} (hi : i ≤ a ∨ a + d ≤ i) (hj : j ≤ a ∨ a + d ≤ j)
    (hm : m ≤ a ∨ a + d ≤ m) (ht : t < d) : moveIdx i j m (a + t) = moveIdx i j m a + t := by
  unfold moveIdx
  split_ifs <;> lia

/-- The permutation of the items moving the block `[i, j]` behind the block `[j, m]`. -/
def moveItem (i j m : Fin (Ω.numItems + 1)) : Equiv.Perm (Fin Ω.numItems) where
  toFun k := ⟨moveIdx i j m k, moveIdx_lt m.is_le k.is_lt⟩
  invFun k := ⟨moveIdx i (i + (m - j)) m k, moveIdx_lt m.is_le k.is_lt⟩
  left_inv _ := Fin.ext moveIdx_moveIdx
  right_inv _ := Fin.ext moveIdx_moveIdx_add_sub

/-- The permutation moving the block `[i, j]` behind `[j, m]` sends the item `k` to
`moveIdx i j m k`. -/
@[simp, grind =]
theorem coe_moveItem (i j m : Fin (Ω.numItems + 1)) (k : Fin Ω.numItems) :
    (Ω.moveItem i j m k : ℕ) = moveIdx i j m k :=
  (rfl)

/-- The inverse of the permutation moving the block `[i, j]` behind `[j, m]` moves the block
`[i, i + (m - j)]` behind `[i + (m - j), m]`. -/
@[simp, grind =]
theorem coe_moveItem_symm (i j m : Fin (Ω.numItems + 1)) (k : Fin Ω.numItems) :
    ((Ω.moveItem i j m).symm k : ℕ) = moveIdx i (i + (m - j)) m k :=
  (rfl)

/-- The permutation of the boundaries moving the block `[i, j]` behind the block `[j, m]`: a
boundary goes with the item to its right, and the last boundary stays. -/
def moveBoundary (i j m : Fin (Ω.numItems + 1)) : Equiv.Perm (Fin (Ω.numItems + 1)) where
  toFun k := ⟨moveIdx i j m k, moveIdx_lt m.is_lt.le k.is_lt⟩
  invFun k := ⟨moveIdx i (i + (m - j)) m k, moveIdx_lt m.is_lt.le k.is_lt⟩
  left_inv _ := Fin.ext moveIdx_moveIdx
  right_inv _ := Fin.ext moveIdx_moveIdx_add_sub

/-- The permutation of the boundaries moving the block `[i, j]` behind `[j, m]` sends the boundary
`k` to `moveIdx i j m k`. -/
@[simp, grind =]
theorem coe_moveBoundary (i j m : Fin (Ω.numItems + 1)) (k : Fin (Ω.numItems + 1)) :
    (Ω.moveBoundary i j m k : ℕ) = moveIdx i j m k :=
  (rfl)

/-- The inverse of the permutation of the boundaries moving the block `[i, j]` behind `[j, m]`
moves the block `[i, i + (m - j)]` behind `[i + (m - j), m]`. -/
@[simp, grind =]
theorem coe_moveBoundary_symm (i j m : Fin (Ω.numItems + 1)) (k : Fin (Ω.numItems + 1)) :
    ((Ω.moveBoundary i j m).symm k : ℕ) = moveIdx i (i + (m - j)) m k :=
  (rfl)

/-- When `i ≤ j ≤ m` fails, or one of the two blocks is empty, no item moves. -/
theorem moveItem_eq_one {i j m : Fin (Ω.numItems + 1)} (h : j ≤ i ∨ m ≤ j) :
    Ω.moveItem i j m = 1 :=
  Equiv.ext fun k => Fin.ext <| congrFun (moveIdx_eq_id (h.imp Fin.le_def.1 Fin.le_def.1)) k

/-- When `i ≤ j ≤ m` fails, or one of the two blocks is empty, no boundary moves. -/
theorem moveBoundary_eq_one {i j m : Fin (Ω.numItems + 1)} (h : j ≤ i ∨ m ≤ j) :
    Ω.moveBoundary i j m = 1 :=
  Equiv.ext fun k => Fin.ext <| congrFun (moveIdx_eq_id (h.imp Fin.le_def.1 Fin.le_def.1)) k

/-! ### Moving a section -/

variable {Ω} in
/-- No closed boundary cuts a base, so the move shifts a base as a whole: a place `p` of the base
`μ`, that is `α(μ) ≤ p < β(μ)`, moves to the place at distance `p - α(μ)` from
`moveIdx i j m α(μ)`. -/
theorem moveIdx_eq_of_le_of_lt {i j m : Fin (Ω.numItems + 1)} (hi : Ω.IsClosedBoundary i)
    (hj : Ω.IsClosedBoundary j) (hm : Ω.IsClosedBoundary m) (μ : Fin Ω.numBases) {p : ℕ}
    (h₁ : Ω.left μ ≤ p) (h₂ : p < Ω.right μ) :
    moveIdx i j m p = moveIdx i j m (Ω.left μ) + (p - Ω.left μ) := by
  have := hi.le_left_or_right_le μ
  have := hj.le_left_or_right_le μ
  have := hm.le_left_or_right_le μ
  have := moveIdx_add (i := i) (j := j) (m := m) (a := Ω.left μ) (d := Ω.right μ - Ω.left μ)
    (t := p - Ω.left μ) (by lia) (by lia) (by lia) (by lia)
  rwa [Nat.add_sub_cancel' h₁] at this

/-- **D2.** Move the items between the closed boundaries `i ≤ j` behind the items between `j`
and the closed boundary `m ≥ j`, with their bases, constant bases and boundary connections. A
base starting at `α` keeps its length and starts at `moveIdx i j m α`; a boundary `p` strictly
inside a base goes to `moveIdx i j m p`. When `i ≤ j ≤ m` fails, nothing moves
(`TauCeti.GenEq.moveSection_eq_self`). -/
abbrev moveSection (i j m : Fin (Ω.numItems + 1)) (hi : Ω.IsClosedBoundary i)
    (hj : Ω.IsClosedBoundary j) (hm : Ω.IsClosedBoundary m) : GenEq A where
  numItems := Ω.numItems
  numBases := Ω.numBases
  left μ := Ω.moveBoundary i j m (Ω.left μ)
  right μ := ⟨moveIdx i j m (Ω.left μ) + (Ω.right μ - Ω.left μ), by
    -- The last item of the base moves to a place below `ρ`.
    have h₁ := Fin.lt_def.1 (Ω.left_lt_right μ)
    have := moveIdx_eq_of_le_of_lt hi hj hm μ (p := Ω.right μ - 1) (by lia) (by lia)
    have := moveIdx_lt (i := i) (j := j) (k := Ω.right μ - 1) m.is_le (by lia)
    lia⟩
  left_lt_right μ := by
    have := Ω.left_lt_right μ
    simp only [Fin.lt_def, coe_moveBoundary] at this ⊢
    lia
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.map
    ((Ω.moveItem i j m).toEmbedding.prodMap (Function.Embedding.refl _))
  connections := Ω.connections.image fun c =>
    (Ω.moveBoundary i j m c.1, c.2.1, Ω.moveBoundary i j m c.2.2)
  bounds_of_mem_connections := by
    simp only [Finset.mem_image]
    rintro _ ⟨⟨p, μ, q⟩, hc, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc
    simp only [Fin.lt_def, coe_moveBoundary] at h₁ h₂ h₃ h₄ ⊢
    -- A boundary strictly inside a base moves with the base.
    have := moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂
    have := moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄
    lia
  dual_mem_connections := by
    simp only [Finset.mem_image]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, Ω.dual_mem_connections c hc, rfl⟩

/-! ### The equations of the moved equation -/

/-- A segment `h[x, x + d]` that none of the boundaries `i`, `j`, `m` cuts moves to the segment of
the same length starting at `moveIdx i j m x`, with the items renamed. -/
theorem segment_moveIdx {i j m : Fin (Ω.numItems + 1)} {x d : ℕ}
    (hi : (i : ℕ) ≤ x ∨ x + d ≤ i) (hj : (j : ℕ) ≤ x ∨ x + d ≤ j) (hm : (m : ℕ) ≤ x ∨ x + d ≤ m)
    (s : Bool) :
    Ω.segment (moveIdx i j m x) (moveIdx i j m x + d) s =
      (Ω.segment x (x + d) s).map (Prod.map (Sum.map (Ω.moveItem i j m) id) id) := by
  have hadd {t : ℕ} (ht : t < d) : moveIdx i j m (x + t) = moveIdx i j m x + t :=
    moveIdx_add hi hj hm ht
  -- The moved segment has as many items as the segment: it ends before the last boundary when the
  -- segment does, and otherwise the segment lies behind `m`, where nothing moves.
  have hlen : min (moveIdx i j m x + d) Ω.numItems - moveIdx i j m x =
      min (x + d) Ω.numItems - x := by
    by_cases hx : x + d ≤ Ω.numItems
    · rcases Nat.eq_zero_or_pos d with rfl | h
      · lia
      · have := moveIdx_lt (i := i) (j := j) (k := x + (d - 1)) m.is_le (by lia)
        rw [hadd (by lia)] at this
        lia
    · have := m.is_le
      rw [moveIdx_eq_self_of_le (by lia)]
  have key : ((List.finRange Ω.numItems).take (moveIdx i j m x + d)).drop (moveIdx i j m x) =
      (((List.finRange Ω.numItems).take (x + d)).drop x).map (Ω.moveItem i j m) := by
    refine List.ext_getElem ?_ fun t h₁ h₂ => Fin.ext ?_
    · simpa only [List.length_drop, List.length_take, List.length_finRange, List.length_map,
        min_comm] using hlen
    · simp only [List.getElem_drop, List.getElem_take, List.getElem_finRange, List.getElem_map,
        coe_moveItem, Fin.val_cast]
      simp only [List.length_drop, List.length_take, List.length_finRange] at h₁
      exact (hadd (by lia)).symm
  cases s
  · rw [segment_false, segment_false, segment_true, segment_true, key]
    simp [FreeGroup.invRev, List.map_reverse, List.map_map, Function.comp_def]
  · rw [segment_true, segment_true, key, List.map_map, List.map_map]
    rfl

variable {Ω} {i j m : Fin (Ω.numItems + 1)}
  (hi : Ω.IsClosedBoundary i) (hj : Ω.IsClosedBoundary j) (hm : Ω.IsClosedBoundary m)

/-- The constant bases of the moved equation are those of `Ω` with their items moved. -/
theorem mem_constBases_moveSection {b : Fin Ω.numItems × (A × Bool)} :
    b ∈ (Ω.moveSection i j m hi hj hm).constBases ↔
      ((Ω.moveItem i j m).symm b.1, b.2) ∈ Ω.constBases := by
  refine ⟨fun hb => ?_, fun hb => Finset.mem_map.2 ⟨_, hb, by simp⟩⟩
  obtain ⟨b, hb', rfl⟩ := Finset.mem_map.1 hb
  simpa using hb'

/-- The boundary connections of the moved equation are those of `Ω` with their boundaries
moved. -/
theorem mem_connections_moveSection
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} :
    c ∈ (Ω.moveSection i j m hi hj hm).connections ↔
      ((Ω.moveBoundary i j m).symm c.1, c.2.1, (Ω.moveBoundary i j m).symm c.2.2) ∈
        Ω.connections := by
  refine ⟨fun hc => ?_, fun hc => Finset.mem_image.2 ⟨_, hc, by simp⟩⟩
  obtain ⟨c, hc', rfl⟩ := Finset.mem_image.1 hc
  simpa using hc'

/-- The moved equation has the items of `Ω`, so the same words `h[a, b] ^ ±1`. -/
@[simp]
theorem segment_moveSection (a b : ℕ) (s : Bool) :
    (Ω.moveSection i j m hi hj hm).segment a b s = Ω.segment a b s := by
  cases s <;> simp only [segment_false, segment_true]

include hi hj hm in
/-- A segment `h[x, y]` inside a base moves to the segment of the same length starting at
`moveIdx i j m x`, with the items renamed. -/
private theorem segment_moveIdx_of_le (μ : Fin Ω.numBases) {x y : ℕ} (hx : (Ω.left μ : ℕ) ≤ x)
    (hxy : x ≤ y) (hy : y ≤ Ω.right μ) (s : Bool) :
    Ω.segment (moveIdx i j m x) (moveIdx i j m x + (y - x)) s =
      (Ω.segment x y s).map (Prod.map (Sum.map (Ω.moveItem i j m) id) id) := by
  have := hi.le_left_or_right_le μ
  have := hj.le_left_or_right_le μ
  have := hm.le_left_or_right_le μ
  simpa only [Nat.add_sub_cancel' hxy] using
    Ω.segment_moveIdx (i := i) (j := j) (m := m) (x := x) (d := y - x) (by lia) (by lia) (by lia) s

/-- The basic equation of a moved base is the basic equation of the base with the items
renamed. -/
@[simp]
theorem basicEquation_moveSection (μ : Fin Ω.numBases) :
    (Ω.moveSection i j m hi hj hm).basicEquation μ =
      ((Ω.basicEquation μ).1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        (Ω.basicEquation μ).2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) := by
  have hb (ν : Fin Ω.numBases) :=
    segment_moveIdx_of_le hi hj hm ν le_rfl (Fin.le_def.1 (Ω.left_lt_right ν).le) le_rfl
  refine Prod.ext ?_ ?_
  · simpa only [basicEquation_fst, segment_moveSection, coe_moveBoundary] using hb μ _
  · simpa only [basicEquation_snd, segment_moveSection, coe_moveBoundary] using hb (Ω.dual μ) _

/-- The coefficient equations only depend on the items, which the move keeps. -/
@[simp]
theorem coeffEquation_moveSection (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.moveSection i j m hi hj hm).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a moved connection is the boundary equation of the connection with
the items renamed. -/
theorem boundaryEquation_moveSection
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    (Ω.moveSection i j m hi hj hm).boundaryEquation
        (Ω.moveBoundary i j m c.1, c.2.1, Ω.moveBoundary i j m c.2.2) =
      ((Ω.boundaryEquation c).1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        (Ω.boundaryEquation c).2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc
  simp only [Fin.lt_def] at h₁ h₂ h₃ h₄
  refine Prod.ext ?_ ?_
  · simp only [boundaryEquation_fst, segment_moveSection, coe_moveBoundary]
    rw [moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂]
    exact segment_moveIdx_of_le hi hj hm μ le_rfl h₁.le h₂.le _
  · by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · rw [boundaryEquation_snd_of_sign_eq _ hs, boundaryEquation_snd_of_sign_eq _ hs]
      simp only [segment_moveSection, coe_moveBoundary]
      rw [moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄]
      exact segment_moveIdx_of_le hi hj hm (Ω.dual μ) le_rfl h₃.le h₄.le _
    · rw [boundaryEquation_snd_of_sign_ne _ hs, boundaryEquation_snd_of_sign_ne _ hs]
      simp only [segment_moveSection, coe_moveBoundary]
      have e := moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄
      have : moveIdx i j m (Ω.left (Ω.dual μ)) + (Ω.right (Ω.dual μ) - Ω.left (Ω.dual μ)) =
          moveIdx i j m q + (Ω.right (Ω.dual μ) - q) := by lia
      rw [this]
      exact segment_moveIdx_of_le hi hj hm (Ω.dual μ) h₃.le h₄.le le_rfl _

/-- The equations of the moved equation are the equations of `Ω` with the item `hₖ` renamed to
`h_{moveItem k}`. -/
theorem equations_moveSection : (Ω.moveSection i j m hi hj hm).equations =
      (fun e => (e.1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        e.2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id))) '' Ω.equations := by
  ext e
  simp only [mem_equations_iff, Set.mem_image]
  constructor
  · rintro (⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact ⟨_, Or.inl ⟨μ, rfl⟩, (basicEquation_moveSection hi hj hm μ).symm⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      exact ⟨_, Or.inr (Or.inl ⟨b', hb', rfl⟩), Prod.ext (by simp) (by simp)⟩
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      exact ⟨_, Or.inr (Or.inr ⟨c', hc', rfl⟩), (boundaryEquation_moveSection hi hj hm hc').symm⟩
  · rintro ⟨e, (⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩), rfl⟩
    · exact Or.inl ⟨μ, basicEquation_moveSection hi hj hm μ⟩
    · exact Or.inr (Or.inl ⟨_, Finset.mem_map_of_mem _ hb, Prod.ext (by simp) (by simp)⟩)
    · exact Or.inr (Or.inr ⟨_, Finset.mem_image_of_mem _ hc,
        boundaryEquation_moveSection hi hj hm hc⟩)

/-! ### Formal consistency -/

/-- Boundary connections through one moved base keep their order, or reverse it when the base
and its dual have opposite signs. -/
private theorem connections_monotone_or_antitone_moveSection (hΩ : Ω.IsFormallyConsistent)
    {c c' : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hc : c ∈ (Ω.moveSection i j m hi hj hm).connections)
    (hc' : c' ∈ (Ω.moveSection i j m hi hj hm).connections) (hμ : c.2.1 = c'.2.1)
    (hp : c.1 ≤ c'.1) :
    if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then c.2.2 ≤ c'.2.2 else c'.2.2 ≤ c.2.2 := by
  obtain ⟨⟨p, μ, q⟩, hc₀, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨⟨p', μ', q'⟩, hc₀', rfl⟩ := Finset.mem_image.1 hc'
  obtain rfl : μ = μ' := hμ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc₀
  obtain ⟨h₁', h₂', h₃', h₄'⟩ := Ω.bounds_of_mem_connections _ hc₀'
  simp only [Fin.lt_def] at h₁ h₂ h₃ h₄ h₁' h₂' h₃' h₄'
  simp only [Fin.le_def, coe_moveBoundary] at hp ⊢
  -- Inside a base the move is a shift, so it compares boundaries as before.
  rw [moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂,
    moveIdx_eq_of_le_of_lt hi hj hm μ h₁'.le h₂'] at hp
  have hpp : p ≤ p' := Fin.le_def.2 (by lia)
  have h := hΩ.connections_monotone_or_antitone _ hc₀ _ hc₀' rfl hpp
  rw [moveIdx_eq_of_le_of_lt hi hj hm _ h₃.le h₄, moveIdx_eq_of_le_of_lt hi hj hm _ h₃'.le h₄']
  simp only [Fin.le_def] at h
  split_ifs at h ⊢ <;> lia

/-- The two ends of a moved constant base are tied to adjacent boundaries through any moved base. -/
private theorem connections_adjacent_moveSection (hΩ : Ω.IsFormallyConsistent)
    {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ (Ω.moveSection i j m hi hj hm).constBases)
    {c c' : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hc : c ∈ (Ω.moveSection i j m hi hj hm).connections)
    (hc' : c' ∈ (Ω.moveSection i j m hi hj hm).connections) (hμ : c.2.1 = c'.2.1)
    (hp : c.1 = b.1.castSucc) (hp' : c'.1 = b.1.succ) :
    (c.2.2 : ℕ) + 1 = c'.2.2 ∨ (c'.2.2 : ℕ) + 1 = c.2.2 := by
  obtain ⟨⟨k, a⟩, hb₀, rfl⟩ := Finset.mem_map.1 hb
  obtain ⟨⟨p, μ, q⟩, hc₀, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨⟨p', μ', q'⟩, hc₀', rfl⟩ := Finset.mem_image.1 hc'
  obtain rfl : μ = μ' := hμ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc₀
  obtain ⟨h₁', h₂', h₃', h₄'⟩ := Ω.bounds_of_mem_connections _ hc₀'
  simp only [Fin.lt_def] at h₁ h₂ h₃ h₄ h₁' h₂' h₃' h₄'
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Function.Embedding.coe_prodMap,
    Prod.map_fst, Equiv.coe_toEmbedding, coe_moveItem, coe_moveBoundary] at hp hp'
  -- The ends of the constant base were tied to `p` and `p'`, adjacent inside `μ`.
  have e := moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂
  have e' := moveIdx_eq_of_le_of_lt hi hj hm μ h₁'.le h₂'
  have hpk : (p : ℕ) = k := moveIdx_injective hp
  have h := hΩ.connections_adjacent (k, a) hb₀ (p, μ, q) hc₀ (p', μ, q') hc₀' rfl (Fin.ext hpk)
    (Fin.ext (by simp only [Fin.val_succ]; lia))
  dsimp only at h ⊢
  rw [coe_moveBoundary, coe_moveBoundary, moveIdx_eq_of_le_of_lt hi hj hm _ h₃.le h₄,
    moveIdx_eq_of_le_of_lt hi hj hm _ h₃'.le h₄']
  lia

/-- Moving a section preserves formal consistency. -/
theorem IsFormallyConsistent.moveSection (hΩ : Ω.IsFormallyConsistent) :
    (Ω.moveSection i j m hi hj hm).IsFormallyConsistent := by
  refine ⟨fun μ hs => ?_, fun _ hc _ hc' hμ hp =>
      connections_monotone_or_antitone_moveSection hi hj hm hΩ hc hc' hμ hp, ?_, ?_,
    fun _ hb _ hc _ hc' hμ hp hp' =>
      connections_adjacent_moveSection hi hj hm hΩ hb hc hc' hμ hp hp'⟩
  · -- Disjoint bases stay disjoint.
    have h := hΩ.disjoint_of_sign_ne μ hs
    simp only [Fin.le_def, coe_moveBoundary] at h ⊢
    have hb (ν : Fin Ω.numBases) := Fin.lt_def.1 (Ω.left_lt_right ν)
    exact moveIdx_disjoint (hb μ) (hb (Ω.dual μ))
      ⟨hi.le_left_or_right_le μ, hi.le_left_or_right_le (Ω.dual μ)⟩
      ⟨hj.le_left_or_right_le μ, hj.le_left_or_right_le (Ω.dual μ)⟩
      ⟨hm.le_left_or_right_le μ, hm.le_left_or_right_le (Ω.dual μ)⟩ h
  · -- A base and its dual start together exactly when they did before.
    simp only [Finset.mem_image]
    rintro _ ⟨⟨p, μ, q⟩, hc, rfl⟩ hl
    obtain rfl : p = q := hΩ.eq_of_left_eq _ hc ((Ω.moveBoundary i j m).injective hl)
    rfl
  · -- Constant bases on one item come from constant bases on one item.
    simp only [Finset.mem_map]
    rintro _ ⟨⟨k, a⟩, hb, rfl⟩ _ ⟨⟨k', a'⟩, hb', rfl⟩ hk
    simpa using hΩ.label_eq (k, a) hb (k', a') hb' (by simpa using hk)

/-! ### Bases, items and boundaries of the moved equation -/

include hi hj hm in
/-- A place lies in a moved base exactly when the place it comes from lies in the base. -/
private theorem moveIdx_mem_base_iff (μ : Fin Ω.numBases) {p : ℕ} :
    moveIdx i j m (Ω.left μ) ≤ p ∧ p < moveIdx i j m (Ω.left μ) + (Ω.right μ - Ω.left μ) ↔
      Ω.left μ ≤ moveIdx i (i + (m - j)) m p ∧ moveIdx i (i + (m - j)) m p < Ω.right μ := by
  have := hi.le_left_or_right_le μ
  have := hj.le_left_or_right_le μ
  have := hm.le_left_or_right_le μ
  have := Ω.left_lt_right μ
  simp only [Fin.le_def, Fin.lt_def] at *
  unfold moveIdx
  split_ifs <;> lia

include hi hj hm in
/-- A place lies strictly inside a moved base exactly when the place it comes from lies strictly
inside the base. -/
private theorem moveIdx_crosses_iff (μ : Fin Ω.numBases) {p : ℕ} :
    moveIdx i j m (Ω.left μ) < p ∧ p < moveIdx i j m (Ω.left μ) + (Ω.right μ - Ω.left μ) ↔
      Ω.left μ < moveIdx i (i + (m - j)) m p ∧ moveIdx i (i + (m - j)) m p < Ω.right μ := by
  have := hi.le_left_or_right_le μ
  have := hj.le_left_or_right_le μ
  have := hm.le_left_or_right_le μ
  have := Ω.left_lt_right μ
  simp only [Fin.le_def, Fin.lt_def] at *
  unfold moveIdx
  split_ifs <;> lia

/-- The items of a moved base are the moved items of the base. -/
@[simp]
theorem baseItems_moveSection (μ : Fin Ω.numBases) :
    (Ω.moveSection i j m hi hj hm).baseItems μ =
      (Ω.baseItems μ).map (Ω.moveItem i j m).toEmbedding := by
  ext k
  rw [Finset.mem_map_equiv, mem_baseItems, mem_baseItems, coe_moveItem_symm]
  exact moveIdx_mem_base_iff hi hj hm μ

/-- An item of the moved equation is constant exactly when the item it comes from is. -/
@[simp]
theorem isConstantItem_moveSection_iff {k : Fin Ω.numItems} :
    (Ω.moveSection i j m hi hj hm).IsConstantItem k ↔
      Ω.IsConstantItem ((Ω.moveItem i j m).symm k) := by
  rw [isConstantItem_iff, isConstantItem_iff]
  refine ⟨fun ⟨b, hb, hbk⟩ => ⟨_, (mem_constBases_moveSection hi hj hm).1 hb, by rw [hbk]⟩,
    fun ⟨b, hb, hbk⟩ => ⟨(Ω.moveItem i j m b.1, b.2),
      (mem_constBases_moveSection hi hj hm).2 (by simpa using hb), by simp [hbk]⟩⟩

/-- An item of the moved equation is free exactly when the item it comes from is. -/
@[simp]
theorem isFreeItem_moveSection_iff {k : Fin Ω.numItems} :
    (Ω.moveSection i j m hi hj hm).IsFreeItem k ↔ Ω.IsFreeItem ((Ω.moveItem i j m).symm k) := by
  simp only [isFreeItem_iff, baseItems_moveSection, Finset.mem_map_equiv,
    isConstantItem_moveSection_iff]

/-- The degree of an item of the moved equation is the degree of the item it comes from. -/
@[simp]
theorem degree_moveSection (k : Fin Ω.numItems) :
    (Ω.moveSection i j m hi hj hm).degree k = Ω.degree ((Ω.moveItem i j m).symm k) := by
  simp only [degree_def, baseItems_moveSection, Finset.mem_map_equiv]
  congr 1
  rw [Finset.filter_map, Finset.card_map]
  exact congrArg _ (Finset.filter_congr fun b _ => by simp [Equiv.eq_symm_apply])

/-- A boundary of the moved equation crosses a moved base exactly when the boundary it comes from
crosses the base. -/
@[simp]
theorem crosses_moveSection_iff {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} :
    (Ω.moveSection i j m hi hj hm).Crosses p μ ↔ Ω.Crosses ((Ω.moveBoundary i j m).symm p) μ := by
  rw [crosses_iff, crosses_iff, Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def,
    coe_moveBoundary_symm]
  exact moveIdx_crosses_iff hi hj hm μ

/-- A boundary of the moved equation is open exactly when the boundary it comes from is. -/
@[simp]
theorem isOpenBoundary_moveSection_iff {p : Fin (Ω.numItems + 1)} :
    (Ω.moveSection i j m hi hj hm).IsOpenBoundary p ↔
      Ω.IsOpenBoundary ((Ω.moveBoundary i j m).symm p) := by
  simp only [isOpenBoundary_iff, crosses_moveSection_iff]

/-- A boundary of the moved equation is closed exactly when the boundary it comes from is. -/
@[simp]
theorem isClosedBoundary_moveSection_iff {p : Fin (Ω.numItems + 1)} :
    (Ω.moveSection i j m hi hj hm).IsClosedBoundary p ↔
      Ω.IsClosedBoundary ((Ω.moveBoundary i j m).symm p) := by
  rw [← not_isOpenBoundary, ← not_isOpenBoundary, isOpenBoundary_moveSection_iff]

include hi hj hm in
/-- The boundaries `i`, `m` and, when `i ≤ j`, `i + (m - j)` of the moved equation are closed. -/
private theorem isClosedBoundary_moveSection {p : Fin (Ω.numItems + 1)}
    (hp : (p : ℕ) = i ∨ (p : ℕ) = m ∨ i ≤ j ∧ (p : ℕ) = i + (m - j)) :
    (Ω.moveSection i j m hi hj hm).IsClosedBoundary p := by
  refine (isClosedBoundary_iff _).2 fun μ hμ => ?_
  have := hi.le_left_or_right_le μ
  have := hj.le_left_or_right_le μ
  have := hm.le_left_or_right_le μ
  have := Ω.left_lt_right μ
  rw [crosses_iff, Fin.lt_def, Fin.lt_def, coe_moveBoundary] at hμ
  simp only [Fin.le_def, Fin.lt_def] at *
  unfold moveIdx at hμ
  split_ifs at hμ <;> lia

/-- The left end `i` of the moved blocks is a closed boundary of the moved equation. -/
theorem isClosedBoundary_moveSection_left : (Ω.moveSection i j m hi hj hm).IsClosedBoundary i :=
  isClosedBoundary_moveSection hi hj hm (Or.inl rfl)

/-- The right end `m` of the moved blocks is a closed boundary of the moved equation. -/
theorem isClosedBoundary_moveSection_right : (Ω.moveSection i j m hi hj hm).IsClosedBoundary m :=
  isClosedBoundary_moveSection hi hj hm (Or.inr (Or.inl rfl))

/-- When `i ≤ j`, the boundary `i + (m - j)` between the two moved blocks `[i, i + (m - j)]` (the
former `[j, m]`) and `[i + (m - j), m]` (the former `[i, j]`) is closed. -/
theorem isClosedBoundary_moveSection_middle (hij : i ≤ j) {p : Fin (Ω.numItems + 1)}
    (hp : (p : ℕ) = i + (m - j)) : (Ω.moveSection i j m hi hj hm).IsClosedBoundary p :=
  isClosedBoundary_moveSection hi hj hm (Or.inr (Or.inr ⟨hij, hp⟩))

/-! ### Moving back -/

/-- When `i ≤ j ≤ m` fails, or one of the two blocks is empty, nothing moves. -/
theorem moveSection_eq_self (h : j ≤ i ∨ m ≤ j) : Ω.moveSection i j m hi hj hm = Ω := by
  have e : ∀ k, moveIdx i j m k = k := congrFun (moveIdx_eq_id (h.imp Fin.le_def.1 Fin.le_def.1))
  have e₁ := Ω.moveItem_eq_one h
  have e₂ := Ω.moveBoundary_eq_one h
  obtain ⟨n, b, left, right, hlr, sign, dual, hd, cb, conn, hb, hc⟩ := Ω
  unfold moveSection
  dsimp only
  congr 1
  · exact funext fun μ => by rw [e₂]; rfl
  · exact funext fun μ => Fin.ext <| by
      have := hlr μ
      rw [Fin.lt_def] at this
      simp only [e]
      lia
  · convert Finset.map_refl
    ext ⟨k, a⟩ : 1
    simp [e₁]
  · rw [e₂]
    simp

/-- Moving the block `[i, i + (m - j)]` of the moved equation back behind `[i + (m - j), m]`
restores `Ω`. -/
theorem moveSection_moveSection {j' : Fin (Ω.numItems + 1)} (h : (j' : ℕ) = i + (m - j))
    (hi' : (Ω.moveSection i j m hi hj hm).IsClosedBoundary i)
    (hj' : (Ω.moveSection i j m hi hj hm).IsClosedBoundary j')
    (hm' : (Ω.moveSection i j m hi hj hm).IsClosedBoundary m) :
    (Ω.moveSection i j m hi hj hm).moveSection i j' m hi' hj' hm' = Ω := by
  obtain ⟨n, b, left, right, hlr, sign, dual, hd, cb, conn, hb, hc⟩ := Ω
  unfold moveSection
  dsimp only
  congr 1
  · exact funext fun μ => Fin.ext <| by simp [h]
  · exact funext fun μ => Fin.ext <| by
      have := hlr μ
      rw [Fin.lt_def] at this
      simp only [coe_moveBoundary, h, moveIdx_moveIdx]
      lia
  · rw [Finset.map_map]
    convert Finset.map_refl
    ext ⟨k, a⟩ : 1
    simp [h, moveItem]
  · rw [Finset.image_image]
    refine (Finset.image_congr fun c _ => ?_).trans Finset.image_id'
    obtain ⟨p, μ, q⟩ := c
    simp [h, moveBoundary]

/-- The moved equation is formally consistent exactly when `Ω` is. -/
@[simp]
theorem isFormallyConsistent_moveSection_iff :
    (Ω.moveSection i j m hi hj hm).IsFormallyConsistent ↔ Ω.IsFormallyConsistent := by
  refine ⟨fun hΩ => ?_, IsFormallyConsistent.moveSection hi hj hm⟩
  rcases le_or_gt i j with hij | hji
  · have hj' : (i : ℕ) + (m - j) < Ω.numItems + 1 := by
      have := Fin.le_def.1 hij
      have := m.is_lt
      lia
    rw [← moveSection_moveSection hi hj hm (j' := ⟨_, hj'⟩) rfl
      (isClosedBoundary_moveSection_left hi hj hm)
      (isClosedBoundary_moveSection_middle hi hj hm hij rfl)
      (isClosedBoundary_moveSection_right hi hj hm)]
    exact hΩ.moveSection _ _ _
  · rwa [moveSection_eq_self hi hj hm (Or.inl hji.le)] at hΩ

/-! ### Group solutions and coordinate groups -/

/-- **D2 on group solutions.** A tuple is a point of `Ω*` exactly when the tuple with the items
permuted is a point of the system of `Ω` with a section moved. -/
theorem comp_moveItem_mem_V_iff {H : Type*} [Group H] (ι : FreeGroup A →* H)
    {v : Fin Ω.numItems → H} : v ∘ Ω.moveItem i j m ∈ V ι Ω.toSystem ↔
      v ∈ V ι (Ω.moveSection i j m hi hj hm).toSystem := by
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff, equations_moveSection hi hj hm,
    Set.forall_mem_image]
  -- Evaluating a word with the items renamed at `v` is evaluating the word at `v ∘ moveItem`.
  have h (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
          (FreeGroup.mk (w.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id))) =
        FreeGroup.lift (Sum.elim (v ∘ Ω.moveItem i j m) (ι ∘ FreeGroup.of)) (FreeGroup.mk w) := by
    simp [FreeGroup.lift_mk, List.map_map, Function.comp_def, Sum.elim_map]
  exact forall₂_congr fun e _ => by rw [h, h]

/-- **D2 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
permutation of the items, where `Ω′` is `Ω` with a section moved. -/
def moveSectionHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.moveSection i j m hi hj hm).toSystem) :=
  CoordGroup.homOfMapsToWordMap _ _ _ (fun k => inr (FreeGroup.of (Ω.moveItem i j m k)))
    ((CoordGroup.mapsToWordMap_iff _ _ _ _).2 fun v hv => by
      rw [show wordMap _ _ v = v ∘ Ω.moveItem i j m from funext fun k => by simp]
      exact (comp_moveItem_mem_V_iff hi hj hm _).2 hv)

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` renames the items of a word along the permutation of
the items. -/
-- Not `@[simp]`: the reducible `moveSection` in the codomain keeps `simp` from indexing this lemma
-- uninstantiated, so it is used through `rw`.
theorem moveSectionHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    moveSectionHom hi hj hm (w : Ω.coordGroup) =
      (eval (inl : FreeGroup A →* GX (FreeGroup A) (Fin Ω.numItems))
        (fun k => inr (FreeGroup.of (Ω.moveItem i j m k))) w :
          (Ω.moveSection i j m hi hj hm).coordGroup) :=
  CoordGroup.homOfMapsToWordMap_mk _ _ _ _ _ w

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` sends the item `hₖ` to `h_{moveItem k}`. -/
theorem moveSectionHom_inr_of (k : Fin Ω.numItems) :
    moveSectionHom hi hj hm
        ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup) =
      ((inr (FreeGroup.of (Ω.moveItem i j m k)) : GX (FreeGroup A) (Fin Ω.numItems)) :
        (Ω.moveSection i j m hi hj hm).coordGroup) := by
  rw [moveSectionHom_mk, eval_inr_of]

/-- **D2 on coordinate groups.** The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` is an isomorphism. -/
theorem moveSectionHom_bijective : Function.Bijective (moveSectionHom hi hj hm) := by
  -- The inverse is induced by the inverse permutation of the items.
  let ψ : GHom (CoordGroup.coeff (.id (FreeGroup A)) (Ω.moveSection i j m hi hj hm).toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem) :=
    CoordGroup.homOfMapsToWordMap _ _ _
      (fun k => inr (FreeGroup.of ((Ω.moveItem i j m).symm k)))
      ((CoordGroup.mapsToWordMap_iff _ _ _ _).2 fun v hv => by
        rw [show wordMap _ _ v = v ∘ (Ω.moveItem i j m).symm from funext fun k => by simp,
          ← comp_moveItem_mem_V_iff hi hj hm]
        simpa [Function.comp_assoc] using hv)
  have h₁ : ψ.comp (moveSectionHom hi hj hm) = GHom.id _ :=
    CoordGroup.gHom_ext fun k => by
      rw [GHom.coe_comp, Function.comp_apply, moveSectionHom_inr_of]
      simp [ψ]
  have h₂ : (moveSectionHom hi hj hm).comp ψ = GHom.id _ :=
    CoordGroup.gHom_ext fun k => by
      rw [GHom.coe_comp, Function.comp_apply]
      simp only [ψ, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]
      rw [moveSectionHom_inr_of]
      simp
  exact Function.bijective_iff_has_inverse.2 ⟨ψ, fun x => by simpa using DFunLike.congr_fun h₁ x,
    fun x => by simpa using DFunLike.congr_fun h₂ x⟩

/-! ### Solutions -/

/-- A property of the two substituted sides of every equation of the moved equation is the
property of `Ω` for the words with the items renamed. -/
private theorem forall_mem_equations_moveSection (W : Fin Ω.numItems → List (A × Bool))
    (P : List (A × Bool) → List (A × Bool) → Prop) :
    (∀ e ∈ (Ω.moveSection i j m hi hj hm).equations,
      P (substituteVars W e.1) (substituteVars W e.2)) ↔
      ∀ e ∈ Ω.equations, P (substituteVars (W ∘ Ω.moveItem i j m) e.1)
        (substituteVars (W ∘ Ω.moveItem i j m) e.2) := by
  rw [equations_moveSection hi hj hm, Set.forall_mem_image]
  simp only [FreeGroup.substituteVars_map]

/-- **D2 on solutions.** A generalised equation and the equation with a section moved have the
same solutions, with the words of the items permuted. -/
def solutionEquivMoveSection : Ω.Solution ≃ (Ω.moveSection i j m hi hj hm).Solution where
  toFun U :=
    { word := U.word ∘ (Ω.moveItem i j m).symm
      isReduced_word k := U.isReduced_word _
      word_ne_nil k := U.word_ne_nil _
      isReduced_subst := (forall_mem_equations_moveSection hi hj hm _
        fun u w => FreeGroup.IsReduced u ∧ FreeGroup.IsReduced w).2 <| by
          simpa [Function.comp_assoc] using U.isReduced_subst
      subst_eq := (forall_mem_equations_moveSection hi hj hm _ (· = ·)).2 <| by
        simpa [Function.comp_assoc] using U.subst_eq }
  invFun U :=
    { word := U.word ∘ Ω.moveItem i j m
      isReduced_word k := U.isReduced_word _
      word_ne_nil k := U.word_ne_nil _
      isReduced_subst := (forall_mem_equations_moveSection hi hj hm U.word
        fun u w => FreeGroup.IsReduced u ∧ FreeGroup.IsReduced w).1 U.isReduced_subst
      subst_eq := (forall_mem_equations_moveSection hi hj hm U.word (· = ·)).1 U.subst_eq }
  left_inv U := Solution.ext (funext fun k => by simp)
  right_inv U := Solution.ext (funext fun k => by simp)

/-- The solution of the moved equation corresponding to `U` assigns to the item `moveItem k` the
word of `U` at `k`. -/
@[simp]
theorem solutionEquivMoveSection_apply_word (U : Ω.Solution) :
    (solutionEquivMoveSection hi hj hm U).word = U.word ∘ (Ω.moveItem i j m).symm :=
  (rfl)

/-- The solution of `Ω` corresponding to a solution `U` of the moved equation assigns to the item
`k` the word of `U` at `moveItem k`. -/
@[simp]
theorem solutionEquivMoveSection_symm_apply_word (U : (Ω.moveSection i j m hi hj hm).Solution) :
    ((solutionEquivMoveSection hi hj hm).symm U).word = U.word ∘ Ω.moveItem i j m :=
  (rfl)

/-- The point of the solution of the moved equation corresponding to `U` is the point of `U` with
the items permuted. -/
@[simp]
theorem solutionEquivMoveSection_apply_point (U : Ω.Solution) :
    (solutionEquivMoveSection hi hj hm U).point = U.point ∘ (Ω.moveItem i j m).symm := by
  ext
  simp

/-- The point of the solution of `Ω` corresponding to a solution `U` of the moved equation is the
point of `U` with the items permuted. -/
@[simp]
theorem solutionEquivMoveSection_symm_apply_point
    (U : (Ω.moveSection i j m hi hj hm).Solution) :
    ((solutionEquivMoveSection hi hj hm).symm U).point = U.point ∘ Ω.moveItem i j m := by
  ext
  simp

/-- A solution of `Ω` is the composite of the corresponding solution of `Ω′` with
`F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem toHom_comp_moveSectionHom (U : Ω.Solution) :
    (solutionEquivMoveSection hi hj hm U).toHom.comp (moveSectionHom hi hj hm) = U.toHom :=
  CoordGroup.gHom_ext fun k => by
    rw [GHom.coe_comp, Function.comp_apply, moveSectionHom_inr_of]
    simp

/-- **D2 transfers solutions uniquely.** The solution of the moved equation through which a
solution `U` of `Ω` factors is the one corresponding to `U`. -/
theorem toHom_comp_moveSectionHom_eq_iff (U : Ω.Solution)
    (U' : (Ω.moveSection i j m hi hj hm).Solution) :
    U'.toHom.comp (moveSectionHom hi hj hm) = U.toHom ↔
      U' = solutionEquivMoveSection hi hj hm U := by
  refine ⟨fun h => Solution.point_injective (funext fun k => ?_), ?_⟩
  · have h' := DFunLike.congr_fun h
      ((inr (FreeGroup.of ((Ω.moveItem i j m).symm k)) : GX (FreeGroup A) _) : Ω.coordGroup)
    rw [GHom.coe_comp, Function.comp_apply, moveSectionHom_inr_of, Solution.toHom_inr_of,
      Solution.toHom_inr_of] at h'
    simpa using h'
  · rintro rfl
    exact toHom_comp_moveSectionHom hi hj hm U

/-- The homomorphism of the solution of `Ω` corresponding to a solution `U` of the moved equation
is that of `U` composed with `F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem solutionEquivMoveSection_symm_apply_toHom
    (U : (Ω.moveSection i j m hi hj hm).Solution) :
    ((solutionEquivMoveSection hi hj hm).symm U).toHom =
      U.toHom.comp (moveSectionHom hi hj hm) := by
  conv_rhs => rw [← (solutionEquivMoveSection hi hj hm).apply_symm_apply U]
  exact (toHom_comp_moveSectionHom hi hj hm _).symm

/-! ### Example -/

/-- The generalised equation `h₀ = h₁`, `h₂ = a` over `F(a)`. -/
private abbrev exampleEq : GenEq Unit where
  numItems := 3
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := {(2, ((), true))}
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The boundary `2` of `h₀ = h₁`, `h₂ = a` is closed. -/
private theorem exampleEq_isClosedBoundary_two : exampleEq.IsClosedBoundary 2 :=
  exampleEq.isClosedBoundary_iff.2 <| Fin.forall_fin_two.2
    ⟨by rw [crosses_iff]; decide, by rw [crosses_iff]; decide⟩

/-- Moving the section `[0, 2]` of `h₀ = h₁`, `h₂ = a`, which consists of the two closed sections
`[0, 1]` and `[1, 2]`, behind the closed section `[2, 3]` gives `h₁ = h₂`, `h₀ = a`: the bases move
to `[1, 2]`, `[2, 3]` and the constant base to `h₀`. -/
example : (exampleEq.moveSection 0 2 (Fin.last 3) exampleEq.isClosedBoundary_zero
      exampleEq_isClosedBoundary_two exampleEq.isClosedBoundary_last).left = ![1, 2] ∧
    (exampleEq.moveSection 0 2 (Fin.last 3) exampleEq.isClosedBoundary_zero
      exampleEq_isClosedBoundary_two exampleEq.isClosedBoundary_last).right = ![2, 3] ∧
    (exampleEq.moveSection 0 2 (Fin.last 3) exampleEq.isClosedBoundary_zero
      exampleEq_isClosedBoundary_two exampleEq.isClosedBoundary_last).constBases =
      {(0, ((), true))} := by
  decide

end GenEq

end TauCeti
