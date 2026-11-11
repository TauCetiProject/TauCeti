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
it to the right. When `i ≤ j ≤ m` fails, nothing moves.

The result has the same number of items, its equations are the equations of `Ω` with the items
renamed, the renaming induces an `F(A)`-isomorphism of coordinate groups
(`TauCeti.GenEq.moveSectionHom`), and the solutions correspond, with the words permuted
(`TauCeti.GenEq.solutionEquivMoveSection`).

## Main definitions

* `TauCeti.GenEq.moveItem`: the permutation of the items moving the block `[i, j]` behind the
  block `[j, m]`.
* `TauCeti.GenEq.moveSection`: the generalised equation with the block `[i, j]` moved behind the
  block `[j, m]`.
* `TauCeti.GenEq.moveSectionHom`: the `F(A)`-homomorphism of coordinate groups induced by the
  permutation of the items.
* `TauCeti.GenEq.solutionEquivMoveSection`: the bijection between the solutions.

## Main results

* `TauCeti.GenEq.equations_moveSection`: the equations of the moved equation are the equations
  of `Ω` with the items renamed.
* `TauCeti.GenEq.IsFormallyConsistent.moveSection`: moving a section preserves formal
  consistency.
* `TauCeti.GenEq.comp_moveItem_mem_V_iff`: the group solutions correspond.
* `TauCeti.GenEq.moveSectionHom_bijective`: the coordinate groups are isomorphic.
* `TauCeti.GenEq.toHom_comp_moveSectionHom`: a solution factors through the isomorphism.

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

/-! ### Moving a block of items -/

/-- The new place of the item (or of the left end-point of a base) `k` when the block `[i, j]` is
moved behind the block `[j, m]`: the places before `i` and from `m` on are fixed, those of
`[i, j]` move up by `m - j` and those of `[j, m]` move down by `j - i`. When `i ≤ j ≤ m` fails,
every place is fixed. -/
def moveIdx (i j m k : ℕ) : ℕ :=
  if k < i then k else if k < j then k + (m - j) else if k < m then k - (j - i) else k

theorem moveIdx_def (i j m k : ℕ) : moveIdx i j m k =
    if k < i then k else if k < j then k + (m - j) else if k < m then k - (j - i) else k :=
  (rfl)

/-- Moving blocks inside `[0, n]` keeps the places below `n`. -/
theorem moveIdx_lt {i j m n k : ℕ} (hm : m ≤ n) (hk : k < n) : moveIdx i j m k < n := by
  unfold moveIdx
  split_ifs <;> lia

/-- Moving the block `[i, j]` behind `[j, m]` and then the block `[i, i + (m - j)]` behind
`[i + (m - j), m]` restores every place. -/
theorem moveIdx_moveIdx {i j m k : ℕ} : moveIdx i (i + (m - j)) m (moveIdx i j m k) = k := by
  unfold moveIdx
  split_ifs <;> lia

/-- `moveIdx i j m` is injective. -/
private theorem moveIdx_injective {i j m : ℕ} : Function.Injective (moveIdx i j m) :=
  Function.LeftInverse.injective fun _ => moveIdx_moveIdx

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
private theorem moveIdx_add {i j m a d t : ℕ} (hi : i ≤ a ∨ a + d ≤ i) (hj : j ≤ a ∨ a + d ≤ j)
    (hm : m ≤ a ∨ a + d ≤ m) (ht : t < d) : moveIdx i j m (a + t) = moveIdx i j m a + t := by
  unfold moveIdx
  split_ifs <;> lia

/-- The permutation of the items moving the block `[i, j]` behind the block `[j, m]`. -/
def moveItem (i j m : Fin (Ω.numItems + 1)) : Equiv.Perm (Fin Ω.numItems) where
  toFun k := ⟨moveIdx i j m k, moveIdx_lt m.is_le k.is_lt⟩
  invFun k := ⟨moveIdx i (i + (m - j)) m k, moveIdx_lt m.is_le k.is_lt⟩
  left_inv _ := Fin.ext moveIdx_moveIdx
  right_inv _ := Fin.ext <| by
    dsimp only
    unfold moveIdx
    split_ifs <;> lia

/-- The permutation moving the block `[i, j]` behind `[j, m]` sends the item `k` to
`moveIdx i j m k`. -/
@[simp]
theorem coe_moveItem (i j m : Fin (Ω.numItems + 1)) (k : Fin Ω.numItems) :
    (Ω.moveItem i j m k : ℕ) = moveIdx i j m k :=
  (rfl)

/-- The inverse of the permutation moving the block `[i, j]` behind `[j, m]` moves the block
`[i, i + (m - j)]` behind `[i + (m - j), m]`. -/
@[simp]
theorem coe_moveItem_symm (i j m : Fin (Ω.numItems + 1)) (k : Fin Ω.numItems) :
    ((Ω.moveItem i j m).symm k : ℕ) = moveIdx i (i + (m - j)) m k :=
  (rfl)

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
inside a base goes to `moveIdx i j m p`. When `i ≤ j ≤ m` fails, nothing moves. -/
abbrev moveSection (i j m : Fin (Ω.numItems + 1)) (hi : Ω.IsClosedBoundary i)
    (hj : Ω.IsClosedBoundary j) (hm : Ω.IsClosedBoundary m) : GenEq A where
  numItems := Ω.numItems
  numBases := Ω.numBases
  left μ := ⟨moveIdx i j m (Ω.left μ), moveIdx_lt m.is_lt.le (Ω.left μ).is_lt⟩
  right μ := ⟨moveIdx i j m (Ω.left μ) + (Ω.right μ - Ω.left μ), by
    -- The last item of the base moves to a place below `ρ`.
    have h₁ := Fin.lt_def.1 (Ω.left_lt_right μ)
    have := moveIdx_eq_of_le_of_lt hi hj hm μ (p := Ω.right μ - 1) (by lia) (by lia)
    have := moveIdx_lt (i := i) (j := j) (k := Ω.right μ - 1) m.is_le (by lia)
    lia⟩
  left_lt_right μ := by
    have := Ω.left_lt_right μ
    rw [Fin.lt_def] at this ⊢
    lia
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.map
    ((Ω.moveItem i j m).toEmbedding.prodMap (Function.Embedding.refl _))
  connections := Ω.connections.image fun c =>
    (⟨moveIdx i j m c.1, moveIdx_lt m.is_lt.le c.1.is_lt⟩, c.2.1,
      ⟨moveIdx i j m c.2.2, moveIdx_lt m.is_lt.le c.2.2.is_lt⟩)
  bounds_of_mem_connections := by
    simp only [Finset.mem_image]
    rintro _ ⟨⟨p, μ, q⟩, hc, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc
    simp only [Fin.lt_def] at h₁ h₂ h₃ h₄ ⊢
    -- A boundary strictly inside a base moves with the base.
    have := moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂
    have := moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄
    lia
  dual_mem_connections := by
    simp only [Finset.mem_image]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, Ω.dual_mem_connections c hc, rfl⟩

/-! ### The equations of the moved equation -/

/-- A segment `h[x, y]` that none of the boundaries `i`, `j`, `m` cuts moves to the segment of the
same length starting at `moveIdx i j m x`, with the items renamed. -/
private theorem segment_moveIdx {i j m : Fin (Ω.numItems + 1)} {x y : ℕ}
    (hi : (i : ℕ) ≤ x ∨ y ≤ i) (hj : (j : ℕ) ≤ x ∨ y ≤ j) (hm : (m : ℕ) ≤ x ∨ y ≤ m)
    (hxy : x ≤ y) (hy : y ≤ Ω.numItems) (s : Bool) :
    Ω.segment (moveIdx i j m x) (moveIdx i j m x + (y - x)) s =
      (Ω.segment x y s).map (Prod.map (Sum.map (Ω.moveItem i j m) id) id) := by
  have hadd {t : ℕ} (ht : t < y - x) : moveIdx i j m (x + t) = moveIdx i j m x + t :=
    moveIdx_add (d := y - x) (by lia) (by lia) (by lia) ht
  -- The moved segment ends at or before the last boundary.
  have hle : moveIdx i j m x + (y - x) ≤ Ω.numItems := by
    rcases Nat.eq_zero_or_pos (y - x) with h | h
    · have := moveIdx_lt (i := i) (j := j) (k := x) m.is_lt.le (Nat.lt_succ_of_le (by lia))
      lia
    · have := moveIdx_lt (i := i) (j := j) (k := x + (y - x - 1)) m.is_le (by lia)
      rw [hadd (by lia)] at this
      lia
  have key : ((List.finRange Ω.numItems).take (moveIdx i j m x + (y - x))).drop
      (moveIdx i j m x) = (((List.finRange Ω.numItems).take y).drop x).map (Ω.moveItem i j m) := by
    refine List.ext_getElem ?_ fun t h₁ h₂ => Fin.ext ?_
    · simp only [List.length_drop, List.length_take, List.length_finRange, List.length_map]
      lia
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

/-- The moved equation has the items of `Ω`, so the same words `h[a, b] ^ ±1`. -/
private theorem segment_moveSection (a b : ℕ) (s : Bool) :
    (Ω.moveSection i j m hi hj hm).segment a b s = Ω.segment a b s := by
  cases s <;> simp [segment_false, segment_true]

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
  exact Ω.segment_moveIdx (by lia) (by lia) (by lia) hxy (by lia) s

/-- The basic equation of a moved base is the basic equation of the base with the items
renamed. -/
private theorem basicEquation_moveSection (μ : Fin Ω.numBases) :
    (Ω.moveSection i j m hi hj hm).basicEquation μ =
      ((Ω.basicEquation μ).1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        (Ω.basicEquation μ).2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) := by
  have hb (ν : Fin Ω.numBases) :=
    segment_moveIdx_of_le hi hj hm ν le_rfl (Fin.le_def.1 (Ω.left_lt_right ν).le) le_rfl
  refine Prod.ext ?_ ?_
  · simpa only [basicEquation_fst, segment_moveSection] using hb μ _
  · simpa only [basicEquation_snd, segment_moveSection] using hb (Ω.dual μ) _

/-- The coefficient equation of a moved constant base is the coefficient equation of the constant
base with the item renamed. -/
private theorem coeffEquation_moveSection (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.moveSection i j m hi hj hm).coeffEquation (Ω.moveItem i j m b.1, b.2) =
      ((Ω.coeffEquation b).1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        (Ω.coeffEquation b).2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) := by
  refine Prod.ext ?_ ?_ <;> simp

/-- The boundary equation of a moved connection is the boundary equation of the connection with
the items renamed. -/
private theorem boundaryEquation_moveSection
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    (Ω.moveSection i j m hi hj hm).boundaryEquation
        (⟨moveIdx i j m c.1, moveIdx_lt m.is_lt.le c.1.is_lt⟩, c.2.1,
          ⟨moveIdx i j m c.2.2, moveIdx_lt m.is_lt.le c.2.2.is_lt⟩) =
      ((Ω.boundaryEquation c).1.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id),
        (Ω.boundaryEquation c).2.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections _ hc
  simp only [Fin.lt_def] at h₁ h₂ h₃ h₄
  refine Prod.ext ?_ ?_
  · simp only [boundaryEquation_fst, segment_moveSection]
    rw [moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂]
    exact segment_moveIdx_of_le hi hj hm μ le_rfl h₁.le h₂.le _
  · by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · rw [boundaryEquation_snd_of_sign_eq _ hs, boundaryEquation_snd_of_sign_eq _ hs]
      dsimp only
      rw [segment_moveSection, moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄]
      exact segment_moveIdx_of_le hi hj hm (Ω.dual μ) le_rfl h₃.le h₄.le _
    · rw [boundaryEquation_snd_of_sign_ne _ hs, boundaryEquation_snd_of_sign_ne _ hs]
      dsimp only
      have e := moveIdx_eq_of_le_of_lt hi hj hm (Ω.dual μ) h₃.le h₄
      have : moveIdx i j m (Ω.left (Ω.dual μ)) + (Ω.right (Ω.dual μ) - Ω.left (Ω.dual μ)) =
          moveIdx i j m q + (Ω.right (Ω.dual μ) - q) := by lia
      rw [segment_moveSection, this]
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
      exact ⟨_, Or.inr (Or.inl ⟨b', hb', rfl⟩), (coeffEquation_moveSection hi hj hm b').symm⟩
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      exact ⟨_, Or.inr (Or.inr ⟨c', hc', rfl⟩), (boundaryEquation_moveSection hi hj hm hc').symm⟩
  · rintro ⟨e, (⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩), rfl⟩
    · exact Or.inl ⟨μ, basicEquation_moveSection hi hj hm μ⟩
    · exact Or.inr (Or.inl ⟨_, Finset.mem_map_of_mem _ hb, coeffEquation_moveSection hi hj hm b⟩)
    · exact Or.inr (Or.inr ⟨_, Finset.mem_image_of_mem _ hc,
        boundaryEquation_moveSection hi hj hm hc⟩)

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
  simp only [Fin.le_def] at hp ⊢
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
    Prod.map_fst, Equiv.coe_toEmbedding, coe_moveItem] at hp hp'
  -- The ends of the constant base were tied to `p` and `p'`, adjacent inside `μ`.
  have e := moveIdx_eq_of_le_of_lt hi hj hm μ h₁.le h₂
  have e' := moveIdx_eq_of_le_of_lt hi hj hm μ h₁'.le h₂'
  have hpk : (p : ℕ) = k := moveIdx_injective hp
  have h := hΩ.connections_adjacent (k, a) hb₀ (p, μ, q) hc₀ (p', μ, q') hc₀' rfl (Fin.ext hpk)
    (Fin.ext (by simp only [Fin.val_succ]; lia))
  dsimp only at h ⊢
  rw [moveIdx_eq_of_le_of_lt hi hj hm _ h₃.le h₄, moveIdx_eq_of_le_of_lt hi hj hm _ h₃'.le h₄']
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
    simp only [Fin.le_def] at h ⊢
    have hb (ν : Fin Ω.numBases) := Fin.lt_def.1 (Ω.left_lt_right ν)
    exact moveIdx_disjoint (hb μ) (hb (Ω.dual μ))
      ⟨hi.le_left_or_right_le μ, hi.le_left_or_right_le (Ω.dual μ)⟩
      ⟨hj.le_left_or_right_le μ, hj.le_left_or_right_le (Ω.dual μ)⟩
      ⟨hm.le_left_or_right_le μ, hm.le_left_or_right_le (Ω.dual μ)⟩ h
  · -- A base and its dual start together exactly when they did before.
    simp only [Finset.mem_image]
    rintro _ ⟨⟨p, μ, q⟩, hc, rfl⟩ hl
    obtain rfl : p = q := hΩ.eq_of_left_eq _ hc (Fin.ext (moveIdx_injective (Fin.ext_iff.1 hl)))
    rfl
  · -- Constant bases on one item come from constant bases on one item.
    simp only [Finset.mem_map]
    rintro _ ⟨⟨k, a⟩, hb, rfl⟩ _ ⟨⟨k', a'⟩, hb', rfl⟩ hk
    simpa using hΩ.label_eq (k, a) hb (k', a') hb' (by simpa using hk)

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

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` sends the item `hₖ` to `h_{moveItem k}`. -/
theorem moveSectionHom_inr_of (k : Fin Ω.numItems) :
    moveSectionHom hi hj hm
        ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup) =
      ((inr (FreeGroup.of (Ω.moveItem i j m k)) : GX (FreeGroup A) (Fin Ω.numItems)) :
        (Ω.moveSection i j m hi hj hm).coordGroup) := by
  simp [moveSectionHom]

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

/-- Substituting words for the renamed items is substituting the renamed words. -/
private theorem substituteVars_map_moveItem (W : Fin Ω.numItems → List (A × Bool))
    (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    substituteVars W (w.map (Prod.map (Sum.map (Ω.moveItem i j m) id) id)) =
      substituteVars (W ∘ Ω.moveItem i j m) w := by
  simp only [substituteVars, List.flatMap_map]
  congr 1
  funext ⟨y, b⟩
  cases y <;> rfl

/-- A property of the two substituted sides of every equation of the moved equation is the
property of `Ω` for the words with the items renamed. -/
private theorem forall_mem_equations_moveSection (W : Fin Ω.numItems → List (A × Bool))
    (P : List (A × Bool) → List (A × Bool) → Prop) :
    (∀ e ∈ (Ω.moveSection i j m hi hj hm).equations,
      P (substituteVars W e.1) (substituteVars W e.2)) ↔
      ∀ e ∈ Ω.equations, P (substituteVars (W ∘ Ω.moveItem i j m) e.1)
        (substituteVars (W ∘ Ω.moveItem i j m) e.2) := by
  rw [equations_moveSection hi hj hm, Set.forall_mem_image]
  simp only [substituteVars_map_moveItem]

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

/-- A solution of `Ω` is the composite of the corresponding solution of `Ω′` with
`F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem toHom_comp_moveSectionHom (U : Ω.Solution) :
    (solutionEquivMoveSection hi hj hm U).toHom.comp (moveSectionHom hi hj hm) = U.toHom :=
  CoordGroup.gHom_ext fun k => by
    rw [GHom.coe_comp, Function.comp_apply, moveSectionHom_inr_of]
    simp

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

/-- Moving the closed section `[0, 2]` of `h₀ = h₁`, `h₂ = a` behind `[2, 3]` gives `h₁ = h₂`,
`h₀ = a`: the bases move to `[1, 2]`, `[2, 3]` and the constant base to `h₀`. -/
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
