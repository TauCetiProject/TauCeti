/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import TauCeti.Combinatorics.PlanarMatching.Basic
import TauCeti.Combinatorics.NoncrossingPartition.PerfectMatching

/-!
# Half-diagrams and their count

A **half-diagram** on `n` points with `k` defects is the bottom half of a Temperley–Lieb diagram
cut horizontally through `k` through strands: the points `0, …, n - 1` on a line, some of them
joined in pairs by arcs drawn above the line, the others, the **defects**, carrying a vertical
strand up to infinity. The arcs must not cross each other and must not pass over a defect. Here a
half-diagram is encoded by the involution `σ` of `Fin n` that exchanges the two ends of each arc
and fixes the defects (`Equiv.Perm.IsHalfDiagram`), and `TauCeti.HalfDiagram n k` is the finite
type of those with exactly `k` fixed points.

Half-diagrams index the bases of the cell modules of the Temperley–Lieb algebra on `n` strands,
and cutting a Temperley–Lieb diagram `n → m` with `k` through strands across those strands gives
a pair of half-diagrams with `k` defects, one on each boundary. So their number
`TauCeti.halfCount n k` is the rank of a cell module and the factor from which diagrams are counted
by their through strands. With no defect, a half-diagram is a planar matching
(`TauCeti.HalfDiagram.zeroEquivPlanarMatching`).

Deleting the last point gives the branching rule: if the last point is a defect, deleting it
leaves a half-diagram with one defect fewer (`TauCeti.HalfDiagram.lastDefectEquiv`); otherwise it
ends an arc, and deleting it turns its partner into the rightmost defect, giving a half-diagram with
one defect more (`TauCeti.HalfDiagram.lastArcEquiv`). The resulting recurrence
`halfCount (n + 1) (k + 1) = halfCount n k + halfCount n (k + 2)` is the ballot recurrence, which
gives the closed formula
`halfCount n k = n.choose ((n - k) / 2) - n.choose ((n - k) / 2 - 1)` for `k < n` with `n - k`
even, `halfCount n n = 1`, and `halfCount n k = 0` when `n < k` or `n - k` is odd.

## Main definitions

* `Equiv.Perm.IsHalfDiagram σ`: `σ` is an involution whose arcs neither cross each other nor pass
  over a fixed point.
* `TauCeti.HalfDiagram n k`: the half-diagrams on `n` points with `k` defects.
* `TauCeti.halfCount n k`: their number.
* `TauCeti.HalfDiagram.rightmostDefect D`: the rightmost defect of a half-diagram with at least
  one defect.

## Main results

* `TauCeti.HalfDiagram.lastDefectEquiv`, `TauCeti.HalfDiagram.lastArcEquiv`: the branching
  bijections obtained by deleting the last point.
* `TauCeti.halfCount_succ_succ`, `TauCeti.halfCount_succ_zero`, `TauCeti.halfCount_zero_zero`,
  `TauCeti.halfCount_zero_succ`: the ballot recurrence and its initial values.
* `TauCeti.halfCount_eq_zero_of_lt`, `TauCeti.halfCount_eq_zero_of_odd`: there is no half-diagram
  with more defects than points, nor one whose number of points and number of defects have
  different parities; `TauCeti.halfCount_pos` and `TauCeti.halfCount_eq_zero_iff`: these are the
  only obstructions.
* `TauCeti.halfCount_add_two_mul_add_choose`: the ballot formula
  `halfCount (k + 2 * i) k + (k + 2 * i).choose (i + k + 1) = (k + 2 * i).choose i`, and its
  subtractive form `TauCeti.halfCount_eq_choose_sub_choose`.
* `TauCeti.halfCount_self`: the only half-diagram with as many defects as points has no arc.
* `TauCeti.halfCount_two_mul_zero`: the half-diagrams on `2 * n` points without defects are
  counted by the Catalan number `catalan n`.

## References

* B. W. Westbury, *The representation theory of the Temperley–Lieb algebras*, Math. Z. 219
  (1995), 539–565.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505 (half-diagrams appear there as link states).
-/

public section

open Equiv Finset

namespace Equiv.Perm

variable {α : Type*} [LinearOrder α]

/-- A permutation `σ` of a linearly ordered type is a **half-diagram** when it is an involution
whose arcs `{a, σ a}`, `σ a ≠ a`, do not interleave (`Equiv.Perm.IsNoncrossingMatching`) and pass
over no fixed point: no fixed point lies strictly between the two ends of an arc. The fixed points
are the defects of the half-diagram, the ends of its through strands. -/
def IsHalfDiagram (σ : Perm α) : Prop :=
  Function.Involutive σ ∧ σ.IsNoncrossingMatching ∧ ∀ ⦃a x : α⦄, a < x → x < σ a → σ x ≠ x

/-- The defining conditions of `Equiv.Perm.IsHalfDiagram`. -/
theorem isHalfDiagram_iff {σ : Perm α} :
    σ.IsHalfDiagram ↔ Function.Involutive σ ∧ σ.IsNoncrossingMatching ∧
      ∀ ⦃a x : α⦄, a < x → x < σ a → σ x ≠ x :=
  Iff.rfl

instance [Fintype α] (σ : Perm α) : Decidable σ.IsHalfDiagram :=
  inferInstanceAs <| Decidable <| (∀ x, σ (σ x) = x) ∧ σ.IsNoncrossingMatching ∧
    ∀ ⦃a x : α⦄, a < x → x < σ a → σ x ≠ x

end Equiv.Perm

namespace TauCeti

/-- The **half-diagrams** on `n` points with `k` defects: the involutions of `Fin n` whose arcs
neither cross each other nor pass over a fixed point (`Equiv.Perm.IsHalfDiagram`), with exactly
`k` fixed points. -/
abbrev HalfDiagram (n k : ℕ) : Type :=
  {σ : Perm (Fin n) // σ.IsHalfDiagram ∧ #{x | σ x = x} = k}

/-- The number of half-diagrams on `n` points with `k` defects. It is the rank of the cell module
of the Temperley–Lieb algebra on `n` strands with `k` through strands. -/
def halfCount (n k : ℕ) : ℕ :=
  Fintype.card (HalfDiagram n k)

/-- `halfCount n k` is the cardinality of `HalfDiagram n k`. -/
@[simp]
theorem card_halfDiagram (n k : ℕ) : Fintype.card (HalfDiagram n k) = halfCount n k := (rfl)

namespace HalfDiagram

variable {n k : ℕ}

/-- A half-diagram has no more defects than points. -/
theorem defects_le (D : HalfDiagram n k) : k ≤ n := by
  rw [← D.property.2]
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)

/-! ### Deleting and adjoining a last point -/

/-- An involution has the same fixed points as a function and as a permutation. -/
private theorem card_toPerm_eq_self {m : ℕ} {f : Fin m → Fin m} (hf : Function.Involutive f) :
    #{x | hf.toPerm f x = x} = #{x | f x = x} := (rfl)

/-- Delete the last point of `Fin (n + 1)` from an involution `σ`: the partner of the last point
becomes a fixed point, and all other points keep their partners. -/
private def eraseLast (σ : Fin (n + 1) → Fin (n + 1)) (i : Fin n) : Fin n :=
  if h : σ i.castSucc = Fin.last n then i else (σ i.castSucc).castPred h

private theorem eraseLast_of_eq {σ : Fin (n + 1) → Fin (n + 1)} {i : Fin n}
    (h : σ i.castSucc = Fin.last n) : eraseLast σ i = i := by
  simp [eraseLast, h]

private theorem castSucc_eraseLast {σ : Fin (n + 1) → Fin (n + 1)} {i : Fin n}
    (h : σ i.castSucc ≠ Fin.last n) : (eraseLast σ i).castSucc = σ i.castSucc := by
  simp [eraseLast, h]

private theorem eraseLast_eq_self_iff {σ : Fin (n + 1) → Fin (n + 1)} {i : Fin n} :
    eraseLast σ i = i ↔ σ i.castSucc = i.castSucc ∨ σ i.castSucc = Fin.last n := by
  by_cases h : σ i.castSucc = Fin.last n
  · simp [eraseLast_of_eq h, h]
  · rw [← Fin.castSucc_inj, castSucc_eraseLast h]
    simp [h]

/-- A point other than the last one that is not fixed by `eraseLast σ` keeps its partner. -/
private theorem castSucc_eraseLast_of_ne {σ : Fin (n + 1) → Fin (n + 1)} {i : Fin n}
    (h : eraseLast σ i ≠ i) : (eraseLast σ i).castSucc = σ i.castSucc :=
  castSucc_eraseLast fun h' => h (eraseLast_of_eq h')

private theorem eraseLast_involutive {σ : Fin (n + 1) → Fin (n + 1)}
    (hσ : Function.Involutive σ) : Function.Involutive (eraseLast σ) := by
  intro i
  by_cases h : σ i.castSucc = Fin.last n
  · rw [eraseLast_of_eq h, eraseLast_of_eq h]
  · have h' : σ (eraseLast σ i).castSucc ≠ Fin.last n := by
      rw [castSucc_eraseLast h, hσ]
      exact Fin.castSucc_ne_last i
    rw [← Fin.castSucc_inj, castSucc_eraseLast h', castSucc_eraseLast h, hσ]

private theorem isHalfDiagram_eraseLast {σ : Perm (Fin (n + 1))} (hσ : σ.IsHalfDiagram) :
    ((eraseLast_involutive hσ.1).toPerm _).IsHalfDiagram := by
  obtain ⟨hinv, hnc, hdef⟩ := hσ
  rw [Perm.isNoncrossingMatching_iff] at hnc
  refine ⟨eraseLast_involutive hinv, Perm.isNoncrossingMatching_iff.mpr ?_, ?_⟩ <;>
    simp only [Function.Involutive.coe_toPerm]
  · intro a b hab hba hlt
    have ha := castSucc_eraseLast_of_ne (σ := σ) (i := a) (hab.trans hba).ne'
    have hb := castSucc_eraseLast_of_ne (σ := σ) (i := b) (hba.trans hlt).ne'
    rw [← Fin.castSucc_lt_castSucc_iff, ← Fin.castSucc_lt_castSucc_iff, ha, hb] at hlt
    rw [← Fin.castSucc_lt_castSucc_iff, ha] at hba
    exact hnc (Fin.castSucc_lt_castSucc_iff.mpr hab) hba hlt
  · intro a x hax hxa hx
    have ha := castSucc_eraseLast_of_ne (σ := σ) (i := a) (hax.trans hxa).ne'
    rw [← Fin.castSucc_lt_castSucc_iff, ha] at hxa
    rcases eraseLast_eq_self_iff.mp hx with hx | hx
    · exact hdef (Fin.castSucc_lt_castSucc_iff.mpr hax) hxa hx
    · refine hnc (Fin.castSucc_lt_castSucc_iff.mpr hax) hxa ?_
      rw [hx, ← ha]
      exact Fin.castSucc_lt_last _

/-- Deleting the last point removes a fixed point if the last point was one, and creates one,
the former partner of the last point, otherwise. -/
private theorem card_eraseLast_eq_self {σ : Fin (n + 1) → Fin (n + 1)}
    (hσ : Function.Involutive σ) :
    #{i | eraseLast σ i = i} + (if σ (Fin.last n) = Fin.last n then 1 else 0) =
      #{x | σ x = x} + (if σ (Fin.last n) = Fin.last n then 0 else 1) := by
  have hlast : ∀ i : Fin n, σ i.castSucc = Fin.last n ↔ σ (Fin.last n) = i.castSucc :=
    fun i => ⟨fun h => by rw [← h, hσ], fun h => by rw [← h, hσ]⟩
  have hsplit : ∀ i : Fin n, (if eraseLast σ i = i then 1 else 0) =
      (if σ i.castSucc = i.castSucc then 1 else 0) +
        (if σ (Fin.last n) = i.castSucc then 1 else 0) := by
    intro i
    by_cases h₁ : σ i.castSucc = i.castSucc
    · have h₂ : ¬ σ (Fin.last n) = i.castSucc := by
        rw [← hlast, h₁]
        exact Fin.castSucc_ne_last i
      simp [eraseLast_eq_self_iff, h₁, h₂]
    · simp [eraseLast_eq_self_iff, h₁, hlast]
  -- The partner of the last point is a single point of `Fin (n + 1)`.
  have hone : ∑ i : Fin n, (if σ (Fin.last n) = i.castSucc then 1 else 0) +
      (if σ (Fin.last n) = Fin.last n then 1 else 0) = 1 := by
    rw [← Fin.sum_univ_castSucc (f := fun x => if σ (Fin.last n) = x then 1 else 0)]
    simp
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_castSucc (f := fun x => if σ x = x then 1 else 0)]
  simp only [hsplit, Finset.sum_add_distrib]
  split_ifs at hone ⊢ <;> omega

/-- Adjoin a last point to an involution `τ` of `Fin n`, joined by an arc to the point `p`, or a
fixed point when `p` is the last point itself. -/
private def insertLast (τ : Fin n → Fin n) (p : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) :=
  Fin.lastCases p fun i => if i.castSucc = p then Fin.last n else (τ i).castSucc

@[simp]
private theorem insertLast_last (τ : Fin n → Fin n) (p : Fin (n + 1)) :
    insertLast τ p (Fin.last n) = p := by
  simp [insertLast]

@[simp]
private theorem insertLast_castSucc (τ : Fin n → Fin n) (p : Fin (n + 1)) (i : Fin n) :
    insertLast τ p i.castSucc = if i.castSucc = p then Fin.last n else (τ i).castSucc := by
  simp [insertLast]

/-- Adjoining a last point to an involution gives an involution, provided the new partner `p` of
the last point is the last point itself or a fixed point of `τ`. -/
private theorem insertLast_involutive {τ : Fin n → Fin n} (hτ : Function.Involutive τ)
    {p : Fin (n + 1)} (hp : ∀ i, i.castSucc = p → τ i = i) :
    Function.Involutive (insertLast τ p) := by
  intro x
  induction x using Fin.lastCases with
  | last =>
    induction p using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i =>
    by_cases hi : i.castSucc = p
    · subst hi
      simp
    · have hτi : ¬ (τ i).castSucc = p := fun h => hi (by rw [← hτ i, hp _ h, h])
      rw [insertLast_castSucc, ite_eq_right hi, insertLast_castSucc, ite_eq_right hτi, hτ i]

private theorem eraseLast_insertLast {τ : Fin n → Fin n} {p : Fin (n + 1)}
    (hp : ∀ i, i.castSucc = p → τ i = i) : eraseLast (insertLast τ p) = τ := by
  funext i
  by_cases hi : i.castSucc = p
  · rw [eraseLast_of_eq (by rw [insertLast_castSucc, ite_eq_left hi]), hp i hi]
  · have h : insertLast τ p i.castSucc = (τ i).castSucc := by
      rw [insertLast_castSucc, ite_eq_right hi]
    rw [← Fin.castSucc_inj, castSucc_eraseLast (by rw [h]; exact Fin.castSucc_ne_last _), h]

private theorem insertLast_eraseLast {σ : Fin (n + 1) → Fin (n + 1)}
    (hσ : Function.Involutive σ) : insertLast (eraseLast σ) (σ (Fin.last n)) = σ := by
  funext x
  induction x using Fin.lastCases with
  | last => simp
  | cast i =>
    rw [insertLast_castSucc]
    by_cases hi : i.castSucc = σ (Fin.last n)
    · rw [ite_eq_left hi, hi, hσ]
    · have h : σ i.castSucc ≠ Fin.last n := fun h => hi (by rw [← h, hσ])
      rw [ite_eq_right hi, castSucc_eraseLast h]

/-- Adjoining a last point to a half-diagram gives a half-diagram, provided the new partner `p` of
the last point is the last point itself or a defect, and no defect lies to its right. -/
private theorem isHalfDiagram_insertLast {τ : Perm (Fin n)} (hτ : τ.IsHalfDiagram)
    {p : Fin (n + 1)} (hp : ∀ i, i.castSucc = p → τ i = i)
    (hmax : ∀ i, τ i = i → i.castSucc ≤ p) :
    ((insertLast_involutive hτ.1 hp).toPerm _).IsHalfDiagram := by
  obtain ⟨hinv, hnc, hdef⟩ := hτ
  rw [Perm.isNoncrossingMatching_iff] at hnc
  refine ⟨insertLast_involutive hinv hp, Perm.isNoncrossingMatching_iff.mpr ?_, ?_⟩ <;>
    simp only [Function.Involutive.coe_toPerm]
  · intro a b hab hba hlt
    -- None of `a < b < σ a < σ b` is the last point, and `a` is not the partner `p` of the last
    -- point, since otherwise `σ a` would be the last point.
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.mpr (Fin.le_last _))
    | cast a =>
    induction b using Fin.lastCases with
    | last => exact absurd hba (not_lt.mpr (Fin.le_last _))
    | cast b =>
    by_cases ha : a.castSucc = p
    · rw [insertLast_castSucc, ite_eq_left ha] at hlt
      exact absurd hlt (not_lt.mpr (Fin.le_last _))
    rw [insertLast_castSucc, ite_eq_right ha, Fin.castSucc_lt_castSucc_iff] at hba
    rw [Fin.castSucc_lt_castSucc_iff] at hab
    by_cases hb : b.castSucc = p
    · exact hdef hab hba (hp b hb)
    · rw [insertLast_castSucc, ite_eq_right ha, insertLast_castSucc, ite_eq_right hb,
        Fin.castSucc_lt_castSucc_iff] at hlt
      exact hnc hab hba hlt
  · intro a x hax hxa hx
    induction x using Fin.lastCases with
    | last => exact absurd hxa (not_lt.mpr (Fin.le_last _))
    | cast x =>
    have hxp : ¬ x.castSucc = p := fun h => by
      rw [insertLast_castSucc, ite_eq_left h] at hx
      exact Fin.castSucc_ne_last x hx.symm
    rw [insertLast_castSucc, ite_eq_right hxp, Fin.castSucc_inj] at hx
    induction a using Fin.lastCases with
    | last => exact absurd hax (not_lt.mpr (Fin.le_last _))
    | cast a =>
    by_cases ha : a.castSucc = p
    · exact absurd (ha ▸ hax) (not_lt.mpr (hmax x hx))
    · rw [insertLast_castSucc, ite_eq_right ha, Fin.castSucc_lt_castSucc_iff] at hxa
      rw [Fin.castSucc_lt_castSucc_iff] at hax
      exact hdef hax hxa hx

/-! ### The branching bijections -/

/-- **Deleting a last defect.** The half-diagrams on `n + 1` points whose last point is a defect
correspond to the half-diagrams on `n` points with one defect fewer. -/
def lastDefectEquiv (n k : ℕ) :
    {D : HalfDiagram (n + 1) (k + 1) // D.val (Fin.last n) = Fin.last n} ≃ HalfDiagram n k where
  toFun D := ⟨(eraseLast_involutive D.1.2.1.1).toPerm _, isHalfDiagram_eraseLast D.1.2.1, by
    have := card_eraseLast_eq_self D.1.2.1.1
    simp only [D.2, ite_true, D.1.2.2] at this
    rw [card_toPerm_eq_self]
    omega⟩
  invFun D :=
    have hp : ∀ i : Fin n, i.castSucc = Fin.last n → D.1 i = i :=
      fun i h => absurd h (Fin.castSucc_ne_last i)
    ⟨⟨(insertLast_involutive D.2.1.1 hp).toPerm _,
      isHalfDiagram_insertLast D.2.1 hp fun i _ => Fin.le_last _, by
        have := card_eraseLast_eq_self (insertLast_involutive D.2.1.1 hp)
        rw [eraseLast_insertLast hp] at this
        simp only [insertLast_last, ite_true, D.2.2] at this
        rw [card_toPerm_eq_self]
        omega⟩, by simp⟩
  left_inv D := by
    refine Subtype.ext <| Subtype.ext <| Equiv.ext fun x => ?_
    have h := insertLast_eraseLast D.1.2.1.1
    rw [D.2] at h
    simpa using congrFun h x
  right_inv D := Subtype.ext <| Equiv.ext fun i => by
    simp [eraseLast_insertLast fun i h => absurd h (Fin.castSucc_ne_last i)]

/-- Deleting a last defect keeps every arc and every other defect. -/
@[simp]
theorem lastDefectEquiv_apply_castSucc
    (D : {D : HalfDiagram (n + 1) (k + 1) // D.val (Fin.last n) = Fin.last n}) (i : Fin n) :
    ((lastDefectEquiv n k D).val i).castSucc = D.1.val i.castSucc := by
  refine castSucc_eraseLast fun h => Fin.castSucc_ne_last i (D.1.val.injective ?_)
  rw [h, D.2]

/-- Adjoining a last defect. -/
@[simp]
theorem lastDefectEquiv_symm_apply_last (D : HalfDiagram n k) :
    ((lastDefectEquiv n k).symm D).1.val (Fin.last n) = Fin.last n :=
  ((lastDefectEquiv n k).symm D).2

/-- Adjoining a last defect keeps every arc and every other defect. -/
@[simp]
theorem lastDefectEquiv_symm_apply_castSucc (D : HalfDiagram n k) (i : Fin n) :
    ((lastDefectEquiv n k).symm D).1.val i.castSucc = (D.val i).castSucc := by
  simp [lastDefectEquiv, Fin.castSucc_ne_last]

/-! ### The rightmost defect -/

private theorem nonempty_defects (D : HalfDiagram n (k + 1)) :
    ({i | D.val i = i} : Finset (Fin n)).Nonempty :=
  Finset.card_pos.mp (D.2.2.symm ▸ k.succ_pos)

/-- The **rightmost defect** of a half-diagram with at least one defect. -/
def rightmostDefect (D : HalfDiagram n (k + 1)) : Fin n :=
  ({i | D.val i = i} : Finset (Fin n)).max' (nonempty_defects D)

/-- The rightmost defect is a defect. -/
@[simp]
theorem val_rightmostDefect (D : HalfDiagram n (k + 1)) :
    D.val (rightmostDefect D) = rightmostDefect D := by
  have := Finset.max'_mem ({i | D.val i = i} : Finset (Fin n)) (nonempty_defects D)
  rw [Finset.mem_filter] at this
  exact this.2

/-- Every defect lies to the left of the rightmost defect. -/
theorem le_rightmostDefect (D : HalfDiagram n (k + 1)) {i : Fin n} (hi : D.val i = i) :
    i ≤ rightmostDefect D :=
  Finset.le_max' ({i | D.val i = i} : Finset (Fin n)) i (Finset.mem_filter.mpr ⟨mem_univ _, hi⟩)

/-- A defect lying to the right of every defect is the rightmost defect. -/
theorem eq_rightmostDefect (D : HalfDiagram n (k + 1)) {j : Fin n} (hj : D.val j = j)
    (h : ∀ i, D.val i = i → i ≤ j) : j = rightmostDefect D :=
  le_antisymm (le_rightmostDefect D hj) (h _ (val_rightmostDefect D))

/-! ### Deleting a last point joined by an arc -/

/-- Delete the last point of a half-diagram in which it ends an arc; its partner becomes a
defect. -/
private def eraseLastArc
    (D : {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n}) :
    HalfDiagram n (k + 1) :=
  ⟨(eraseLast_involutive D.1.2.1.1).toPerm _, isHalfDiagram_eraseLast D.1.2.1, by
    have := card_eraseLast_eq_self D.1.2.1.1
    simp only [D.2, ite_false, D.1.2.2] at this
    rw [card_toPerm_eq_self]
    omega⟩

@[simp]
private theorem coe_eraseLastArc
    (D : {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n}) :
    ⇑(eraseLastArc D).val = eraseLast D.1.val := by
  simp [eraseLastArc]

/-- After deleting the last point, the former partner of the last point is the rightmost defect:
a defect further right would lie under the arc ending at the last point. -/
private theorem rightmostDefect_eraseLastArc
    (D : {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n}) :
    rightmostDefect (eraseLastArc D) = (D.1.val (Fin.last n)).castPred D.2 := by
  have hinv := D.1.2.1.1
  refine (eq_rightmostDefect _ ?_ fun i hi => ?_).symm
  · rw [coe_eraseLastArc]
    exact eraseLast_of_eq (by rw [Fin.castSucc_castPred, hinv])
  · rw [coe_eraseLastArc] at hi
    rw [Fin.le_castPred_iff]
    by_contra hlt
    rw [not_le] at hlt
    rcases eraseLast_eq_self_iff.mp hi with hi | hi
    · exact D.1.2.1.2.2 hlt (by rw [hinv]; exact Fin.castSucc_lt_last i) hi
    · have h := congrArg D.1.val hi
      rw [hinv] at h
      exact hlt.ne h.symm

/-- **Deleting a last point joined by an arc.** The half-diagrams on `n + 1` points whose last
point ends an arc correspond to the half-diagrams on `n` points with one defect more: deleting the
last point turns its partner into the rightmost defect, and conversely the rightmost defect is
joined to a new last point. -/
def lastArcEquiv (n k : ℕ) :
    {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n} ≃ HalfDiagram n (k + 1) where
  toFun := eraseLastArc
  invFun D :=
    have hp : ∀ i : Fin n, i.castSucc = (rightmostDefect D).castSucc → D.1 i = i :=
      fun i h => by rw [Fin.castSucc_inj.mp h, val_rightmostDefect]
    ⟨⟨(insertLast_involutive D.2.1.1 hp).toPerm _,
      isHalfDiagram_insertLast D.2.1 hp fun i hi =>
        Fin.castSucc_le_castSucc_iff.mpr (le_rightmostDefect D hi), by
        have := card_eraseLast_eq_self (insertLast_involutive D.2.1.1 hp)
        rw [eraseLast_insertLast hp] at this
        simp only [insertLast_last, Fin.castSucc_ne_last, ite_false, D.2.2] at this
        rw [card_toPerm_eq_self]
        omega⟩, by simp [Fin.castSucc_ne_last]⟩
  left_inv D := by
    refine Subtype.ext <| Subtype.ext <| Equiv.ext fun x => ?_
    have h := insertLast_eraseLast D.1.2.1.1
    simp only [Function.Involutive.coe_toPerm, coe_eraseLastArc, rightmostDefect_eraseLastArc,
      Fin.castSucc_castPred]
    exact congrFun h x
  right_inv D := Subtype.ext <| Equiv.ext fun i => by
    simp only [coe_eraseLastArc, Function.Involutive.coe_toPerm]
    rw [eraseLast_insertLast fun i h => by rw [Fin.castSucc_inj.mp h, val_rightmostDefect]]

/-- Deleting a last point joined by an arc keeps the partner of every point not joined to it. -/
theorem lastArcEquiv_apply_castSucc
    (D : {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n}) {i : Fin n}
    (h : D.1.val i.castSucc ≠ Fin.last n) :
    ((lastArcEquiv n k D).val i).castSucc = D.1.val i.castSucc :=
  castSucc_eraseLast h

/-- Deleting the last point turns its former partner into a defect. -/
@[simp]
theorem lastArcEquiv_apply_castPred
    (D : {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n}) :
    (lastArcEquiv n k D).val ((D.1.val (Fin.last n)).castPred D.2) =
      (D.1.val (Fin.last n)).castPred D.2 :=
  eraseLast_of_eq (by rw [Fin.castSucc_castPred, D.1.2.1.1])

/-- The new last point is joined to the rightmost defect. -/
@[simp]
theorem lastArcEquiv_symm_apply_last (D : HalfDiagram n (k + 1)) :
    ((lastArcEquiv n k).symm D).1.val (Fin.last n) = (rightmostDefect D).castSucc := by
  simp [lastArcEquiv]

/-- Joining a new last point to the rightmost defect keeps every other arc and defect. -/
@[simp]
theorem lastArcEquiv_symm_apply_castSucc (D : HalfDiagram n (k + 1)) (i : Fin n) :
    ((lastArcEquiv n k).symm D).1.val i.castSucc =
      if i = rightmostDefect D then Fin.last n else (D.val i).castSucc := by
  simp [lastArcEquiv]

/-! ### No defects -/

/-- A half-diagram without defects is a planar matching. -/
def zeroEquivPlanarMatching (n : ℕ) : HalfDiagram n 0 ≃ PlanarMatching n where
  toFun D := ⟨⟨D.1, isPerfectMatching_iff.mpr ⟨D.2.1.1, fun a ha =>
      Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp D.2.2) (Finset.mem_univ a) ha⟩⟩,
    D.2.1.2.1⟩
  invFun x := ⟨x.1.1, ⟨x.1.2.involutive, x.2, fun _ y _ _ => x.1.apply_ne y⟩,
    Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun y _ => x.1.apply_ne y⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A half-diagram without defects is a planar matching with the same partners. -/
@[simp]
theorem zeroEquivPlanarMatching_apply_val (D : HalfDiagram n 0) :
    (zeroEquivPlanarMatching n D).1.val = D.val := (rfl)

/-- A planar matching is a half-diagram without defects with the same partners. -/
@[simp]
theorem zeroEquivPlanarMatching_symm_apply_val (x : PlanarMatching n) :
    ((zeroEquivPlanarMatching n).symm x).val = x.1.val := (rfl)

end HalfDiagram

/-! ### Counting half-diagrams -/

/-- Splitting the half-diagrams on `n + 1` points according to whether the last point is a
defect. -/
private theorem halfCount_succ_eq (n k : ℕ) :
    halfCount (n + 1) k =
      Fintype.card {D : HalfDiagram (n + 1) k // D.val (Fin.last n) = Fin.last n} +
        Fintype.card {D : HalfDiagram (n + 1) k // D.val (Fin.last n) ≠ Fin.last n} := by
  rw [halfCount, ← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl _).symm

/-- **The ballot recurrence.** A half-diagram on `n + 1` points either has its last point as a
defect or joins it by an arc to the rightmost defect of the rest. -/
theorem halfCount_succ_succ (n k : ℕ) :
    halfCount (n + 1) (k + 1) = halfCount n k + halfCount n (k + 2) := by
  rw [halfCount_succ_eq, Fintype.card_congr (HalfDiagram.lastDefectEquiv n k),
    Fintype.card_congr (HalfDiagram.lastArcEquiv n (k + 1)), halfCount, halfCount]

/-- Without defects, the last point ends an arc. -/
theorem halfCount_succ_zero (n : ℕ) : halfCount (n + 1) 0 = halfCount n 1 := by
  have : IsEmpty {D : HalfDiagram (n + 1) 0 // D.val (Fin.last n) = Fin.last n} :=
    ⟨fun D => Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp D.1.2.2)
      (Finset.mem_univ (Fin.last n)) D.2⟩
  rw [halfCount_succ_eq, Fintype.card_eq_zero, Fintype.card_congr (HalfDiagram.lastArcEquiv n 0),
    zero_add, halfCount]

/-- The empty half-diagram. -/
theorem halfCount_zero_zero : halfCount 0 0 = 1 := by
  decide

/-- There is no defect without points. -/
@[simp]
theorem halfCount_zero_succ (k : ℕ) : halfCount 0 (k + 1) = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun D => by simpa using D.2.2⟩

private theorem halfCount_eq_zero_of_lt_or_odd :
    ∀ {n k : ℕ}, n < k ∨ Odd (n + k) → halfCount n k = 0
  | 0, 0, h => by simp at h
  | 0, k + 1, _ => halfCount_zero_succ k
  | n + 1, 0, h => by
    rw [halfCount_succ_zero]
    refine halfCount_eq_zero_of_lt_or_odd (Or.inr ?_)
    simpa [Nat.odd_iff] using h
  | n + 1, k + 1, h => by
    rw [halfCount_succ_succ, halfCount_eq_zero_of_lt_or_odd, halfCount_eq_zero_of_lt_or_odd] <;>
      simp only [Nat.odd_iff] at h ⊢ <;> omega

/-- There is no half-diagram with more defects than points. -/
theorem halfCount_eq_zero_of_lt {n k : ℕ} (h : n < k) : halfCount n k = 0 :=
  halfCount_eq_zero_of_lt_or_odd (Or.inl h)

/-- There is no half-diagram whose numbers of points and of defects have different parities: the
points that are not defects come in pairs. -/
theorem halfCount_eq_zero_of_odd {n k : ℕ} (h : Odd (n + k)) : halfCount n k = 0 :=
  halfCount_eq_zero_of_lt_or_odd (Or.inr h)

/-- The non-defect points of a half-diagram come in pairs. -/
theorem HalfDiagram.even_sub {n k : ℕ} (D : HalfDiagram n k) : Even (n - k) := by
  have hpos : 0 < halfCount n k := Fintype.card_pos_iff.mpr ⟨D⟩
  have hnot : ¬ Odd (n + k) := fun h => hpos.ne' (halfCount_eq_zero_of_odd h)
  rw [Nat.not_odd_iff_even, Nat.even_iff] at hnot
  rw [Nat.even_iff]
  have := D.defects_le
  omega

/-- There is a half-diagram on `n` points with `k` defects whenever `k ≤ n` and `n - k` is
even. -/
theorem halfCount_pos : ∀ {n k : ℕ}, k ≤ n → Even (n + k) → 0 < halfCount n k
  | 0, 0, _, _ => by rw [halfCount_zero_zero]; exact Nat.one_pos
  | 0, k + 1, h, _ => by omega
  | n + 1, 0, _, h => by
    rw [Nat.even_iff] at h
    rw [halfCount_succ_zero]
    exact halfCount_pos (by omega) (by rw [Nat.even_iff]; omega)
  | n + 1, k + 1, h, he => by
    rw [Nat.even_iff] at he
    have := halfCount_pos (n := n) (k := k) (by omega) (by rw [Nat.even_iff]; omega)
    rw [halfCount_succ_succ]
    omega

/-- The half-diagrams on `n` points with `k` defects exist exactly when `k ≤ n` and `n - k` is
even. -/
theorem halfCount_eq_zero_iff {n k : ℕ} : halfCount n k = 0 ↔ n < k ∨ Odd (n + k) := by
  refine ⟨fun h => ?_, halfCount_eq_zero_of_lt_or_odd⟩
  by_contra h'
  rw [not_or, not_lt, Nat.not_odd_iff_even] at h'
  exact (halfCount_pos h'.1 h'.2).ne' h

/-- The only half-diagram with as many defects as points is the one without arcs. -/
@[simp]
theorem halfCount_self (n : ℕ) : halfCount n n = 1 := by
  induction n with
  | zero => exact halfCount_zero_zero
  | succ n ih => rw [halfCount_succ_succ, ih, halfCount_eq_zero_of_lt (by omega)]

/-- **The ballot formula.** The half-diagrams on `k + 2 * i` points with `k` defects, that is,
with `i` arcs, number `(k + 2 * i).choose i - (k + 2 * i).choose (i + k + 1)`; it is stated here
without subtraction. -/
theorem halfCount_add_two_mul_add_choose (k i : ℕ) :
    halfCount (k + 2 * i) k + (k + 2 * i).choose (i + k + 1) = (k + 2 * i).choose i := by
  induction i generalizing k with
  | zero => simp
  | succ i ih =>
    induction k with
    | zero =>
      have h := ih 1
      have p₁ := Nat.choose_succ_succ' (1 + 2 * i) (i + 1)
      have p₂ := Nat.choose_succ_succ' (1 + 2 * i) i
      have e : 0 + 2 * (i + 1) = 1 + 2 * i + 1 := by ring
      rw [e, halfCount_succ_zero]
      ring_nf at h p₁ p₂ ⊢
      omega
    | succ k ihk =>
      have h := ih (k + 2)
      have p₁ := Nat.choose_succ_succ' (k + 2 * (i + 1)) (i + k + 2)
      have p₂ := Nat.choose_succ_succ' (k + 2 * (i + 1)) i
      have e : k + 1 + 2 * (i + 1) = k + 2 * (i + 1) + 1 := by ring
      rw [e, halfCount_succ_succ]
      ring_nf at h ihk p₁ p₂ ⊢
      omega

/-- **The ballot formula**, in subtractive form: for `k < n` with `n - k` even, the half-diagrams
on `n` points with `k` defects number `n.choose ((n - k) / 2) - n.choose ((n - k) / 2 - 1)`. -/
theorem halfCount_eq_choose_sub_choose {n k : ℕ} (hkn : k < n) (h : Even (n + k)) :
    halfCount n k = n.choose ((n - k) / 2) - n.choose ((n - k) / 2 - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = k + 2 * i := ⟨(n - k) / 2, by rw [Nat.even_iff] at h; omega⟩
  have e : (k + 2 * i - k) / 2 = i := by omega
  -- `k < k + 2 * i` forces `1 ≤ i`, so `i - 1` and `i + k + 1` are complementary in `k + 2 * i`.
  have hsplit : k + 2 * i = (i - 1) + (i + k + 1) := by omega
  rw [e, Nat.choose_symm_of_eq_add hsplit]
  have := halfCount_add_two_mul_add_choose k i
  omega

/-- The half-diagrams on `2 * n` points without defects, that is, the planar matchings of
`2 * n` points, are counted by the Catalan number `catalan n`. -/
theorem halfCount_two_mul_zero (n : ℕ) : halfCount (2 * n) 0 = catalan n := by
  rw [halfCount, ← Nat.card_eq_fintype_card, Nat.card_congr (HalfDiagram.zeroEquivPlanarMatching _)]
  exact PerfectMatching.card_isNoncrossingMatching_eq_catalan (by simp)

/-- There are three half-diagrams on four points with two defects, and none with one defect: the
subtractive ballot formula, evaluated without its parity hypothesis, would wrongly give
`choose 4 1 - choose 4 0 = 3` there too. -/
example : halfCount 4 2 = 3 ∧ halfCount 4 1 = 0 :=
  ⟨by decide, halfCount_eq_zero_of_odd (by decide)⟩

/-- The squares of the numbers of half-diagrams on four points add up to `catalan 4 = 14`. -/
example : ∑ k ∈ Finset.range 5, halfCount 4 k ^ 2 = catalan 4 := by
  rw [catalan_eq_centralBinom_div]
  decide

end TauCeti
