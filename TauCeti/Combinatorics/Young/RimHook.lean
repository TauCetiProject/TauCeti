/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.Combinatorics.Young.BetaNumbers
public import TauCeti.Combinatorics.Young.Corner
import TauCeti.Combinatorics.Young.OfRowLens

/-!
# Rim hooks of a Young diagram

A **rim hook** (border strip, ribbon) of a Young diagram `μ` is a skew shape `μ / ν` that is
edge-connected and contains no `2 × 2` block.  Removing rim hooks is the recursion behind the
Murnaghan--Nakayama rule for the characters of the symmetric group, and the same move read on
beta-numbers is the abacus.

## The definition, and why it is the geometric one

The rows of a skew shape are intervals: row `i` of `μ / ν` is the set of columns
`[ν.rowLen i, μ.rowLen i)`.  So `μ / ν` is edge-connected exactly when the rows it meets form an
interval and two consecutive such rows overlap in a column, `ν.rowLen i < μ.rowLen (i + 1)`; and
it contains no `2 × 2` block exactly when two consecutive such rows overlap in at most one column,
`μ.rowLen (i + 1) ≤ ν.rowLen i + 1`.  `YoungDiagram.IsRimHook` therefore asks for `ν ≤ μ` with
`ν ≠ μ`, for the rows met by `μ / ν` to be `Set.OrdConnected`, and for
`μ.rowLen (i + 1) = ν.rowLen i + 1` at two consecutive rows the shape meets.

That the definition really says "connected, and no `2 × 2` block" is not left to the prose.  The
two geometric conditions are proved from it in `YoungDiagram.IsRimHook.mem_succ_succ_of_notMem` (no
cell of `μ / ν` has its diagonal neighbour in `μ / ν`, which for a skew shape is exactly
`2 × 2`-freeness, since a `2 × 2` block contains such a pair) and
`YoungDiagram.IsRimHook.mem_succ_rowLen` (consecutive rows met by the shape share a column, so the
shape is connected), and `YoungDiagram.isRimHook_of_forall` recovers the definition from them.

## Removing a rim hook is a move of one beta-number

Let `μ / ν` be a rim hook occupying the rows `a ≤ i ≤ b`.  Its row lengths satisfy
`ν.rowLen i = μ.rowLen (i + 1) - 1` for `a ≤ i < b`, so the beta-numbers of `ν` relative to a
bound `r > b` are those of `μ` with the value at `a` deleted, the values between shifted up by one
index, and the single new value

`ν.betaNumber r b = μ.betaNumber r a - (μ.card - ν.card)`.

Removing a rim hook of size `s` is thus exactly the move of one bead down `s` places on the
abacus, and the **height** `b - a` of the rim hook, one less than the number of rows it meets,
counts the beads the moving bead jumps over.  Both statements are proved here:
`YoungDiagram.IsRimHook.card_add_betaNumber` and
`YoungDiagram.IsRimHook.card_filter_betaNumber`.

## Main definitions

* `YoungDiagram.IsRimHook`: the skew shape `μ / ν` is a rim hook.  As in
  `YoungDiagram.InterlacedBy`, the ambient shape is written first.
* `YoungDiagram.rimHookRows`: the rows met by `μ / ν`.
* `YoungDiagram.rimHookHeight`: one less than the number of rows met by `μ / ν`.

## Main results

* `YoungDiagram.IsCorner.isRimHook_erase` and
  `YoungDiagram.IsRimHook.exists_isCorner_of_card_succ`: the rim hooks with one cell are exactly
  the erasures of corners.
* `YoungDiagram.IsRimHook.mem_succ_succ_of_notMem`, `YoungDiagram.IsRimHook.mem_succ_rowLen` and
  `YoungDiagram.isRimHook_of_forall`: the geometric reading of the definition.
* `YoungDiagram.IsRimHook.exists_rimHookRows_eq_Icc`: a rim hook meets a contiguous block of rows.
* `YoungDiagram.IsRimHook.card_add_rowLen`: the number of cells of a rim hook is
  `μ.rowLen a - ν.rowLen b` plus its height, stated without truncated subtraction.
* `YoungDiagram.IsRimHook.card_add_betaNumber`: removing a rim hook lowers one beta-number by the
  number of cells removed, with `YoungDiagram.betaNumber_eq_of_notMem_rimHookRows` and
  `YoungDiagram.IsRimHook.betaNumber_eq_betaNumber_succ` describing the other beta-numbers.
* `YoungDiagram.IsRimHook.card_filter_betaNumber`: the height of a rim hook is the number of
  beta-numbers of `μ` that the moved bead jumps over.
* `YoungDiagram.IsRimHook.update_betaNumber_eq_comp_cycleIcc`: the beta-numbers of `ν` with the
  bead of the bottom row raised are those of `μ`, rearranged by the cycle of the rows the hook
  meets, whose sign is `(-1)` to the height.
* `YoungDiagram.exists_isRimHook_rimHookRows_eq_Icc`,
  `YoungDiagram.IsRimHook.betaNumber_ne_betaNumber_add` and
  `YoungDiagram.IsRimHook.eq_of_card_eq_of_rimHookRows_eq_Icc`: conversely, raising a bead of `ν`
  to a free position adds a rim hook with that bottom row, every rim hook arises this way, and it is
  determined by its bottom row and size.  So the rim hooks of size `s` that can be added to `ν`
  correspond to the beads of `ν` that can move up `s` places.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 8, for border strips and their description by beta-numbers.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 4.10, for rim hooks, their heights and
  the Murnaghan--Nakayama rule.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/SchurWeyl/README.md),
  Layer 6, whose "rim hooks and Murnaghan--Nakayama" item this supplies the combinatorics of.
-/

public section

namespace YoungDiagram

variable {μ ν : YoungDiagram} {a b i j r : ℕ} {c : ℕ × ℕ}

/-! ### The definition -/

/-- The skew shape `μ / ν` is a **rim hook** (border strip): it is nonempty, edge-connected, and
contains no `2 × 2` block.  The conditions are recorded on row lengths, which is where the
geometry lands for a skew shape; see `YoungDiagram.IsRimHook.mem_succ_succ_of_notMem`,
`YoungDiagram.IsRimHook.mem_succ_rowLen` and `YoungDiagram.isRimHook_of_forall` for the
equivalence with the geometric conditions.  As in `YoungDiagram.InterlacedBy`, the ambient shape
is written first. -/
structure IsRimHook (μ ν : YoungDiagram) : Prop where
  /-- The removed shape is a sub-diagram. -/
  le : ν ≤ μ
  /-- The skew shape is nonempty. -/
  ne : ν ≠ μ
  /-- The rows met by the skew shape form an interval, so the shape is connected across rows. -/
  ordConnected : {i | ν.rowLen i < μ.rowLen i}.OrdConnected
  /-- Two consecutive rows met by the skew shape overlap in exactly one column. -/
  rowLen_succ : ∀ i, ν.rowLen i < μ.rowLen i → ν.rowLen (i + 1) < μ.rowLen (i + 1) →
    μ.rowLen (i + 1) = ν.rowLen i + 1

namespace IsRimHook

/-- A rim hook has at least one cell. -/
theorem card_lt (h : IsRimHook μ ν) : ν.card < μ.card :=
  Finset.card_lt_card (cells_ssubset_iff.mpr (lt_of_le_of_ne h.le h.ne))

end IsRimHook

/-! ### The geometry: connected, and no `2 × 2` block -/

/-- **A rim hook contains no `2 × 2` block**: the diagonal neighbour of a cell of `μ / ν` is never
a cell of `μ / ν`.  For a skew shape that is exactly `2 × 2`-freeness, because `μ` and `ν` are
lower sets, so a `2 × 2` block of `μ / ν` contains such a pair as its top-left and bottom-right
cells. -/
theorem IsRimHook.mem_succ_succ_of_notMem (h : IsRimHook μ ν) (hμ : (i, j) ∈ μ) (hν : (i, j) ∉ ν)
    (hμ' : (i + 1, j + 1) ∈ μ) : (i + 1, j + 1) ∈ ν := by
  rw [mem_iff_lt_rowLen] at hμ hν hμ' ⊢
  by_contra hν'
  have := h.rowLen_succ i (by omega) (by omega)
  omega

/-- **A rim hook is connected across rows**: if the rows `i` and `i + 1` both meet `μ / ν`, then
the cell `(i + 1, ν.rowLen i)` lies in `μ / ν`, directly below the cell `(i, ν.rowLen i)` of
`μ / ν`.  So consecutive rows met by the shape share a column. -/
theorem IsRimHook.mem_succ_rowLen (h : IsRimHook μ ν) (hi : ν.rowLen i < μ.rowLen i)
    (hi' : ν.rowLen (i + 1) < μ.rowLen (i + 1)) :
    (i + 1, ν.rowLen i) ∈ μ ∧ (i + 1, ν.rowLen i) ∉ ν := by
  have hstep := h.rowLen_succ i hi hi'
  have := ν.rowLen_anti i (i + 1) (Nat.le_succ i)
  simp only [mem_iff_lt_rowLen]
  omega

/-- The two geometric conditions characterize rim hooks: a nonempty skew shape `μ / ν` whose rows
form an interval, which contains no `2 × 2` block and whose consecutive rows overlap, is a rim
hook.  This is the converse of `YoungDiagram.IsRimHook.mem_succ_succ_of_notMem` and
`YoungDiagram.IsRimHook.mem_succ_rowLen`. -/
theorem isRimHook_of_forall (hle : ν ≤ μ) (hne : ν ≠ μ)
    (hoc : {i | ν.rowLen i < μ.rowLen i}.OrdConnected)
    (hblock : ∀ i j, (i, j) ∈ μ → (i, j) ∉ ν → (i + 1, j + 1) ∈ μ → (i + 1, j + 1) ∈ ν)
    (hconn : ∀ i, ν.rowLen i < μ.rowLen i → ν.rowLen (i + 1) < μ.rowLen (i + 1) →
      (i + 1, ν.rowLen i) ∈ μ) :
    IsRimHook μ ν where
  le := hle
  ne := hne
  ordConnected := hoc
  rowLen_succ := fun i hi hi' => by
    have hover := mem_iff_lt_rowLen.mp (hconn i hi hi')
    have hanti := ν.rowLen_anti i (i + 1) (Nat.le_succ i)
    by_contra hne'
    have hmem : ((i, ν.rowLen i) : ℕ × ℕ) ∈ μ := mem_iff_lt_rowLen.mpr hi
    have hnotmem : ((i, ν.rowLen i) : ℕ × ℕ) ∉ ν := by
      rw [mem_iff_lt_rowLen]; omega
    have hdiag : ((i + 1, ν.rowLen i + 1) : ℕ × ℕ) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
    have := mem_iff_lt_rowLen.mp (hblock i _ hmem hnotmem hdiag)
    omega

/-! ### The rows a rim hook meets -/

/-- The rows met by the skew shape `μ / ν`: the rows in which `ν` is strictly shorter than `μ`. -/
def rimHookRows (μ ν : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0)).filter fun i => ν.rowLen i < μ.rowLen i

@[simp]
theorem mem_rimHookRows : i ∈ μ.rimHookRows ν ↔ ν.rowLen i < μ.rowLen i := by
  simp only [rimHookRows, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hi
  exact absurd (rowLen_eq_zero_of_colLen_le (Nat.not_lt.mp hi)) (by omega)

/-- Outside the rows it meets, the skew shape `μ / ν` is empty, so `ν` and `μ` agree there. -/
theorem rowLen_eq_of_notMem_rimHookRows (hle : ν ≤ μ) (hi : i ∉ μ.rimHookRows ν) :
    ν.rowLen i = μ.rowLen i :=
  le_antisymm (rowLen_le_of_le hle i) (Nat.not_lt.mp (mt mem_rimHookRows.mpr hi))

/-- One less than the number of rows the skew shape `μ / ν` meets.  For a rim hook this is its
**height**, the sign exponent in the Murnaghan--Nakayama rule. -/
def rimHookHeight (μ ν : YoungDiagram) : ℕ := (μ.rimHookRows ν).card - 1

/-- The height of a rim hook occupying the rows `a ≤ i ≤ b` is `b - a`. -/
theorem rimHookHeight_eq_sub (hab : μ.rimHookRows ν = Finset.Icc a b) :
    μ.rimHookHeight ν = b - a := by
  rw [rimHookHeight, hab, Nat.card_Icc]
  omega

namespace IsRimHook

/-- A rim hook meets at least one row. -/
theorem rimHookRows_nonempty (h : IsRimHook μ ν) : (μ.rimHookRows ν).Nonempty := by
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty] at hc
  refine h.ne (rowLen_injective (funext fun i => ?_))
  exact rowLen_eq_of_notMem_rimHookRows h.le (by rw [hc]; simp)

/-- **A rim hook meets a contiguous block of rows.** -/
theorem exists_rimHookRows_eq_Icc (h : IsRimHook μ ν) :
    ∃ a b, a ≤ b ∧ μ.rimHookRows ν = Finset.Icc a b := by
  have hne := h.rimHookRows_nonempty
  refine ⟨(μ.rimHookRows ν).min' hne, (μ.rimHookRows ν).max' hne,
    Finset.min'_le _ _ ((μ.rimHookRows ν).max'_mem hne), ?_⟩
  ext i
  refine ⟨fun hi => Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hi, Finset.le_max' _ _ hi⟩,
    fun hi => mem_rimHookRows.mpr ?_⟩
  exact h.ordConnected.out' (mem_rimHookRows.mp ((μ.rimHookRows ν).min'_mem hne))
    (mem_rimHookRows.mp ((μ.rimHookRows ν).max'_mem hne)) (Finset.mem_Icc.mp hi)

/-- The block of rows a rim hook meets is a nonempty interval. -/
theorem le_of_rimHookRows_eq_Icc (h : IsRimHook μ ν) (hab : μ.rimHookRows ν = Finset.Icc a b) :
    a ≤ b := by
  obtain ⟨i, hi⟩ := h.rimHookRows_nonempty
  rw [hab, Finset.mem_Icc] at hi
  omega

end IsRimHook

/-- Every row of the block a rim hook meets really is met by it. -/
theorem rowLen_lt_of_rimHookRows_eq_Icc (hab : μ.rimHookRows ν = Finset.Icc a b)
    (hai : a ≤ i) (hib : i ≤ b) : ν.rowLen i < μ.rowLen i :=
  mem_rimHookRows.mp (by rw [hab]; exact Finset.mem_Icc.mpr ⟨hai, hib⟩)

/-! ### The number of cells of a rim hook -/

/-- The telescoping computation behind `YoungDiagram.IsRimHook.card_add_rowLen`, isolated from
Young diagrams: if `f (i + 1) = g i + 1` throughout `[a, b)`, then the sums of `f` and of `g` over
`[a, b]` differ by `f a - g b` plus `b - a`.  Both sides are written additively, so that no
truncated subtraction appears. -/
private theorem sum_Icc_add_eq (f g : ℕ → ℕ) (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b → f (i + 1) = g i + 1) :
    (∑ i ∈ Finset.Icc a b, f i) + g b + a = (∑ i ∈ Finset.Icc a b, g i) + f a + b := by
  suffices H : ∀ n, (∀ i, a ≤ i → i < a + n → f (i + 1) = g i + 1) →
      (∑ i ∈ Finset.Icc a (a + n), f i) + g (a + n) + a
        = (∑ i ∈ Finset.Icc a (a + n), g i) + f a + (a + n) by
    obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
    exact H n hstep
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton]
    omega
  | succ n ih =>
    intro hstep
    have hrw : a + (n + 1) = a + n + 1 := by omega
    rw [hrw, Finset.sum_Icc_succ_top (by omega : a ≤ a + n + 1),
      Finset.sum_Icc_succ_top (by omega : a ≤ a + n + 1)]
    have hstep' := hstep (a + n) (by omega) (by omega)
    have hih := ih fun i hi hib => hstep i hi (by omega)
    omega

namespace IsRimHook

/-- **The number of cells of a rim hook.**  A rim hook meeting the rows `a ≤ i ≤ b` has
`(μ.rowLen a - ν.rowLen b) + (b - a)` cells: the rows contribute the drop in row length from the
top row of the hook to its bottom row, plus one extra cell for each step down.  The statement is
additive, so that no truncated subtraction appears. -/
theorem card_add_rowLen (h : IsRimHook μ ν) (hab : μ.rimHookRows ν = Finset.Icc a b) :
    μ.card + ν.rowLen b + a = ν.card + μ.rowLen a + b := by
  have hle := h.le_of_rimHookRows_eq_Icc hab
  have hb := rowLen_lt_of_rimHookRows_eq_Icc hab hle le_rfl
  have hbcol : b < μ.colLen 0 := by
    by_contra hb'
    exact absurd (rowLen_eq_zero_of_colLen_le (Nat.not_lt.mp hb')) (by omega)
  obtain ⟨N, hμN, hνN⟩ : ∃ N, μ.colLen 0 ≤ N ∧ ν.colLen 0 ≤ N :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hsub : Finset.Icc a b ⊆ Finset.range N := fun i hi =>
    Finset.mem_range.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 (lt_of_lt_of_le hbcol hμN))
  have hμcard : μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := card_eq_sum_range_rowLen μ hμN
  have hνcard : ν.card = ∑ i ∈ Finset.range N, ν.rowLen i := card_eq_sum_range_rowLen ν hνN
  have hμsplit := Finset.sum_sdiff (f := μ.rowLen) hsub
  have hνsplit := Finset.sum_sdiff (f := ν.rowLen) hsub
  have houter : ∑ i ∈ Finset.range N \ Finset.Icc a b, μ.rowLen i
      = ∑ i ∈ Finset.range N \ Finset.Icc a b, ν.rowLen i :=
    Finset.sum_congr rfl fun i hi =>
      (rowLen_eq_of_notMem_rimHookRows h.le (by rw [hab]; exact (Finset.mem_sdiff.mp hi).2)).symm
  have hkey := sum_Icc_add_eq μ.rowLen ν.rowLen hle fun i hai hib =>
    h.rowLen_succ i (rowLen_lt_of_rimHookRows_eq_Icc hab hai (by omega))
      (rowLen_lt_of_rimHookRows_eq_Icc hab (by omega) (by omega))
  omega

/-- The height of a rim hook is smaller than its number of cells: a rim hook with `s` cells meets
at most `s` rows. -/
theorem card_add_rimHookHeight_lt (h : IsRimHook μ ν) : ν.card + μ.rimHookHeight ν < μ.card := by
  obtain ⟨a, b, hle, hab⟩ := h.exists_rimHookRows_eq_Icc
  have hcard := h.card_add_rowLen hab
  have hb := rowLen_lt_of_rimHookRows_eq_Icc hab hle le_rfl
  have hanti := μ.rowLen_anti a b hle
  rw [rimHookHeight_eq_sub hab]
  omega

end IsRimHook

/-! ### Rim hooks with one cell are the erasures of corners -/

/-- Erasing a corner of `μ` leaves a rim hook.  This is the nontrivial witness that
`YoungDiagram.IsRimHook` is satisfiable, and the size-one case of the Murnaghan--Nakayama
recursion. -/
theorem IsCorner.isRimHook_erase (hc : IsCorner μ c) : IsRimHook μ (erase μ c) := by
  have hpos : 0 < μ.rowLen c.1 := by rw [hc.rowLen_eq_snd_add_one]; omega
  -- Erasing a corner shortens its own row and no other, so the skew shape is the single cell `c`.
  have hmem : ∀ k, (erase μ c).rowLen k < μ.rowLen k → k = c.1 := fun k hk => by
    rw [hc.rowLen_erase] at hk
    split at hk
    · next hck => exact hck.symm
    · omega
  have hc1 : (erase μ c).rowLen c.1 < μ.rowLen c.1 := by
    rw [hc.rowLen_erase]
    split
    · omega
    · next hck => exact absurd rfl hck
  refine ⟨erase_le μ c, fun heq => ?_, ⟨fun x hx y hy z hz => ?_⟩, fun i hi hi' => ?_⟩
  · have hcard := hc.card_erase
    rw [heq] at hcard
    omega
  · have hxc := hmem x hx
    have hyc := hmem y hy
    obtain ⟨hxz, hzy⟩ := Set.mem_Icc.mp hz
    -- Both endpoints are the corner's row, so the row `z` between them is that row too.
    have hzc : z = c.1 := by omega
    subst hzc
    exact hc1
  · have h1 := hmem i hi
    have h2 := hmem (i + 1) hi'
    omega

/-- Conversely, a rim hook with a single cell is the erasure of a corner. -/
theorem IsRimHook.exists_isCorner_of_card_succ (h : IsRimHook μ ν) (hcard : ν.card + 1 = μ.card) :
    ∃ c, IsCorner μ c ∧ ν = erase μ c := by
  obtain ⟨a, b, hle, hab⟩ := h.exists_rimHookRows_eq_Icc
  have hcard' := h.card_add_rowLen hab
  have hb := rowLen_lt_of_rimHookRows_eq_Icc hab hle le_rfl
  have hanti := μ.rowLen_anti a b hle
  have hba : a = b := by omega
  subst hba
  have hstep : μ.rowLen a = ν.rowLen a + 1 := by omega
  have hnext : ν.rowLen (a + 1) = μ.rowLen (a + 1) :=
    rowLen_eq_of_notMem_rimHookRows h.le (by
      rw [hab]; simp only [Finset.mem_Icc, not_and, not_le]; omega)
  have hnextle := ν.rowLen_anti a (a + 1) (Nat.le_succ a)
  have hcorner : IsCorner μ (a, μ.rowLen a - 1) := by
    refine (isCorner_def μ _).mpr ⟨mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
    · simp only [mem_iff_lt_rowLen]; omega
    · simp only [mem_iff_lt_rowLen]; omega
  refine ⟨_, hcorner, rowLen_injective (funext fun i => ?_)⟩
  rw [hcorner.rowLen_erase]
  split
  · next hai =>
    have hai' : a = i := hai
    subst hai'
    omega
  · next hai =>
    have hai' : a ≠ i := hai
    exact rowLen_eq_of_notMem_rimHookRows h.le
      (by rw [hab]; simp only [Finset.mem_Icc, not_and, not_le]; omega)

/-! ### Removing a rim hook moves one beta-number -/

/-- Outside the rows the skew shape `μ / ν` meets, the beta-numbers are unchanged. -/
theorem betaNumber_eq_of_notMem_rimHookRows (hle : ν ≤ μ) (hi : i ∉ μ.rimHookRows ν) :
    ν.betaNumber r i = μ.betaNumber r i := by
  rw [betaNumber_def, betaNumber_def, rowLen_eq_of_notMem_rimHookRows hle hi]

namespace IsRimHook

/-- Inside the block of rows a rim hook meets, and above its bottom row, the beta-numbers of `ν`
are those of `μ` shifted up by one index: the moving bead has vacated position `a`, and the beads
it passes keep their values. -/
theorem betaNumber_eq_betaNumber_succ (h : IsRimHook μ ν)
    (hab : μ.rimHookRows ν = Finset.Icc a b) (hai : a ≤ i) (hib : i < b) (hbr : b < r) :
    ν.betaNumber r i = μ.betaNumber r (i + 1) := by
  have hstep := h.rowLen_succ i (rowLen_lt_of_rimHookRows_eq_Icc hab hai (by omega))
    (rowLen_lt_of_rimHookRows_eq_Icc hab (by omega) (by omega))
  rw [betaNumber_def, betaNumber_def, hstep]
  omega

/-- **Removing a rim hook lowers one beta-number by the number of cells removed.**  The bead at
position `a` moves down `μ.card - ν.card` places, landing at position `b`.  The statement is
additive, so that no truncated subtraction appears. -/
theorem card_add_betaNumber (h : IsRimHook μ ν) (hab : μ.rimHookRows ν = Finset.Icc a b)
    (hbr : b < r) : ν.card + μ.betaNumber r a = μ.card + ν.betaNumber r b := by
  have hle := h.le_of_rimHookRows_eq_Icc hab
  have hcard := h.card_add_rowLen hab
  rw [betaNumber_def, betaNumber_def]
  omega

/-- **The height of a rim hook counts the beads the moving bead jumps over.**  The beta-numbers of
`μ` lying strictly between the new value `ν.betaNumber r b` and the old value `μ.betaNumber r a`
are exactly those of the rows `a < i ≤ b`, so there are `μ.rimHookHeight ν` of them. -/
theorem card_filter_betaNumber (h : IsRimHook μ ν) (hab : μ.rimHookRows ν = Finset.Icc a b)
    (hbr : b < r) :
    ((Finset.range r).filter fun i => ν.betaNumber r b < μ.betaNumber r i ∧
        μ.betaNumber r i < μ.betaNumber r a).card = μ.rimHookHeight ν := by
  have hle := h.le_of_rimHookRows_eq_Icc hab
  have har : a < r := by omega
  have hb := rowLen_lt_of_rimHookRows_eq_Icc hab hle le_rfl
  have hbeta : ν.betaNumber r b < μ.betaNumber r b := by
    rw [betaNumber_def, betaNumber_def]; omega
  have hfilter : ((Finset.range r).filter fun i => ν.betaNumber r b < μ.betaNumber r i ∧
      μ.betaNumber r i < μ.betaNumber r a) = Finset.Icc (a + 1) b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hir, hlow, hhigh⟩
      refine ⟨?_, ?_⟩
      · rcases Nat.lt_or_ge a i with h1 | h1
        · omega
        · exfalso
          rcases eq_or_lt_of_le h1 with rfl | h2
          · omega
          · have := μ.betaNumber_lt_betaNumber h2 har
            omega
      · by_contra hib'
        have hib : b < i := Nat.not_le.mp hib'
        have hνi : ν.betaNumber r i = μ.betaNumber r i :=
          betaNumber_eq_of_notMem_rimHookRows h.le
            (by rw [hab]; simp only [Finset.mem_Icc, not_and, not_le]; omega)
        have := ν.betaNumber_lt_betaNumber hib hir
        omega
    · rintro ⟨hai, hib⟩
      refine ⟨by omega, ?_, μ.betaNumber_lt_betaNumber (by omega) (by omega)⟩
      rcases eq_or_lt_of_le hib with rfl | hlt
      · exact hbeta
      · exact hbeta.trans (μ.betaNumber_lt_betaNumber hlt (by omega))
  rw [hfilter, Nat.card_Icc, rimHookHeight_eq_sub hab]
  omega

end IsRimHook

/-! ### Adding a rim hook moves one bead up -/

namespace IsRimHook

/-- **Adding a rim hook, read on all the beta-numbers at once.**  Let `μ / ν` be a rim hook
meeting the rows `a ≤ i ≤ b`.  Raising the beta-number of `ν` at the bottom row `b` by the number
of cells of the hook gives the beta-numbers of `μ`, rearranged by the cycle
`a ↦ a + 1 ↦ ⋯ ↦ b ↦ a` of the rows the hook meets.  That cycle has sign `(-1) ^ (b - a)`, the
sign of the height of the hook (`Fin.sign_cycleIcc_of_le`). -/
theorem update_betaNumber_eq_comp_cycleIcc (h : IsRimHook μ ν)
    (hab : μ.rimHookRows ν = Finset.Icc a b) (hbr : b < r) :
    Function.update (fun i : Fin r => ν.betaNumber r i) ⟨b, hbr⟩
        (ν.betaNumber r b + (μ.card - ν.card)) =
      (fun i : Fin r => μ.betaNumber r i) ∘
        Fin.cycleIcc ⟨a, (h.le_of_rimHookRows_eq_Icc hab).trans_lt hbr⟩ ⟨b, hbr⟩ := by
  have hle := h.le_of_rimHookRows_eq_Icc hab
  have hcard := h.card_add_betaNumber hab hbr
  have hlt := h.card_lt
  have : NeZero r := ⟨by omega⟩
  funext ⟨i, hi⟩
  have hout : i < a ∨ b < i → ν.betaNumber r i = μ.betaNumber r i := fun hi' =>
    betaNumber_eq_of_notMem_rimHookRows h.le (by rw [hab]; simp only [Finset.mem_Icc]; omega)
  simp only [Function.comp_apply]
  rcases lt_or_ge i a with hia | hai
  · rw [Fin.cycleIcc_of_lt (Fin.mk_lt_mk.mpr hia),
      Function.update_of_ne (by simp only [ne_eq, Fin.mk.injEq]; omega)]
    exact hout (Or.inl hia)
  rcases lt_trichotomy i b with hib | rfl | hbi
  · rw [Fin.cycleIcc_of_ge_of_lt (Fin.mk_le_mk.mpr hai) (Fin.mk_lt_mk.mpr hib),
      Function.update_of_ne (by simp only [ne_eq, Fin.mk.injEq]; omega), Fin.val_add,
      Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega : i + 1 < r)]
    exact h.betaNumber_eq_betaNumber_succ hab hai hib hbr
  · rw [Fin.cycleIcc_of_last (Fin.mk_le_mk.mpr hle), Function.update_self]
    dsimp only
    omega
  · rw [Fin.cycleIcc_of_gt (Fin.mk_lt_mk.mpr hbi),
      Function.update_of_ne (by simp only [ne_eq, Fin.mk.injEq]; omega)]
    exact hout (Or.inr hbi)

/-- The bottom row of a rim hook lies above the first empty row of the larger diagram. -/
theorem lt_colLen_of_rimHookRows_eq_Icc (h : IsRimHook μ ν)
    (hab : μ.rimHookRows ν = Finset.Icc a b) : b < μ.colLen 0 := by
  have hb := rowLen_lt_of_rimHookRows_eq_Icc hab (h.le_of_rimHookRows_eq_Icc hab) le_rfl
  by_contra hb'
  rw [rowLen_eq_zero_of_colLen_le (Nat.not_lt.mp hb')] at hb
  omega

/-- **A rim hook is determined by its size and its bottom row.**  Two rim hooks `μ₁ / ν` and
`μ₂ / ν` with the same number of cells and the same bottom row have the same larger diagram: by
`YoungDiagram.IsRimHook.update_betaNumber_eq_comp_cycleIcc` the beta-numbers of `μ₁` and of `μ₂`
are rearrangements of the same family, and a strictly decreasing family is determined by its set
of values. -/
theorem eq_of_card_eq_of_rimHookRows_eq_Icc {μ₁ μ₂ : YoungDiagram} {a₁ a₂ : ℕ} (h₁ : IsRimHook μ₁ ν)
    (h₂ : IsRimHook μ₂ ν) (hcard : μ₁.card = μ₂.card)
    (hab₁ : μ₁.rimHookRows ν = Finset.Icc a₁ b) (hab₂ : μ₂.rimHookRows ν = Finset.Icc a₂ b) :
    μ₁ = μ₂ := by
  set r := max (μ₁.colLen 0) (μ₂.colLen 0)
  have hbr : b < r := (h₁.lt_colLen_of_rimHookRows_eq_Icc hab₁).trans_le (le_max_left _ _)
  have hu := (h₁.update_betaNumber_eq_comp_cycleIcc hab₁ hbr).symm.trans
    (hcard ▸ h₂.update_betaNumber_eq_comp_cycleIcc hab₂ hbr)
  have hanti : ∀ μ : YoungDiagram, StrictAnti fun i : Fin r => μ.betaNumber r i :=
    fun μ _ _ hij => μ.betaNumber_lt_betaNumber hij (Fin.is_lt _)
  have hrange := congrArg Set.range hu
  rw [EquivLike.range_comp, EquivLike.range_comp,
    (hanti μ₁).range_inj_of_wellFoundedGT (hanti μ₂)] at hrange
  exact eq_of_betaNumber_eq (le_max_left _ _) (le_max_right _ _)
    fun i hi => congrFun hrange ⟨i, hi⟩

/-- **The bead moved by a rim hook lands on a free position**: raising the beta-number of `ν` at
the bottom row of a rim hook `μ / ν` by the number of cells of the hook gives a value that is not
a beta-number of `ν`.  This is the converse of
`YoungDiagram.exists_isRimHook_rimHookRows_eq_Icc`. -/
theorem betaNumber_ne_betaNumber_add (h : IsRimHook μ ν)
    (hab : μ.rimHookRows ν = Finset.Icc a b) (hir : i < r) (hbr : b < r) :
    ν.betaNumber r i ≠ ν.betaNumber r b + (μ.card - ν.card) := by
  intro hi
  have hlt := h.card_lt
  have hib : i ≠ b := by
    rintro rfl
    omega
  -- The raised family is a rearrangement of the beta-numbers of `μ`, hence injective.
  have hinj : Function.Injective (Function.update (fun i : Fin r => ν.betaNumber r i) ⟨b, hbr⟩
      (ν.betaNumber r b + (μ.card - ν.card))) := by
    have hμ : Function.Injective fun i : Fin r => μ.betaNumber r i :=
      fun _ _ hkl => Fin.ext (μ.injOn_betaNumber r (Fin.is_lt _) (Fin.is_lt _) hkl)
    rw [h.update_betaNumber_eq_comp_cycleIcc hab hbr]
    exact hμ.comp (Equiv.injective _)
  have := @hinj ⟨i, hir⟩ ⟨b, hbr⟩ (by
    rw [Function.update_of_ne (by simpa [Fin.ext_iff] using hib), Function.update_self, ← hi])
  exact hib (Fin.mk.inj_iff.mp this)

end IsRimHook

/-- **Adding a rim hook moves one bead up.**  Let `ν` have at most `r` rows, and suppose that
raising its beta-number at the row `j < r` by `s` produces a value that is not already a
beta-number of `ν` (which forces `s > 0`).  Then there is a rim hook `μ / ν` with `s` cells whose
bottom row is `j`, and `μ` still has at most `r` rows.  This is the converse of
`YoungDiagram.IsRimHook.card_add_betaNumber`: the moved bead lands at the first row `a` whose
beta-number falls below the new value, and the rows `a < i ≤ j` are the beads it jumps over. -/
theorem exists_isRimHook_rimHookRows_eq_Icc {s : ℕ} (hν : ν.colLen 0 ≤ r) (hjr : j < r)
    (hfree : ∀ i < r, ν.betaNumber r i ≠ ν.betaNumber r j + s) :
    ∃ μ, IsRimHook μ ν ∧ μ.colLen 0 ≤ r ∧ μ.card = ν.card + s ∧
      ∃ a, μ.rimHookRows ν = Finset.Icc a j := by
  classical
  have hs : 0 < s :=
    Nat.pos_of_ne_zero fun hs => hfree j hjr (by rw [hs, Nat.add_zero])
  set v := ν.betaNumber r j + s with hv
  have hex : ∃ i, ν.betaNumber r i < v := ⟨j, by omega⟩
  -- The moved bead lands at the first row `a` whose beta-number is smaller than `v`.
  set a := Nat.find hex with ha
  have hav : ν.betaNumber r a < v := Nat.find_spec hex
  have haj : a ≤ j := Nat.find_min' hex (by omega)
  have hbefore : ∀ i < a, v < ν.betaNumber r i := fun i hi =>
    lt_of_le_of_ne (Nat.not_lt.mp (Nat.find_min hex hi)) fun hi' => hfree i (by omega) hi'.symm
  simp only [betaNumber_def] at hav hbefore
  -- The row lengths of the enlarged diagram.
  set g : ℕ → ℕ := fun i => if i < a then ν.rowLen i else if i = a then v - (r - 1 - a)
    else if i ≤ j then ν.rowLen (i - 1) + 1 else ν.rowLen i with hg
  have hg_lt : ∀ i < a, g i = ν.rowLen i := fun i hi => by simp [hg, hi]
  have hg_a : g a = v - (r - 1 - a) := by simp [hg]
  have hg_mid : ∀ i, a < i → i ≤ j → g i = ν.rowLen (i - 1) + 1 := fun i hai hij => by
    have hnotlt : ¬ i < a := by omega
    have hne : i ≠ a := by omega
    simp [hg, hij, hnotlt, hne]
  have hg_gt : ∀ i, j < i → g i = ν.rowLen i := fun i hji => by
    have hnotlt : ¬ i < a := by omega
    have hne : i ≠ a := by omega
    have hnotle : ¬ i ≤ j := by omega
    simp [hg, hnotlt, hne, hnotle]
  have hanti : ∀ {i i'}, i ≤ i' → ν.rowLen i' ≤ ν.rowLen i := fun h => ν.rowLen_anti _ _ h
  -- Row by row, `g` agrees with `ν` outside `[a, j]` and exceeds it inside.
  have hrows : ∀ i, (ν.rowLen i < g i ↔ a ≤ i ∧ i ≤ j) ∧ ν.rowLen i ≤ g i := fun i => by
    rcases lt_trichotomy i a with hia | rfl | hai
    · rw [hg_lt i hia]
      omega
    · rw [hg_a]
      omega
    rcases le_or_gt i j with hij | hji
    · have := hanti (Nat.sub_le i 1)
      rw [hg_mid i hai hij]
      omega
    · rw [hg_gt i hji]
      omega
  have hgmono : Antitone g := antitone_nat_of_succ_le fun i => by
    have h1 := hanti (Nat.le_succ i)
    rcases lt_trichotomy (i + 1) a with hia | hia | hia
    · rw [hg_lt _ hia, hg_lt i (by omega)]
      exact h1
    · have := hbefore i (by omega)
      rw [hia, hg_a, hg_lt i (by omega)]
      omega
    rcases le_or_gt (i + 1) j with hij | hji
    · rw [hg_mid _ hia hij, Nat.add_sub_cancel]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hia) with rfl | hai
      · rw [hg_a]
        omega
      · rw [hg_mid i hai (by omega)]
        have := hanti (Nat.sub_le i 1)
        omega
    · rw [hg_gt _ hji]
      exact h1.trans (hrows i).2
  set μ := ofRowLensFin (fun i : Fin r => g i) fun _ _ h => hgmono h
  have hμ : ∀ i, μ.rowLen i = g i := fun i => by
    by_cases hi : i < r
    · exact rowLen_ofRowLensFin _ _ ⟨i, hi⟩
    · have hzero : μ.rowLen i = 0 :=
        rowLen_ofRowLensFin_eq_zero_of_le _ _ (Nat.not_lt.mp hi)
      rw [hzero, hg_gt i (by omega)]
      exact (rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))).symm
  have hμrows : μ.rimHookRows ν = Finset.Icc a j := by
    ext i
    rw [mem_rimHookRows, hμ, (hrows i).1, Finset.mem_Icc]
  have hrim : IsRimHook μ ν :=
    { le := le_of_forall_rowLen_le fun i => (hμ i).symm ▸ (hrows i).2
      ne := fun h => by
        have := (hrows a).1.mpr ⟨le_rfl, haj⟩
        rw [← hμ, ← h] at this
        exact lt_irrefl _ this
      ordConnected := by
        have hset : {i | ν.rowLen i < μ.rowLen i} = Set.Icc a j := by
          ext i
          simp only [Set.mem_ofPred_eq, hμ, (hrows _).1, Set.mem_Icc]
        rw [hset]
        exact Set.ordConnected_Icc
      rowLen_succ := fun i hi hi' => by
        rw [hμ, (hrows _).1] at hi hi'
        rw [hμ, hg_mid _ (by omega) hi'.2, Nat.add_sub_cancel] }
  refine ⟨μ, hrim, colLen_zero_ofRowLensFin_le _ _, ?_, a, hμrows⟩
  have hcard := hrim.card_add_betaNumber hμrows hjr
  rw [betaNumber_def, hμ, hg_a] at hcard
  omega

end YoungDiagram
