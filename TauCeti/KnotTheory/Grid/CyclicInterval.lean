/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Circular.ZMod
public import Mathlib.Order.Interval.Finset.Fin
public import TauCeti.Data.Fin.Basic

/-!
# Complementary cyclic intervals in finite grids

This file records finite-set bookkeeping for the clockwise cyclic intervals used by toroidal
grid rectangles. For distinct endpoints `a` and `b`, the two open arcs `cIoo a b` and `cIoo b a`
are disjoint and together contain exactly the points other than `a` and `b`. The half-open arc
`cIco a b` restores the initial endpoint, except in the degenerate case, and indexes the columns
or rows of squares covered by a rectangle.

These lemmas are deliberately stated at the one-dimensional `Fin n` level. Rectangle-pair
arguments for the grid differential can then apply them independently in the column and row
directions before taking products.

## Main definitions

* `TauCeti.Grid.cIco`: the clockwise half-open arc, the one-dimensional shape of the squares a
  toroidal rectangle covers.
* `TauCeti.Grid.cyclicPosition`: the position of a point on the cycle read clockwise from the
  successor of a basepoint.

## Main results

* `TauCeti.Grid.disjoint_cIoo_swap`: opposite open arcs are disjoint.
* `TauCeti.Grid.mem_cIoo_or_mem_cIoo_swap_iff`: a point lies in one opposite arc exactly when
  it is not an endpoint.
* `TauCeti.Grid.cIoo_union_swap`: the two opposite arcs cover the endpoint complement.
* `TauCeti.Grid.mem_cIoo_cyclic_left`, `TauCeti.Grid.mem_cIoo_cyclic_right`: the two rotations
  of a cyclic order of three points.
* `TauCeti.Grid.mem_cIoo_swap_of_notMem`: a point off both endpoints that misses one arc lies on
  the opposite arc.
* `TauCeti.Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap`: if `a` and `b` lie on opposite arcs from
  `c` to `d`, then `d` lies on the clockwise arc from `a` to `b`.
* `TauCeti.Grid.mem_cIoo_and_mem_cIoo_swap_of_notMem`: cyclic separation is symmetric, so `c` and
  `d` then lie on the two opposite arcs between `a` and `b`.
* `TauCeti.Grid.card_cIoo_add_card_cIoo_swap`: the two arc lengths add to `n - 2`.
* `TauCeti.Grid.cIoo_image_rev`: reversing a clockwise open arc by `Fin.rev` gives the clockwise
  open arc with reversed, exchanged endpoints.
* `TauCeti.Grid.mem_cIoo_finRotate_finRotate`, `TauCeti.Grid.mem_cIco_finRotate_finRotate`: the
  cyclic permutation `finRotate n` preserves the open and half-open arcs, as do its powers
  (`TauCeti.Grid.mem_cIoo_finRotate_pow_finRotate_pow`,
  `TauCeti.Grid.mem_cIco_finRotate_pow_finRotate_pow`).
* `TauCeti.Grid.mem_cIoo_finRotate_rev`, `TauCeti.Grid.rev_mem_cIco_finRotate_rev`: the half-turn
  `x ↦ finRotate n x.rev` of the grid points reverses the open arcs of points, and acts on the
  half-open arcs of squares as `Fin.rev`.
* `TauCeti.Grid.finRotate_ne_self`: on a cycle of length at least two, the cyclic successor has
  no fixed point.
* `TauCeti.Grid.cIoo_finRotate_eq_empty`, `TauCeti.Grid.cIco_eq_singleton_iff`: the arcs from a
  point to its cyclic successor are empty and a single point, and these are the only one-point
  half-open arcs.
* `TauCeti.Grid.mem_cIco`: membership in the clockwise half-open arc.
* `TauCeti.Grid.card_cIco`: the length of a half-open arc in standard representatives.
* `TauCeti.Grid.cIco_union_swap`: opposite nondegenerate half-open arcs partition the grid.
* `TauCeti.Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo`: an interior point cuts a half-open arc
  into two adjacent half-open arcs.
* `TauCeti.Grid.disjoint_cIco_cIco_of_mem_cIoo`: the two pieces of such a cut are disjoint.
* `TauCeti.Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo`: an interior point cuts an open arc
  into two open arcs and the cutting point itself.
* `TauCeti.Grid.cIoo_subset_cIoo_right_of_mem_cIoo`,
  `TauCeti.Grid.cIoo_subset_cIoo_left_of_mem_cIoo`: the two pieces of that cut are contained in
  the arc they cut.
* `TauCeti.Grid.Noninterleaving`: two endpoint pairs lie on the same cyclic side of each other.
* `TauCeti.Grid.noninterleaving_rev`: non-interleaving is preserved by reversing every endpoint
  with `Fin.rev`, exchanging the two endpoints within each pair.
* `TauCeti.Grid.noninterleaving_of_eq_finRotate`, `TauCeti.Grid.noninterleaving_of_finRotate_eq`:
  an endpoint pair of two cyclically adjacent points is non-interleaving with every endpoint pair
  that avoids its endpoints suitably, using `TauCeti.Grid.finRotate_mem_cIoo_iff` (stepping to the
  cyclic successor stays on the same side of an arc) and `TauCeti.Grid.mem_cIoo_finRotate_left_iff`
  (the arc from the successor of `a` back to `a` misses only these two points).
* `TauCeti.Grid.mem_cIoo_succAbove_succAbove`,
  `TauCeti.Grid.mem_cIco_succAbove_succAbove`: inserting a point into the cycle with
  `Fin.succAbove` preserves the arcs between old points, and
  `TauCeti.Grid.mem_cIoo_succ_succAbove_succ_succAbove_iff` locates the inserted point.
* `TauCeti.Grid.mem_cIco_succ_succAbove_succ_succAbove_iff`: after inserting a point immediately
  after `i`, a half-open arc between old points is the preimage of the old arc under the collapse
  `Fin.predAbove i`.
* `TauCeti.Grid.cIco_subset_of_mem_cIoo`: a half-open arc starting strictly inside another is
  contained in it.
* `TauCeti.Grid.mem_cIco_of_mem_cIco_of_mem_cIoo`: the membership form of that nesting.
* `TauCeti.Grid.notMem_cIco_finRotate_left`: a point is never in the half-open arc starting at
  its own cyclic successor.
* `TauCeti.Grid.self_mem_cIco_finRotate`: a point always lies in a nondegenerate half-open arc
  ending at its own cyclic successor.
* `TauCeti.Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate`: moving from `p` to `q` enters
  the arc from `finRotate n α` to `finRotate n β` when passing `α` and leaves it when passing
  `β`.
* `TauCeti.Grid.notMem_cIco_of_cIco_union`: a point missing both halves of a half-open arc
  cut at an interior point misses the whole arc.
* `TauCeti.Grid.cyclicPosition_lt_of_notMem_cIco`: two distinct points whose half-open arc
  avoids the basepoint come in increasing order of cyclic position.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.3, "The
complexes and `∂² = 0`", where the annular cases in the juxtaposition proof use the fact that
the two complementary cyclic intervals partition the non-endpoint columns or rows. The
terminology follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace Grid

variable {n : ℕ}

/-- The clockwise open cyclic interval from `a` to `b` in `Fin n`.

If `a < b` in the standard representatives, this is the ordinary open interval
`a < x < b`. If `b ≤ a` and `a ≠ b`, it wraps around `0`, so it is the union of
`a < x` and `x < b`. The interval from a point to itself is empty. -/
noncomputable def cIoo (a b : Fin n) : Finset (Fin n) :=
  ((Set.finite_univ : (Set.univ : Set (Fin n)).Finite).subset
    (Set.subset_univ (Set.cIoo a b : Set (Fin n)))).toFinset

/-- Membership in a clockwise open cyclic interval, unfolded as inequalities between the
standard representatives. -/
@[simp]
theorem mem_cIoo (a b x : Fin n) :
    x ∈ cIoo a b ↔
      a ≠ b ∧
        if a.val < b.val then
          a.val < x.val ∧ x.val < b.val
        else
          a.val < x.val ∨ x.val < b.val := by
  rw [cIoo]
  simp only [Set.Finite.mem_toFinset, Set.mem_cIoo, Fin.sbtw_iff, Fin.lt_def]
  constructor
  · rintro (⟨hax, hxb⟩ | ⟨hxb, hba⟩ | ⟨hba, hax⟩)
    · exact ⟨fun hab => by omega, by simp [hax, hxb]⟩
    · exact ⟨fun hab => by omega, by simp [Nat.not_lt_of_gt hba, hxb]⟩
    · exact ⟨fun hab => by omega, by simp [Nat.not_lt_of_gt hba, hax]⟩
  · intro h
    by_cases hab : a.val < b.val
    · exact Or.inl (by simpa [hab] using h.2)
    · have hba : b.val < a.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
      rcases (by simpa [hab] using h.2) with hax | hxb
      · exact Or.inr (Or.inr ⟨hba, hax⟩)
      · exact Or.inr (Or.inl ⟨hxb, hba⟩)

/-- The open cyclic interval from a point to itself is empty. -/
@[simp]
theorem cIoo_self (a : Fin n) : cIoo a a = ∅ := by
  ext x
  simp

/-- The initial endpoint is not in its open cyclic interval. -/
theorem left_notMem_cIoo (a b : Fin n) : a ∉ cIoo a b := by
  intro ha
  rw [mem_cIoo] at ha
  by_cases hab : a.val < b.val
  · have hinside : a.val < a.val ∧ a.val < b.val := by
      simpa only [hab, ite_true] using ha.2
    exact Nat.lt_irrefl a.val hinside.1
  · have hinside : a.val < a.val ∨ a.val < b.val := by
      simpa only [hab, ite_false] using ha.2
    cases hinside with
    | inl hlt => exact Nat.lt_irrefl a.val hlt
    | inr hlt => exact hab hlt

/-- The terminal endpoint is not in its open cyclic interval. -/
theorem right_notMem_cIoo (a b : Fin n) : b ∉ cIoo a b := by
  intro hb
  rw [mem_cIoo] at hb
  by_cases hab : a.val < b.val
  · have hinside : a.val < b.val ∧ b.val < b.val := by
      simpa only [hab, ite_true] using hb.2
    exact Nat.lt_irrefl b.val hinside.2
  · have hinside : a.val < b.val ∨ b.val < b.val := by
      simpa only [hab, ite_false] using hb.2
    cases hinside with
    | inl hlt => exact hab hlt
    | inr hlt => exact Nat.lt_irrefl b.val hlt

/-- A point in an open cyclic interval differs from its initial endpoint. -/
theorem ne_left_of_mem_cIoo {a b x : Fin n} (h : x ∈ cIoo a b) : x ≠ a := by
  rintro rfl
  exact left_notMem_cIoo _ _ h

/-- A point in an open cyclic interval differs from its terminal endpoint. -/
theorem ne_right_of_mem_cIoo {a b x : Fin n} (h : x ∈ cIoo a b) : x ≠ b := by
  rintro rfl
  exact right_notMem_cIoo _ _ h

/-- The clockwise half-open cyclic interval from `a` to `b` in `Fin n`.

This is the arc that starts at `a` and stops just before `b`, so it is the open arc `cIoo a b`
with its initial endpoint restored, and it is empty when the two endpoints agree. It is the
one-dimensional shape of the set of *squares* a toroidal rectangle covers, whereas `cIoo` is the
shape of the set of grid *points* strictly inside it. Mathlib's circular-order intervals stop at
`Set.cIcc` and `Set.cIoo` precisely because a half-open circular interval cannot be described
without separating the degenerate case, which is why the definition below is by cases. -/
noncomputable def cIco (a b : Fin n) : Finset (Fin n) :=
  if a = b then ∅ else insert a (cIoo a b)

/-- Between distinct endpoints the half-open cyclic interval is the open one with its initial
endpoint restored. -/
theorem cIco_of_ne {a b : Fin n} (h : a ≠ b) : cIco a b = insert a (cIoo a b) := by
  simp only [cIco, h, ite_false]

/-- The half-open cyclic interval from a point to itself is empty. -/
@[simp]
theorem cIco_self (a : Fin n) : cIco a a = ∅ := by
  simp only [cIco, ite_true]

/-- Membership in a clockwise half-open cyclic interval, unfolded as inequalities between the
standard representatives. Only the comparison against the initial endpoint is weakened relative
to `Grid.mem_cIoo`. -/
@[simp]
theorem mem_cIco (a b x : Fin n) :
    x ∈ cIco a b ↔
      a ≠ b ∧
        if a.val < b.val then
          a.val ≤ x.val ∧ x.val < b.val
        else
          a.val ≤ x.val ∨ x.val < b.val := by
  by_cases hab : a = b
  · simp [hab]
  · simp only [cIco_of_ne hab, Finset.mem_insert, mem_cIoo, hab, ne_eq, not_false_eq_true,
      true_and, ← Fin.val_inj]
    split_ifs with h <;> omega

/-- The non-wrapping description of a half-open cyclic interval: when the initial endpoint
precedes the terminal one, the arc is the ordinary half-open interval between them. -/
theorem mem_cIco_iff_of_left_lt_right {a b : Fin n} (h : a.val < b.val) (x : Fin n) :
    x ∈ cIco a b ↔ a.val ≤ x.val ∧ x.val < b.val := by
  rw [mem_cIco]
  have hab : a ≠ b := fun e => by simp [e] at h
  simp [hab, h]

/-- The wrapping description of a half-open cyclic interval: when the terminal endpoint precedes
the initial one, the arc runs off the top and reappears at the bottom. -/
theorem mem_cIco_iff_of_right_lt_left {a b : Fin n} (h : b.val < a.val) (x : Fin n) :
    x ∈ cIco a b ↔ a.val ≤ x.val ∨ x.val < b.val := by
  rw [mem_cIco]
  have hab : a ≠ b := fun e => by simp [e] at h
  simp [hab, Nat.not_lt_of_gt h]

/-- The initial endpoint of a nondegenerate half-open cyclic interval belongs to it. -/
theorem left_mem_cIco {a b : Fin n} (h : a ≠ b) : a ∈ cIco a b := by
  rw [cIco_of_ne h]
  exact Finset.mem_insert_self _ _

/-- The terminal endpoint is not in its half-open cyclic interval. -/
theorem right_notMem_cIco (a b : Fin n) : b ∉ cIco a b := by
  by_cases hab : a = b
  · simp [hab]
  · rw [cIco_of_ne hab, Finset.mem_insert]
    exact fun h => h.elim (fun hba => hab hba.symm) (right_notMem_cIoo a b)

/-- A point of a half-open cyclic interval other than its initial endpoint lies in the open
interval with the same endpoints. -/
theorem mem_cIoo_of_mem_cIco {a b x : Fin n} (h : x ∈ cIco a b) (hx : x ≠ a) : x ∈ cIoo a b := by
  by_cases hab : a = b
  · rw [hab, cIco_self] at h
    exact absurd h (Finset.notMem_empty x)
  · rw [cIco_of_ne hab, Finset.mem_insert] at h
    exact h.resolve_left hx

/-- The open cyclic interval is contained in the half-open one with the same endpoints. -/
theorem cIoo_subset_cIco (a b : Fin n) : cIoo a b ⊆ cIco a b := by
  by_cases hab : a = b
  · simp [hab]
  · rw [cIco_of_ne hab]
    exact Finset.subset_insert _ _

/-- A nondegenerate half-open cyclic interval has one more point than the corresponding open
interval. -/
theorem card_cIco_of_ne {a b : Fin n} (h : a ≠ b) :
    (cIco a b).card = (cIoo a b).card + 1 := by
  rw [cIco_of_ne h, Finset.card_insert_of_notMem (left_notMem_cIoo a b)]

/-- A non-wrapping half-open cyclic interval is the ordinary half-open interval in `Fin n`. -/
theorem cIco_eq_Ico_of_lt {a b : Fin n} (h : a.val < b.val) :
    cIco a b = Finset.Ico a b := by
  ext x
  rw [mem_cIco_iff_of_left_lt_right h]
  simp only [Finset.mem_Ico, Fin.le_def, Fin.lt_def]

/-- A wrapping half-open cyclic interval is the union of the final segment starting at its
initial endpoint and the initial segment ending before its terminal endpoint. -/
theorem cIco_eq_Ici_union_Iio_of_lt {a b : Fin n} (h : b.val < a.val) :
    cIco a b = Finset.Ici a ∪ Finset.Iio b := by
  ext x
  rw [mem_cIco_iff_of_right_lt_left h]
  simp only [Finset.mem_union, Finset.mem_Ici, Finset.mem_Iio, Fin.le_def, Fin.lt_def]

/-- The cardinality of a clockwise half-open cyclic interval, including the degenerate case. -/
@[simp]
theorem card_cIco (a b : Fin n) :
    (cIco a b).card =
      if a = b then 0
      else if a.val < b.val then b.val - a.val else n - a.val + b.val := by
  by_cases hab : a = b
  · simp [hab]
  by_cases hlt : a.val < b.val
  · rw [cIco_eq_Ico_of_lt hlt]
    simp [hab, hlt, Fin.card_Ico]
  · have hgt : b.val < a.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hab (Fin.val_inj.mp h.symm))
    rw [cIco_eq_Ici_union_Iio_of_lt hgt,
      Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]
        intro x hx hxb
        simp only [Finset.mem_Ici, Finset.mem_Iio, Fin.le_def, Fin.lt_def] at hx hxb
        omega)]
    simp [hab, hlt, Fin.card_Ici, Fin.card_Iio]

/-- Opposite half-open cyclic intervals are disjoint. -/
theorem disjoint_cIco_swap (a b : Fin n) : Disjoint (cIco a b) (cIco b a) := by
  rw [Finset.disjoint_left]
  intro x hxab hxba
  rw [mem_cIco] at hxab hxba
  by_cases hab : a.val < b.val
  · have hba : ¬b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
    simp only [hab, hba, ite_true, ite_false] at hxab hxba
    omega
  · have hba : b.val < a.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (fun e => hxab.1 (Fin.val_inj.mp e.symm))
    simp only [hab, hba, ite_true, ite_false] at hxab hxba
    omega

/-- Opposite nondegenerate half-open cyclic intervals partition the grid. -/
@[simp]
theorem cIco_union_swap {a b : Fin n} (h : a ≠ b) :
    cIco a b ∪ cIco b a = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rw [mem_cIco, mem_cIco]
  by_cases hab : a.val < b.val
  · have hba : ¬b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
    simp only [h, h.symm, ne_eq, not_false_eq_true, true_and, hab, hba, ite_true, ite_false]
    omega
  · have hba : b.val < a.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (fun e => h (Fin.val_inj.mp e.symm))
    simp only [h, h.symm, ne_eq, not_false_eq_true, true_and, hab, hba, ite_true, ite_false]
    omega

/-- The cardinalities of opposite nondegenerate half-open cyclic intervals add to the grid
size. -/
theorem card_cIco_add_card_cIco_swap {a b : Fin n} (h : a ≠ b) :
    (cIco a b).card + (cIco b a).card = n := by
  have hcard := congrArg Finset.card (cIco_union_swap h)
  rw [Finset.card_union_of_disjoint (disjoint_cIco_swap a b), Finset.card_univ,
    Fintype.card_fin] at hcard
  exact hcard

/-- Two oriented cyclic intervals have non-interleaving endpoint pairs.

The endpoints `a₀`, `a₁` lie on the same side of the pair `b₀`, `b₁`, and conversely. This
two-sided formulation handles shared-endpoint cases uniformly. -/
@[expose] def Noninterleaving (a₀ a₁ b₀ b₁ : Fin n) : Prop :=
  (a₀ ∈ cIoo b₀ b₁ ↔ a₁ ∈ cIoo b₀ b₁) ∧
    (b₀ ∈ cIoo a₀ a₁ ↔ b₁ ∈ cIoo a₀ a₁)

/-- The defining endpoint-side conditions for `Grid.Noninterleaving`. -/
theorem noninterleaving_iff (a₀ a₁ b₀ b₁ : Fin n) :
    Noninterleaving a₀ a₁ b₀ b₁ ↔
      (a₀ ∈ cIoo b₀ b₁ ↔ a₁ ∈ cIoo b₀ b₁) ∧
        (b₀ ∈ cIoo a₀ a₁ ↔ b₁ ∈ cIoo a₀ a₁) :=
  Iff.rfl

/-- An endpoint pair is non-interleaving with itself. -/
@[simp]
theorem noninterleaving_self (a₀ a₁ : Fin n) : Noninterleaving a₀ a₁ a₀ a₁ := by
  simp [Noninterleaving]

/-- Non-interleaving is symmetric in the two endpoint pairs. -/
theorem noninterleaving_comm {a₀ a₁ b₀ b₁ : Fin n} :
    Noninterleaving a₀ a₁ b₀ b₁ ↔ Noninterleaving b₀ b₁ a₀ a₁ := by
  rw [Noninterleaving, Noninterleaving]
  exact and_comm

/-- A point cannot lie in both open cyclic intervals with the same endpoints but opposite
orientations. -/
private theorem not_mem_cIoo_and_cIoo_swap (a b x : Fin n) :
    ¬(x ∈ cIoo a b ∧ x ∈ cIoo b a) := by
  rw [mem_cIoo, mem_cIoo]
  rintro ⟨hxab, hxba⟩
  by_cases hab : a.val < b.val
  · have hxab' : a.val < x.val ∧ x.val < b.val := by
      simpa [hab] using hxab.2
    have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
    have hxba' : b.val < x.val ∨ x.val < a.val := by
      simpa [hbxa] using hxba.2
    omega
  · have hxab' : a.val < x.val ∨ x.val < b.val := by
      simpa [hab] using hxab.2
    have hba : b.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
    have hxba' : b.val < x.val ∧ x.val < a.val := by
      simpa [hba] using hxba.2
    omega

/-- Opposite open cyclic intervals with the same endpoints are disjoint. -/
theorem disjoint_cIoo_swap (a b : Fin n) : Disjoint (cIoo a b) (cIoo b a) := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy hxy
  subst hxy
  exact not_mem_cIoo_and_cIoo_swap a b x ⟨hx, hy⟩

/-- Membership in one of the two opposite cyclic intervals is the same as being neither
endpoint. -/
theorem mem_cIoo_or_mem_cIoo_swap_iff {a b x : Fin n} (h : a ≠ b) :
    x ∈ cIoo a b ∨ x ∈ cIoo b a ↔ x ≠ a ∧ x ≠ b := by
  constructor
  · rintro (hx | hx)
    · exact ⟨fun hxa => left_notMem_cIoo a b (hxa ▸ hx),
        fun hxb => right_notMem_cIoo a b (hxb ▸ hx)⟩
    · exact ⟨fun hxa => right_notMem_cIoo b a (hxa ▸ hx),
        fun hxb => left_notMem_cIoo b a (hxb ▸ hx)⟩
  · intro hx
    by_cases hab : a.val < b.val
    · by_cases hax : a.val < x.val
      · by_cases hxb : x.val < b.val
        · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by simp [hab, hax, hxb]⟩)
        · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by
            have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
            have hbx : b.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hxb) (by omega)
            simp [hbxa, hbx]⟩)
      · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by
          have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
          have hxa : x.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hax) (by omega)
          simp [hbxa, hxa]⟩)
    · have hba : b.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
      by_cases hbx : b.val < x.val
      · by_cases hxa : x.val < a.val
        · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by simp [hba, hbx, hxa]⟩)
        · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by
            have hax : a.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hxa) (by omega)
            simp [hab, hax]⟩)
      · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by
          have hxb : x.val < b.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hbx) (by omega)
          simp [hab, hxb]⟩)

/-- A point strictly between two endpoints cuts their half-open cyclic interval into two
adjacent half-open intervals. -/
theorem cIco_union_cIco_eq_cIco_of_mem_cIoo {a b c : Fin n} (h : b ∈ cIoo a c) :
    cIco a b ∪ cIco b c = cIco a c := by
  ext x
  rw [Finset.mem_union, mem_cIco, mem_cIco, mem_cIco]
  rw [mem_cIoo] at h
  split_ifs at h ⊢ <;> omega

/-- The two pieces obtained by cutting a half-open cyclic interval at an interior point are
disjoint. -/
theorem disjoint_cIco_cIco_of_mem_cIoo {a b c : Fin n} (h : b ∈ cIoo a c) :
    Disjoint (cIco a b) (cIco b c) := by
  rw [Finset.disjoint_left]
  intro x hxab hxbc
  rw [mem_cIco] at hxab hxbc
  rw [mem_cIoo] at h
  split_ifs at h hxab hxbc <;> omega

/-- An interior point cuts a clockwise open arc into two open arcs and the cutting point. -/
theorem cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo {a b c : Fin n} (h : b ∈ cIoo a c) :
    cIoo a b ∪ insert b (cIoo b c) = cIoo a c := by
  ext x
  rw [mem_cIoo] at h
  simp only [Finset.mem_union, Finset.mem_insert, mem_cIoo, ne_eq, Fin.ext_iff]
  split_ifs at h ⊢ <;> omega

/-- The initial piece of a cut open arc is contained in the whole arc. -/
theorem cIoo_subset_cIoo_right_of_mem_cIoo {a b c : Fin n} (h : b ∈ cIoo a c) :
    cIoo a b ⊆ cIoo a c := by
  rw [← cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo h]
  exact Finset.subset_union_left

/-- The terminal piece of a cut open arc is contained in the whole arc. -/
theorem cIoo_subset_cIoo_left_of_mem_cIoo {a b c : Fin n} (h : b ∈ cIoo a c) :
    cIoo b c ⊆ cIoo a c := by
  rw [← cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo h]
  exact Finset.subset_union_right.trans' (Finset.subset_insert _ _)

/-- A point `v` strictly inside the arc from `u` to `w` cuts every arc from `u` to a point `s` of
the arc from `v` to `w`, counted. -/
theorem ite_mem_cIco_eq_add_of_mem_cIoo {u v w s : Fin n} (hv : v ∈ cIoo u w)
    (hs : s ∈ cIco v w) (t : Fin n) :
    (if t ∈ cIco u s then 1 else 0 : ℕ) =
      (if t ∈ cIco u v then 1 else 0) + if t ∈ cIco v s then 1 else 0 := by
  simp only [mem_cIco, mem_cIoo, ne_eq, ← Fin.val_inj] at hv hs ⊢
  split_ifs at hv hs ⊢ <;> omega

/-- A point `s` of the arc from `u` to `w` cuts it into the arc before `s`, the point `s` and the
open arc after `s`, counted. -/
theorem ite_mem_cIco_eq_add_add {u w s : Fin n} (hs : s ∈ cIco u w) (t : Fin n) :
    (if t ∈ cIco u w then 1 else 0 : ℕ) =
      (if t ∈ cIco u s then 1 else 0) + (if t = s then 1 else 0) +
        if t ∈ cIoo s w then 1 else 0 := by
  simp only [mem_cIco, mem_cIoo, ne_eq, ← Fin.val_inj] at hs ⊢
  split_ifs at hs ⊢ <;> omega

/-- A point outside the clockwise interval from `a` to `b` is either an endpoint or lies in
the opposite clockwise interval. -/
theorem not_mem_cIoo_iff {a b x : Fin n} (h : a ≠ b) :
    x ∉ cIoo a b ↔ x = a ∨ x = b ∨ x ∈ cIoo b a := by
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ((mem_cIoo_or_mem_cIoo_swap_iff h).mpr ⟨hxa, hxb⟩ |>.resolve_left hx))
  · intro hx
    rcases hx with hxa | hxb | hx
    · rw [hxa]
      exact left_notMem_cIoo a b
    · rw [hxb]
      exact right_notMem_cIoo a b
    · intro hxab
      exact not_mem_cIoo_and_cIoo_swap a b x ⟨hxab, hx⟩

/-- Rotating a cyclic order: if `b` lies on the clockwise arc from `a` to `c`, then `c` lies on
the clockwise arc from `b` to `a`. -/
theorem mem_cIoo_cyclic_left {a b c : Fin n} (h : b ∈ cIoo a c) : c ∈ cIoo b a := by
  simp only [cIoo, Set.Finite.mem_toFinset, Set.mem_cIoo] at h ⊢
  exact sbtw_cyclic_left h

/-- Rotating a cyclic order the other way: if `b` lies on the clockwise arc from `a` to `c`, then
`a` lies on the clockwise arc from `c` to `b`. -/
theorem mem_cIoo_cyclic_right {a b c : Fin n} (h : b ∈ cIoo a c) : a ∈ cIoo c b := by
  simp only [cIoo, Set.Finite.mem_toFinset, Set.mem_cIoo] at h ⊢
  exact sbtw_cyclic_right h

/-- A point off both endpoints and outside one cyclic arc lies on the opposite arc. -/
theorem mem_cIoo_swap_of_notMem {a b u : Fin n} (hab : a ≠ b)
    (hua : u ≠ a) (hub : u ≠ b) (hout : u ∉ cIoo a b) : u ∈ cIoo b a :=
  ((mem_cIoo_or_mem_cIoo_swap_iff hab).mpr ⟨hua, hub⟩).resolve_left hout

/-- If `a` and `b` lie on opposite arcs from `c` to `d`, then `d` lies on the clockwise arc from
`a` to `b`.

If `a` lies on the clockwise arc from `c` to `d` while `b` lies on the opposite arc, then the four
points occur in the cyclic order `c`, `a`, `d`, `b`, so `d` lies on the clockwise arc from `a` to
`b`. -/
theorem mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap {a b c d : Fin n} (ha : a ∈ cIoo c d)
    (hb : b ∈ cIoo d c) : d ∈ cIoo a b := by
  simp only [cIoo, Set.Finite.mem_toFinset, Set.mem_cIoo] at ha hb ⊢
  exact sbtw_cyclic_left (sbtw_trans_left (sbtw_cyclic_left hb) ha)

/-- Cyclic separation is symmetric: if `a` lies on the clockwise arc from `c` to `d` while `b`,
distinct from both endpoints, lies off it, then `c` and `d` lie on the two opposite arcs between
`a` and `b`. -/
theorem mem_cIoo_and_mem_cIoo_swap_of_notMem {a b c d : Fin n} (hbc : b ≠ c) (hbd : b ≠ d)
    (hbout : b ∉ cIoo c d) (ha : a ∈ cIoo c d) :
    d ∈ cIoo a b ∧ c ∈ cIoo b a :=
  have hb := mem_cIoo_swap_of_notMem ((mem_cIoo c d a).mp ha).1 hbc hbd hbout
  ⟨mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap ha hb, mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hb ha⟩

/-- The two opposite cyclic intervals cover exactly the complement of their endpoints. -/
@[simp]
theorem cIoo_union_swap {a b : Fin n} (h : a ≠ b) :
    cIoo a b ∪ cIoo b a = (Finset.univ.erase a).erase b := by
  ext x
  rw [Finset.mem_union, mem_cIoo_or_mem_cIoo_swap_iff h]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hxa, hxb⟩
    exact ⟨hxb, hxa⟩
  · rintro ⟨hxb, hxa⟩
    exact ⟨hxa, hxb⟩

/-- The opposite cyclic interval is the endpoint complement with the first interval removed. -/
theorem cIoo_swap_eq_erase_erase_sdiff {a b : Fin n} (h : a ≠ b) :
    cIoo b a = (Finset.univ.erase a).erase b \ cIoo a b := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [← cIoo_union_swap h]
      exact Finset.mem_union_right _ hx
    · intro hxab
      exact not_mem_cIoo_and_cIoo_swap a b x ⟨hxab, hx⟩
  · intro hx
    have hxu : x ∈ cIoo a b ∪ cIoo b a := by
      rw [cIoo_union_swap h]
      exact (Finset.mem_sdiff.mp hx).1
    rcases Finset.mem_union.mp hxu with hxab | hxba
    · exact ((Finset.mem_sdiff.mp hx).2 hxab).elim
    · exact hxba

/-- The two complementary cyclic intervals have total cardinality `n - 2`. -/
theorem card_cIoo_add_card_cIoo_swap {a b : Fin n} (h : a ≠ b) :
    (cIoo a b).card + (cIoo b a).card = n - 2 := by
  have hcard := congrArg Finset.card (cIoo_union_swap h)
  rw [Finset.card_union_of_disjoint (disjoint_cIoo_swap a b)] at hcard
  have hbmem : b ∈ (Finset.univ : Finset (Fin n)).erase a := by
    simp [h.symm]
  rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

/-- In a grid of size at most two, every open cyclic interval is empty. There are no grid points
strictly between two endpoints on either of the two complementary arcs. -/
theorem cIoo_eq_empty_of_le_two (hn : n ≤ 2) (a b : Fin n) : cIoo a b = ∅ := by
  by_cases hab : a = b
  · simp [hab]
  · apply Finset.card_eq_zero.mp
    have hsum := card_cIoo_add_card_cIoo_swap hab
    have hcard : (cIoo a b).card = 0 := by omega
    exact hcard

/-- A clockwise open cyclic interval reversed by `Fin.rev` is the clockwise open cyclic interval
with the two endpoints reversed and exchanged.

Coordinate reversal reverses the cyclic order, so it turns the clockwise arc from `a` to `b` into
the clockwise arc from `bᵒ` to `aᵒ`. -/
theorem cIoo_image_rev (a b : Fin n) : (cIoo a b).image Fin.rev = cIoo b.rev a.rev := by
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cIoo] at hx ⊢
    obtain ⟨hne, hc⟩ := hx
    refine ⟨fun h => hne (Fin.rev_injective h).symm, ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hx' := x.isLt
    simp only [Fin.val_rev]
    split_ifs at hc ⊢ <;> omega
  · intro hy
    refine ⟨Fin.rev y, ?_, Fin.rev_rev y⟩
    rw [mem_cIoo] at hy ⊢
    obtain ⟨hne, hc⟩ := hy
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hy' := y.isLt
    simp only [Fin.val_rev] at hc ⊢
    split_ifs at hc ⊢ <;> omega

/-- Membership in a clockwise open arc with both endpoints and the queried point reversed by
`Fin.rev`. Since coordinate reversal reverses the cyclic order, the reversed point lies in the
reversed arc exactly when the original point lies in the opposite arc. -/
theorem mem_cIoo_rev_rev (a b x : Fin n) :
    x.rev ∈ cIoo a.rev b.rev ↔ x ∈ cIoo b a := by
  rw [← cIoo_image_rev b a, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← Fin.rev_injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The cyclic permutation `finRotate n` preserves and reflects membership in open cyclic
intervals. -/
theorem mem_cIoo_finRotate_finRotate (a b x : Fin n) :
    finRotate n x ∈ cIoo (finRotate n a) (finRotate n b) ↔ x ∈ cIoo a b := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    rw [mem_cIoo, mem_cIoo, (finRotate _).injective.ne_iff]
    simp only [coe_finRotate, Fin.ext_iff, Fin.val_last]
    have := a.isLt; have := b.isLt; have := x.isLt
    split_ifs <;> omega

/-- The cyclic permutation `finRotate n` preserves and reflects membership in half-open cyclic
intervals. -/
theorem mem_cIco_finRotate_finRotate (a b x : Fin n) :
    finRotate n x ∈ cIco (finRotate n a) (finRotate n b) ↔ x ∈ cIco a b := by
  by_cases hab : a = b
  · subst b
    simp
  · rw [cIco_of_ne ((finRotate n).injective.ne hab), cIco_of_ne hab,
      Finset.mem_insert, Finset.mem_insert, (finRotate n).injective.eq_iff,
      mem_cIoo_finRotate_finRotate]

/-- The half-turn `x ↦ finRotate n x.rev` of the cycle, which is negation modulo `n`, reverses
the cyclic order: it carries the clockwise open arc from `a` to `b` onto the clockwise open arc
between the images of `b` and `a`. -/
theorem mem_cIoo_finRotate_rev (a b x : Fin n) :
    finRotate n x.rev ∈ cIoo (finRotate n b.rev) (finRotate n a.rev) ↔ x ∈ cIoo a b := by
  rw [mem_cIoo_finRotate_finRotate, mem_cIoo_rev_rev]

/-- On squares named by their lower-left grid points, the half-turn `x ↦ finRotate n x.rev` of
the grid points acts as `Fin.rev`: it carries the clockwise half-open arc of squares from `a` to
`b` onto the one between the images of `b` and `a` under the half-turn of the grid points. -/
theorem rev_mem_cIco_finRotate_rev (a b x : Fin n) :
    x.rev ∈ cIco (finRotate n b.rev) (finRotate n a.rev) ↔ x ∈ cIco a b := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    have := a.isLt; have := b.isLt; have := x.isLt
    simp only [mem_cIco, ne_eq, coe_finRotate, Fin.ext_iff, Fin.val_last, Fin.val_rev,
      Nat.succ_eq_add_one]
    split_ifs <;>
      (try simp only [not_false_eq_true, not_true_eq_false, true_and, false_and, false_iff]) <;>
      omega

/-- Powers of the cyclic permutation `finRotate n` preserve and reflect membership in open cyclic
intervals. -/
theorem mem_cIoo_finRotate_pow_finRotate_pow (k : ℕ) (a b x : Fin n) :
    (finRotate n ^ k) x ∈ cIoo ((finRotate n ^ k) a) ((finRotate n ^ k) b) ↔ x ∈ cIoo a b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      mem_cIoo_finRotate_finRotate, ih]

/-- Powers of the cyclic permutation `finRotate n` preserve and reflect membership in half-open
cyclic intervals. -/
theorem mem_cIco_finRotate_pow_finRotate_pow (k : ℕ) (a b x : Fin n) :
    (finRotate n ^ k) x ∈ cIco ((finRotate n ^ k) a) ((finRotate n ^ k) b) ↔ x ∈ cIco a b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      mem_cIco_finRotate_finRotate, ih]

/-- Replacing a point by its cyclic successor preserves membership in a half-open cyclic interval
when the successor is not an endpoint. -/
theorem mem_cIco_finRotate_iff_of_ne {a b c : Fin n}
    (ha : a ≠ finRotate n c) (hb : b ≠ finRotate n c) :
    finRotate n c ∈ cIco a b ↔ c ∈ cIco a b := by
  cases n with
  | zero => exact c.elim0
  | succ n =>
    rw [mem_cIco, mem_cIco]
    have hc := c.isLt
    have ha' := a.isLt
    have hb' := b.isLt
    have haVal : a.val ≠ (finRotate (n + 1) c).val := fun h => ha (Fin.ext h)
    have hbVal : b.val ≠ (finRotate (n + 1) c).val := fun h => hb (Fin.ext h)
    by_cases hlast : c = Fin.last n
    · have hrot : (finRotate (n + 1) c).val = 0 := by simp [hlast]
      have hlastVal : c.val = n := by simp [hlast]
      rw [hrot] at haVal hbVal ⊢
      split_ifs <;> omega
    · have hrot : (finRotate (n + 1) c).val = c.val + 1 :=
        coe_finRotate_of_ne_last hlast
      rw [hrot] at haVal hbVal ⊢
      split_ifs <;> omega

/-- The value of the cyclic successor, split into the wrapping and the non-wrapping case. -/
theorem val_finRotate_cases {m : ℕ} (i : Fin (m + 1)) :
    (i.val = m ∧ (finRotate (m + 1) i).val = 0) ∨
      (i.val < m ∧ (finRotate (m + 1) i).val = i.val + 1) := by
  rw [coe_finRotate]
  have := i.isLt
  split_ifs with h
  · exact Or.inl ⟨by simpa [Fin.ext_iff] using h, rfl⟩
  · exact Or.inr ⟨by rw [Fin.ext_iff, Fin.val_last] at h; omega, rfl⟩

/-- **Crossing count for a shifted arc.** For distinct `α` and `β`, going from `p` to `q` enters
the half-open arc from `finRotate n α` to `finRotate n β` once if the arc from `p` to `q` passes
`α`, and leaves it once if it passes `β`. On a grid, with `α` and `β` naming rows of squares and
`p`, `q` horizontal grid lines, the shifted arc is the band of lines `α + 1, …, β` strictly above
the centre of square row `α` and below the centre of square row `β`. -/
theorem ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate {p q α β : Fin n}
    (hpq : p ≠ q) (hαβ : α ≠ β) :
    ((if q ∈ cIco (finRotate n α) (finRotate n β) then 1 else 0 : ℤ) -
        if p ∈ cIco (finRotate n α) (finRotate n β) then 1 else 0) =
      (if α ∈ cIco p q then 1 else 0 : ℤ) - if β ∈ cIco p q then 1 else 0 := by
  cases n with
  | zero => exact p.elim0
  | succ m =>
    have hα := val_finRotate_cases α
    have hβ := val_finRotate_cases β
    simp only [mem_cIco, ne_eq, Fin.ext_iff, ite_prop_iff_or]
    simp only [ne_eq, Fin.ext_iff] at hpq hαβ
    have := p.isLt
    have := q.isLt
    split_ifs <;> omega

/-- On a cycle of length at least two, no point is fixed by the cyclic successor `finRotate n`. -/
theorem finRotate_ne_self (hn : 1 < n) (a : Fin n) : finRotate n a ≠ a := by
  cases n with
  | zero => exact a.elim0
  | succ n =>
    rw [Ne, Fin.ext_iff, coe_finRotate]
    have := a.isLt
    split_ifs with h <;> simp only [Fin.ext_iff, Fin.val_last] at h <;> omega

/-- The open cyclic interval from a point to its cyclic successor is empty. -/
theorem cIoo_finRotate_eq_empty (a : Fin n) : cIoo a (finRotate n a) = ∅ := by
  cases n with
  | zero => exact a.elim0
  | succ n =>
    ext x
    simp only [mem_cIoo, ne_eq, Finset.notMem_empty, iff_false, not_and]
    intro _
    have := a.isLt; have := x.isLt
    rw [coe_finRotate]
    split_ifs with h₁ h₂ <;> simp only [Fin.ext_iff, Fin.val_last] at h₁ <;> omega

/-- Moving from a point `x` to its cyclic successor does not cross the endpoints of an open
cyclic interval that starts away from `x` and ends away from its successor. -/
theorem finRotate_mem_cIoo_iff {a b x : Fin n} (ha : a ≠ x) (hb : b ≠ finRotate n x) :
    finRotate n x ∈ cIoo a b ↔ x ∈ cIoo a b := by
  cases n with
  | zero => exact x.elim0
  | succ m =>
    have hx := val_finRotate_cases x
    simp only [mem_cIoo, ne_eq, Fin.ext_iff] at ha hb ⊢
    have := a.isLt; have := b.isLt
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at hb ⊢ <;> split_ifs <;> omega

/-- The open cyclic interval from the cyclic successor of `a` back to `a` contains every point
except these two, provided they are distinct. -/
theorem mem_cIoo_finRotate_left_iff {a x : Fin n} (ha : a ≠ finRotate n a) :
    x ∈ cIoo (finRotate n a) a ↔ x ≠ a ∧ x ≠ finRotate n a := by
  rw [← mem_cIoo_or_mem_cIoo_swap_iff ha, cIoo_finRotate_eq_empty]
  simp

/-- An endpoint pair whose second point is the cyclic successor of its first is non-interleaving
with every endpoint pair whose first point avoids the first and whose second point avoids the
second. -/
theorem noninterleaving_of_eq_finRotate {a₀ a₁ b₀ b₁ : Fin n} (ha : a₁ = finRotate n a₀)
    (hb₀ : b₀ ≠ a₀) (hb₁ : b₁ ≠ a₁) : Noninterleaving a₀ a₁ b₀ b₁ := by
  subst ha
  refine ⟨(finRotate_mem_cIoo_iff hb₀ hb₁).symm, ?_⟩
  rw [cIoo_finRotate_eq_empty]
  simp

/-- An endpoint pair whose first point is the cyclic successor of its second is non-interleaving
with every endpoint pair disjoint from it. -/
theorem noninterleaving_of_finRotate_eq {a₀ a₁ b₀ b₁ : Fin n} (ha : a₀ = finRotate n a₁)
    (hb₀ : b₀ ≠ a₀) (hb₀' : b₀ ≠ a₁) (hb₁ : b₁ ≠ a₀) (hb₁' : b₁ ≠ a₁) :
    Noninterleaving a₀ a₁ b₀ b₁ := by
  subst ha
  refine ⟨finRotate_mem_cIoo_iff hb₀' hb₁, ?_⟩
  by_cases h : a₁ = finRotate n a₁
  · simp [← h]
  · rw [mem_cIoo_finRotate_left_iff h, mem_cIoo_finRotate_left_iff h]
    exact ⟨fun _ ↦ ⟨hb₁', hb₁⟩, fun _ ↦ ⟨hb₀', hb₀⟩⟩

/-- A half-open cyclic interval is a single point exactly when that point is its initial endpoint
and its terminal endpoint is the distinct cyclic successor of that point. -/
theorem cIco_eq_singleton_iff {a b c : Fin n} :
    cIco a b = {c} ↔ a = c ∧ b = finRotate n c ∧ a ≠ b := by
  constructor
  · intro h
    have hab : a ≠ b := by
      rintro rfl
      simp at h
    have hac : a = c := Finset.mem_singleton.mp (h ▸ left_mem_cIco hab)
    subst c
    refine ⟨rfl, ?_, hab⟩
    have hcard := congrArg Finset.card h
    simp only [card_cIco, Finset.card_singleton, hab, ↓reduceIte] at hcard
    cases n with
    | zero => exact a.elim0
    | succ n =>
      have := a.isLt; have := b.isLt
      rw [Fin.ext_iff, coe_finRotate]
      have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
      by_cases hlast : a = Fin.last n
      · simp only [hlast, ↓reduceIte] at hcard ⊢
        simp only [Fin.val_last] at hcard ⊢
        split_ifs at hcard <;> omega
      · simp only [hlast, ↓reduceIte]
        rw [Fin.ext_iff, Fin.val_last] at hlast
        split_ifs at hcard <;> omega
  · rintro ⟨rfl, rfl, hab⟩
    rw [cIco_of_ne hab, cIoo_finRotate_eq_empty]
    rfl

/-- Non-interleaving is preserved by reversing every endpoint with `Fin.rev`, with the cyclic
orientation reversal accounted for by exchanging the two endpoints within each pair. -/
theorem noninterleaving_rev (a₀ a₁ b₀ b₁ : Fin n) :
    Noninterleaving a₀.rev a₁.rev b₀.rev b₁.rev ↔ Noninterleaving a₁ a₀ b₁ b₀ := by
  rw [Noninterleaving, Noninterleaving]
  simp only [mem_cIoo_rev_rev]
  tauto

/-! ### Inserting a point into a cycle -/

/-- Inserting a new point into the cycle `Fin n` preserves the clockwise open arcs between old
points. -/
theorem mem_cIoo_succAbove_succAbove (p : Fin (n + 1)) (a b x : Fin n) :
    p.succAbove x ∈ cIoo (p.succAbove a) (p.succAbove b) ↔ x ∈ cIoo a b := by
  simp only [mem_cIoo, ne_eq, Fin.succAbove, Fin.lt_def, ← Fin.val_inj]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

/-- Inserting a new point into the cycle `Fin n` preserves the clockwise half-open arcs between
old points. -/
theorem mem_cIco_succAbove_succAbove (p : Fin (n + 1)) (a b x : Fin n) :
    p.succAbove x ∈ cIco (p.succAbove a) (p.succAbove b) ↔ x ∈ cIco a b := by
  simp only [mem_cIco, ne_eq, Fin.succAbove, Fin.lt_def, ← Fin.val_inj]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

/-- A point inserted immediately after `i` lies strictly inside the arc between two old points
exactly when the arc passes from `i` to its successor, that is, when `i` lies in the half-open
arc. -/
theorem mem_cIoo_succ_succAbove_succ_succAbove_iff (i a b : Fin n) :
    i.succ ∈ cIoo (i.succ.succAbove a) (i.succ.succAbove b) ↔ i ∈ cIco a b := by
  simp only [mem_cIoo, mem_cIco, ne_eq, Fin.succAbove, Fin.lt_def, ← Fin.val_inj]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

/-- Collapsing the point inserted immediately after `i` back onto `i` with `Fin.predAbove`
identifies the half-open arcs between old points before and after the insertion. -/
theorem mem_cIco_succ_succAbove_succ_succAbove_iff (i a b : Fin n) (x : Fin (n + 1)) :
    x ∈ cIco (i.succ.succAbove a) (i.succ.succAbove b) ↔ i.predAbove x ∈ cIco a b := by
  induction x using Fin.succAboveCases i.succ with
  | x =>
    rw [Fin.predAbove_succ_self]
    simp only [mem_cIco, ne_eq, Fin.succAbove, Fin.lt_def, ← Fin.val_inj]
    split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega
  | p c => rw [Fin.predAbove_succ_succAbove, mem_cIco_succAbove_succAbove]

/-- The cyclic predecessor of the terminal endpoint `i.succ` lies in every nondegenerate
half-open arc ending there. -/
theorem castSucc_mem_cIco_succ {a : Fin (n + 1)} {i : Fin n} (h : a ≠ i.succ) :
    i.castSucc ∈ cIco a i.succ := by
  rw [ne_eq, ← Fin.val_inj, Fin.val_succ] at h
  simp only [mem_cIco, ne_eq, ← Fin.val_inj, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- A half-open cyclic interval starting strictly inside another is contained in it. -/
theorem cIco_subset_of_mem_cIoo {a b r : Fin n}
    (h : b ∈ cIoo a r) : cIco b r ⊆ cIco a r := by
  have hunion := cIco_union_cIco_eq_cIco_of_mem_cIoo h
  intro x hx
  rw [← hunion]
  exact Finset.mem_union.mpr (Or.inr hx)

/-- Moving the initial endpoint of a half-open cyclic interval covers it by the interval from the
new initial endpoint and the interval between the two initial endpoints: every point of
`cIco t u` lies in `cIco w u ∪ cIco t w`. With no hypothesis on `w` the two intervals may overlap,
so this is a covering by a union, not a partition; the strict cut is
`cIco_union_cIco_eq_cIco_of_mem_cIoo`. -/
theorem cIco_subset_cIco_union_cIco {t w u : Fin n} :
    cIco t u ⊆ cIco w u ∪ cIco t w := by
  intro x h
  by_cases htu : t = u
  · rw [htu] at h
    simp at h
  by_cases hwu : w = u
  · exact Finset.mem_union.mpr (Or.inr (by rw [hwu]; exact h))
  by_cases htw : t = w
  · exact Finset.mem_union.mpr (Or.inl (by rw [← htw]; exact h))
  simp only [Finset.mem_union, mem_cIco] at ⊢
  simp only [mem_cIco] at h
  split_ifs at h ⊢ <;> omega

/-- Interval nesting: a point in `cIco A B` with `B` strictly inside `cIco A C` lies in
`cIco A C`. This is the `cIco`-membership version of `cIco_subset_of_mem_cIoo`. -/
theorem mem_cIco_of_mem_cIco_of_mem_cIoo {A B C s : Fin n}
    (hmem : s ∈ cIco A B) (hB : B ∈ cIoo A C) :
    s ∈ cIco A C := by
  have hunion := cIco_union_cIco_eq_cIco_of_mem_cIoo hB
  rw [← hunion]
  exact Finset.mem_union.mpr (Or.inl hmem)

/-- A point is never in the half-open cyclic interval starting at its own successor.
Going clockwise from `c + 1`, the point `c` is the last point reached — only after a full
cycle. The half-open arc `cIco (c + 1) r` stops before `r`, hence before completing the
cycle, so it never reaches `c`.
Stated with `c + 1` rather than `finRotate n c` so the left-hand side is already
in simp normal form (`finRotate_apply` would otherwise rewrite it). The `NeZero n`
instance needed for `c + 1` is supplied locally from `c` itself (as in `finRotate_apply`),
so no typeclass hypothesis is required. -/
@[simp high]
theorem notMem_cIco_finRotate_left (c r : Fin n) :
    haveI := c.neZero; c ∉ cIco (c + 1) r := by
  match n with
  | 0 => exact c.elim0
  | n + 1 =>
    have h : c + 1 = finRotate (n + 1) c := (finRotate_apply c).symm
    rw [h, mem_cIco]
    rintro ⟨hne, hmem⟩
    have hc := c.isLt
    have hr := r.isLt
    have hne' : (finRotate (n + 1) c).val ≠ r.val := fun h => hne (Fin.ext h)
    by_cases hlast : c = Fin.last n
    · -- `c` is last: `finRotate` wraps to 0
      have hrot : (finRotate (n + 1) c).val = 0 := by
        rw [coe_finRotate]
        simp [hlast]
      have hcval : c.val = n := by simp [hlast]
      rw [hrot] at hmem hne'
      split_ifs at hmem with h <;> omega
    · -- `c` is not last: `finRotate` increments by 1
      have hrot : (finRotate (n + 1) c).val = c.val + 1 :=
        coe_finRotate_of_ne_last hlast
      rw [hrot] at hmem hne'
      split_ifs at hmem with h <;> omega

/-- A point lies in every nondegenerate half-open cyclic interval ending at its own cyclic
successor: going clockwise, `a` is the last point reached before `finRotate n a`, so any arc
that stops there and does not start there has already passed through `a`. -/
theorem self_mem_cIco_finRotate {a c : Fin n} (h : c ≠ finRotate n a) :
    a ∈ cIco c (finRotate n a) := by
  have hmem : a ∈ cIco c (finRotate n a) ∪ cIco (finRotate n a) c := by
    rw [cIco_union_swap h]
    exact Finset.mem_univ a
  -- The complementary arc starts at the cyclic successor of `a`, so it misses `a`: that is
  -- `notMem_cIco_finRotate_left`, which `simp` applies once `finRotate n a` is normalized.
  exact (Finset.mem_union.mp hmem).resolve_right (by simp)

/-- A point missing both halves of a half-open cyclic interval cut at an interior point
misses the whole interval. -/
theorem notMem_cIco_of_cIco_union {p r₀ r₁ s : Fin n}
    (h₁ : p ∉ cIco r₀ r₁) (h₂ : p ∉ cIco r₁ s) (hcyc : r₁ ∈ cIoo r₀ s) :
    p ∉ cIco r₀ s := by
  -- Rewrite the goal interval as the union of the two halves, then case on the union.
  intro hmem
  rw [← cIco_union_cIco_eq_cIco_of_mem_cIoo hcyc] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact h₁ h
  · exact h₂ h

/-! ### Positions on the cycle -/

/-- The position of `r` on the cycle `Fin n` read clockwise from the cyclic successor of `p`: the
length of the half-open arc from `finRotate n p` to `r`. The successor of `p` has position `0`
and `p` itself comes last. -/
noncomputable def cyclicPosition (p r : Fin n) : ℕ :=
  (cIco (finRotate n p) r).card

/-- The cyclic successor `p + 1` of `p` (that is, `finRotate n p`) comes first, in position
`0`. -/
@[simp]
theorem cyclicPosition_add_one_self (p : Fin n) :
    haveI := p.neZero; cyclicPosition p (p + 1) = 0 := by
  cases n with
  | zero => exact p.elim0
  | succ n => simp [cyclicPosition, cIco_self]

/-- The point `p` itself comes last, in position `n - 1`. -/
@[simp]
theorem cyclicPosition_self (p : Fin n) : cyclicPosition p p = n - 1 := by
  cases n with
  | zero => exact p.elim0
  | succ n =>
    have := p.isLt
    simp only [cyclicPosition, card_cIco, ← Fin.val_inj, coe_finRotate, Fin.val_last]
    split_ifs <;> omega

/-- Two distinct points whose half-open arc avoids `p` come in strictly increasing order of
position read from the cyclic successor of `p`. -/
theorem cyclicPosition_lt_of_notMem_cIco {p a b : Fin n} (hab : a ≠ b) (h : p ∉ cIco a b) :
    cyclicPosition p a < cyclicPosition p b := by
  cases n with
  | zero => exact p.elim0
  | succ n =>
    have := p.isLt; have := a.isLt; have := b.isLt
    have hab' : a.val ≠ b.val := fun e ↦ hab (Fin.ext e)
    simp only [cyclicPosition, card_cIco, mem_cIco, ne_eq, ← Fin.val_inj, coe_finRotate,
      Fin.val_last] at h ⊢
    split_ifs at h ⊢ <;> omega

end Grid

end TauCeti
