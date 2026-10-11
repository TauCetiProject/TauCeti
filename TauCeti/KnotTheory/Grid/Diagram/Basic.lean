/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin

import Mathlib.Data.Sym.Card

/-!
# Grid diagrams and grid states

A grid state of grid number `n` is a wrapper around a permutation of `Fin n`, sending each
column to the unique row occupied by the state in that column. A grid diagram is encoded by two
such permutation graphs, one for the `O` markings and one for the `X` markings, with the
condition that no square contains both markings.

A state coordinate `(c, r)` is the grid point where column line `c` meets row line `r`. A marking
coordinate `(c, r)` instead names the square whose lower-left corner is that grid point, bounded
by column lines `c`, `c + 1` and row lines `r`, `r + 1`, with indices read cyclically.

The point-set API records the basic row, column, cardinality, and disjointness facts about the
occupied grid points of a grid state.

* `TauCeti.GridState`: a grid state with a permutation graph on `Fin n`.
* `TauCeti.GridState.subdiagonal`: the grid state whose occupied row is one below its column.
* `TauCeti.GridState.pointSet`: the finite set of occupied grid points of a grid state.
* `TauCeti.GridDiagram`: an `n × n` grid diagram with `O` and `X` markings.
* `TauCeti.GridDiagram.OSet`, `TauCeti.GridDiagram.XSet`: the marking-square sets.
* Relabeling, swapping, transposition, and marking-swap operations for grid states and diagrams.

## References

* Ozsváth–Stipsicz–Szabó, *Grid Homology for Knots and Links*: grid diagrams (one `O` and one
  `X` marking in each row and column) in Chapter 3, and grid states (one point in each row and
  column) in Chapter 4.
-/

@[expose] public section

namespace TauCeti

/-- A grid state on an `n × n` toroidal grid.

The field `toPerm` sends each column to its occupied row. The named wrapper gives grid states
their own preferred point-set API below, while still allowing direct access to the underlying
permutation when needed. -/
structure GridState (n : ℕ) where
  /-- The permutation sending each column to the occupied row in that column. -/
  toPerm : Equiv.Perm (Fin n)

namespace GridState

variable {n : ℕ}

/-- Grid states on an `n × n` grid are equivalent to permutations of `Fin n`, via the
column-to-row permutation. -/
@[simps]
def equivPerm (n : ℕ) : GridState n ≃ Equiv.Perm (Fin n) where
  toFun x := x.toPerm
  invFun σ := ⟨σ⟩
  left_inv x := by cases x; rfl
  right_inv σ := rfl

/-- There are finitely many grid states of a fixed grid size. -/
instance : Fintype (GridState n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n)) (equivPerm n).symm

/-- Equality of grid states is decidable: a grid state is determined by its underlying
permutation, whose equality is decidable. This makes finite sets of grid states computable. -/
instance : DecidableEq (GridState n) :=
  (equivPerm n).decidableEq

/-- Apply a grid state to a column to get its occupied row. -/
instance : CoeFun (GridState n) fun _ => Fin n → Fin n where
  coe x := x.toPerm

/-- Grid states are extensional in their column-to-row functions. -/
@[ext]
theorem ext {x y : GridState n} (h : ∀ c : Fin n, x c = y c) : x = y :=
  (equivPerm n).injective (Equiv.ext h)

/-- The subdiagonal grid state of an `n`-column grid: its point in column `c` lies one row below
the diagonal point `(c, c)`. -/
def subdiagonal (n : ℕ) : GridState n :=
  ⟨(finRotate n)⁻¹⟩

/-- The permutation underlying the subdiagonal state is the inverse cyclic shift. -/
theorem subdiagonal_toPerm (n : ℕ) : (subdiagonal n).toPerm = (finRotate n)⁻¹ :=
  rfl

/-- The subdiagonal state reads off the inverse cyclic shift. -/
theorem subdiagonal_apply (c : Fin n) :
    subdiagonal n c = (finRotate n)⁻¹ c :=
  rfl

/-- Moving the subdiagonal point of a column up one row reaches the diagonal. -/
theorem subdiagonal_apply_add_one [NeZero n] (c : Fin n) :
    subdiagonal n c + 1 = c := by
  rw [← finRotate_apply, subdiagonal_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-- The subdiagonal state sends each column to the preceding row. -/
@[simp]
theorem subdiagonal_apply_eq_sub_one [NeZero n] (c : Fin n) :
    subdiagonal n c = c - 1 :=
  eq_sub_iff_add_eq.mpr (subdiagonal_apply_add_one c)

/-- The finite set of occupied grid points of a grid state. The first coordinate is the column and
the second coordinate is the row. -/
def pointSet (x : GridState n) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun c => (c, x c)

/-- The point set of the grid state obtained from `σ` is the graph `{(c, σ c)}`. -/
theorem equivPerm_symm_pointSet (σ : Equiv.Perm (Fin n)) :
    ((equivPerm n).symm σ : GridState n).pointSet = Finset.univ.image fun c => (c, σ c) := rfl

/-- Membership in the point set of a grid state is the graph condition for its permutation. -/
@[simp]
theorem mem_pointSet (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.pointSet ↔ x p.1 = p.2 := by
  simp [pointSet, Prod.ext_iff]

/-- The grid point `(c, r)` lies in a grid state's point set exactly when `x c = r`. -/
theorem mk_mem_pointSet (x : GridState n) (c r : Fin n) : (c, r) ∈ x.pointSet ↔ x c = r := by
  simp

/-- The point set of a grid state has exactly `n` occupied grid points. -/
@[simp]
theorem card_pointSet (x : GridState n) : x.pointSet.card = n := by
  rw [pointSet, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    exact Prod.mk.inj hab |>.1

/-- A sum over the occupied grid points of a grid state is a sum over the columns. -/
theorem sum_pointSet {M : Type*} [AddCommMonoid M] (x : GridState n)
    (f : Fin n × Fin n → M) : ∑ p ∈ x.pointSet, f p = ∑ c : Fin n, f (c, x c) := by
  rw [pointSet, Finset.sum_image]
  intro c _ c' _ hc
  exact (Prod.ext_iff.mp hc).1

/-- A grid state meets a set of columns in as many occupied grid points as there are columns. -/
theorem sum_ite_mem_columns {R : Type*} [AddCommMonoidWithOne R] (x : GridState n)
    (C : Finset (Fin n)) :
    ∑ p ∈ x.pointSet, (if p.1 ∈ C then (1 : R) else 0) = (C.card : R) := by
  rw [sum_pointSet]
  simp

/-- A grid state meets a set of rows in as many occupied grid points as there are rows. -/
theorem sum_ite_mem_rows {R : Type*} [AddCommMonoidWithOne R] (x : GridState n)
    (D : Finset (Fin n)) :
    ∑ p ∈ x.pointSet, (if p.2 ∈ D then (1 : R) else 0) = (D.card : R) := by
  rw [sum_pointSet, Equiv.sum_comp x.toPerm fun r => if r ∈ D then (1 : R) else 0]
  simp

/-- A product of column and row sets avoids a grid state's points exactly when every
column in the first set has its occupied row outside the second set. -/
theorem disjoint_product_pointSet_iff (M : GridState n) (s t : Finset (Fin n)) :
    Disjoint (s ×ˢ t) M.pointSet ↔ ∀ c ∈ s, M c ∉ t := by
  rw [Finset.disjoint_left]
  constructor
  · intro h c hc ht
    exact h (Finset.mk_mem_product hc ht) ((M.mk_mem_pointSet c (M c)).2 rfl)
  · intro h p hp hM
    obtain ⟨hc, hr⟩ := Finset.mem_product.mp hp
    exact h p.1 hc ((M.mem_pointSet p).1 hM ▸ hr)

/-- A grid state occupies a grid point in every column, so its point set meets `s ×ˢ univ` for every
nonempty set `s` of columns. -/
theorem not_disjoint_product_univ_pointSet (M : GridState n) {s : Finset (Fin n)}
    (hs : s.Nonempty) : ¬Disjoint (s ×ˢ (Finset.univ : Finset (Fin n))) M.pointSet := by
  rw [M.disjoint_product_pointSet_iff]
  obtain ⟨c, hc⟩ := hs
  exact fun h => h c hc (Finset.mem_univ (M c))

/-- A grid state occupies a grid point in every row, so its point set meets `univ ×ˢ t` for every
nonempty set `t` of rows. -/
theorem not_disjoint_univ_product_pointSet (M : GridState n) {t : Finset (Fin n)}
    (ht : t.Nonempty) : ¬Disjoint ((Finset.univ : Finset (Fin n)) ×ˢ t) M.pointSet := by
  rw [M.disjoint_product_pointSet_iff]
  obtain ⟨r, hr⟩ := ht
  intro h
  exact h (M.toPerm.symm r) (Finset.mem_univ _)
    ((M.toPerm.apply_symm_apply r).symm ▸ hr)

/-- A row with one column removed avoids a grid state's points exactly when the point in
that row lies in the removed column. -/
theorem disjoint_univ_erase_product_singleton_pointSet_iff (M : GridState n) (c r : Fin n) :
    Disjoint ((Finset.univ.erase c) ×ˢ ({r} : Finset (Fin n))) M.pointSet ↔ M c = r := by
  rw [M.disjoint_product_pointSet_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨d, hd⟩ := M.toPerm.surjective r
    have hdc : d = c := by
      by_contra hdc
      exact h d hdc hd
    simpa only [hdc] using hd
  · intro h d hdc hd
    exact hdc (M.toPerm.injective (hd.trans h.symm))

/-- Point sets of grid states are equal exactly when the underlying permutations are equal. -/
@[simp]
theorem pointSet_inj {x y : GridState n} : x.pointSet = y.pointSet ↔ x = y :=
  ⟨fun h => ext fun c => by rw [← mk_mem_pointSet, h, mk_mem_pointSet], congrArg _⟩

/-- Two grid states have disjoint point sets exactly when they disagree in every column. -/
theorem disjoint_pointSet_iff (x y : GridState n) :
    Disjoint x.pointSet y.pointSet ↔ ∀ c : Fin n, x c ≠ y c := by
  simp [Finset.disjoint_right]

/-- Relabel the rows of a grid state by a permutation of `Fin n`.

If `ρ` is the row permutation, the point in column `c` moves from row `x c` to row
`ρ (x c)`. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm := x.toPerm.trans ρ

/-- Relabel the columns of a grid state by a permutation of `Fin n`.

The point in the old column `c` appears in the new column `κ c`, so the row in a new column
`c` is read from the old column `κ.symm c`. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm := κ.symm.trans x.toPerm

/-- Row relabeling evaluates by applying the row permutation to the old row. -/
@[simp]
theorem relabelRows_apply (ρ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelRows ρ c = ρ (x c) :=
  rfl

/-- Column relabeling evaluates by reading the old state at the inverse column. -/
@[simp]
theorem relabelColumns_apply (κ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelColumns κ c = x (κ.symm c) :=
  rfl

/-- Relabeling rows by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelRows_refl (x : GridState n) : x.relabelRows (Equiv.refl (Fin n)) = x :=
  rfl

/-- Relabeling columns by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelColumns_refl (x : GridState n) :
    x.relabelColumns (Equiv.refl (Fin n)) = x :=
  rfl

/-- Successive row relabelings compose. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelRows σ = x.relabelRows (ρ.trans σ) :=
  rfl

/-- Successive column relabelings compose. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).relabelColumns τ = x.relabelColumns (κ.trans τ) :=
  rfl

/-- Row and column relabeling commute on grid states. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelColumns κ = (x.relabelColumns κ).relabelRows ρ :=
  rfl

/-- Membership in the point set after a row relabeling. -/
theorem mem_pointSet_relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.relabelRows ρ).pointSet ↔ (p.1, ρ.symm p.2) ∈ x.pointSet := by
  simp [Equiv.eq_symm_apply]

/-- Membership in the point set after a column relabeling. -/
theorem mem_pointSet_relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.relabelColumns κ).pointSet ↔ (κ.symm p.1, p.2) ∈ x.pointSet := by
  simp

/-- Undoing a row relabeling transports the relabeled state's points to the original
point set. -/
theorem pointSet_eq_map_relabelRows (x : GridState n) (ρ : Equiv.Perm (Fin n)) :
    x.pointSet = (x.relabelRows ρ).pointSet.map
      ((Equiv.refl (Fin n)).prodCongr ρ.symm).toEmbedding := by
  ext p
  simp only [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_symm,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    mem_pointSet_relabelRows, Equiv.symm_apply_apply]

/-- Undoing a column relabeling transports the relabeled state's points to the original
point set. -/
theorem pointSet_eq_map_relabelColumns (x : GridState n) (κ : Equiv.Perm (Fin n)) :
    x.pointSet = (x.relabelColumns κ).pointSet.map
      (κ.symm.prodCongr (Equiv.refl (Fin n))).toEmbedding := by
  ext p
  simp only [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_symm,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    mem_pointSet_relabelColumns, Equiv.symm_apply_apply]

/-- A set of squares relabeled back avoids a state's points exactly when the set avoids
the row-relabeled state's points. -/
theorem disjoint_map_relabelRows_pointSet_iff (x : GridState n) (ρ : Equiv.Perm (Fin n))
    (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map ((Equiv.refl (Fin n)).prodCongr ρ.symm).toEmbedding) x.pointSet ↔
      Disjoint S (x.relabelRows ρ).pointSet := by
  rw [x.pointSet_eq_map_relabelRows ρ, Finset.disjoint_map]

/-- A set of squares relabeled back avoids a state's points exactly when the set avoids
the column-relabeled state's points. -/
theorem disjoint_map_relabelColumns_pointSet_iff (x : GridState n) (κ : Equiv.Perm (Fin n))
    (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map (κ.symm.prodCongr (Equiv.refl (Fin n))).toEmbedding) x.pointSet ↔
      Disjoint S (x.relabelColumns κ).pointSet := by
  rw [x.pointSet_eq_map_relabelColumns κ, Finset.disjoint_map]

/-- Swapping two rows in a grid state. -/
def swapRows (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid state. -/
def swapColumns (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelColumns (Equiv.swap a b)

/-- Row swaps evaluate by swapping the row selected by the old state. -/
@[simp]
theorem swapRows_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapRows a b c = Equiv.swap a b (x c) :=
  rfl

/-- Column swaps evaluate by reading the old state at the swapped column. -/
@[simp]
theorem swapColumns_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapColumns a b c = x (Equiv.swap a b c) := by
  simp [swapColumns, relabelColumns]

/-- Swapping columns is symmetric in the two chosen columns. -/
theorem swapColumns_comm (a b : Fin n) (x : GridState n) :
    x.swapColumns a b = x.swapColumns b a := by
  ext c
  simp [swapColumns_apply, Equiv.swap_comm]

/-- Swapping two columns of a grid state is the same as swapping the two rows they occupy: the
state is a bijection between columns and rows, so either operation exchanges the rows of the
points in columns `a` and `b` and leaves every other point in place. -/
theorem swapColumns_eq_swapRows (a b : Fin n) (x : GridState n) :
    x.swapColumns a b = x.swapRows (x a) (x b) := by
  ext c
  simp [x.toPerm.injective.swap_apply]

/-- Swapping the same pair of columns twice is the identity on grid states. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp [swapColumns]

/-- Conjugating the first transposition by the second reorders two column swaps.

When the pairs are disjoint this is commutation. When `a ≠ b`, `c ≠ d`, and the pairs share
exactly one column, the conjugated pair is the third pair among the three involved columns. -/
theorem swapColumns_swapColumns_conj (x : GridState n) (a b c d : Fin n) :
    (x.swapColumns a b).swapColumns c d =
      (x.swapColumns c d).swapColumns (Equiv.swap c d a) (Equiv.swap c d b) := by
  refine GridState.ext fun k => ?_
  simp only [swapColumns_apply]
  simpa using
    ((Equiv.swap c d).injective.swap_apply (Equiv.swap c d a) (Equiv.swap c d b) k)

/-- The grid states obtained from `x` by transposing a pair of distinct columns.

These are exactly the states a single grid rectangle can reach from `x`: the fully blocked
differential of the generator `x` is supported here. -/
def columnSwapNeighbors (x : GridState n) : Finset (GridState n) :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).image
    fun p => x.swapColumns p.1 p.2

/-- A state is a column-swap neighbour of `x` exactly when it is `x` with a pair of distinct
columns transposed. -/
@[simp]
theorem mem_columnSwapNeighbors {x y : GridState n} :
    y ∈ x.columnSwapNeighbors ↔ ∃ c d : Fin n, c ≠ d ∧ y = x.swapColumns c d := by
  simp [columnSwapNeighbors, eq_comm]

/-- If `y` is a column-swap neighbour of `x`, then `x` is a column-swap neighbour of `y`.

This is the elementary reversibility of a rectangle target: the same pair of side columns swaps
back to the source state. -/
theorem mem_columnSwapNeighbors_comm {x y : GridState n} :
    y ∈ x.columnSwapNeighbors ↔ x ∈ y.columnSwapNeighbors := by
  simp only [mem_columnSwapNeighbors]
  constructor <;> rintro ⟨a, b, hab, rfl⟩ <;> exact ⟨a, b, hab, by simp⟩

/-- The finite set of column-swap neighbours is the image of the off-diagonal of the
column set: an ordered pair of distinct columns gives the state obtained by swapping
those columns. -/
theorem columnSwapNeighbors_eq_offDiag_image (x : GridState n) :
    x.columnSwapNeighbors =
      (Finset.univ : Finset (Fin n)).offDiag.image fun p => x.swapColumns p.1 p.2 := by
  ext y
  simp [columnSwapNeighbors, Finset.mem_offDiag]

/-- If a nontrivial column swap of a grid state agrees with another column swap of it, then the two
swap the same unordered pair of columns. -/
theorem sym2_mk_eq_of_swapColumns_eq {x : GridState n} {a b c d : Fin n} (hab : a ≠ b)
    (h : x.swapColumns a b = x.swapColumns c d) : s(a, b) = s(c, d) := by
  have hswap : Equiv.swap a b = Equiv.swap c d := Equiv.ext fun k =>
    x.toPerm.injective (by simpa [swapColumns_apply] using congrArg (fun y : GridState n => y k) h)
  have ha : a = c ∨ a = d := by
    by_contra hnot
    rw [not_or] at hnot
    have hval := congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hnot.1 hnot.2] at hval
    exact hab hval.symm
  rcases ha with rfl | rfl
  · have hbd : b = d := by
      simpa using congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [hbd]
  · have hbc : b = c := by
      simpa using congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [hbc, Sym2.eq_swap]

/-- A grid state has exactly `n.choose 2` column-swap neighbours. -/
@[simp]
theorem card_columnSwapNeighbors (x : GridState n) :
    x.columnSwapNeighbors.card = n.choose 2 := by
  let f : Sym2 (Fin n) → GridState n :=
    Sym2.lift ⟨fun a b => x.swapColumns a b, fun a b => swapColumns_comm a b x⟩
  have h : x.columnSwapNeighbors = (Finset.univ.offDiag.image Sym2.mk.uncurry).image f := by
    rw [x.columnSwapNeighbors_eq_offDiag_image, Finset.image_image]
    rfl
  rw [h, Finset.card_image_of_injOn, Sym2.card_image_offDiag, Finset.card_univ, Fintype.card_fin]
  rintro _ hz _ hw hzw
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨⟨c, d⟩, -, rfl⟩ := Finset.mem_image.mp hw
  exact sym2_mk_eq_of_swapColumns_eq (Finset.mem_offDiag.mp hab).2.2 hzw

-- Not `@[simp]`: `mem_columnSwapNeighbors` already rewrites the left-hand side.
/-- A grid state is not a column-swap neighbour of itself: swapping two distinct columns moves the
occupied row of either column, so the result differs from the original. -/
theorem self_notMem_columnSwapNeighbors (x : GridState n) : x ∉ x.columnSwapNeighbors := by
  rw [mem_columnSwapNeighbors]
  rintro ⟨c, d, hcd, hx⟩
  have hval := congrArg (fun z : GridState n => z c) hx
  simp only [swapColumns_apply, Equiv.swap_apply_left] at hval
  exact hcd (x.toPerm.injective hval)

/-- Row swaps transport the point set by the row transposition. -/
theorem mem_pointSet_swapRows (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapRows a b).pointSet ↔ (p.1, Equiv.swap a b p.2) ∈ x.pointSet := by
  simpa [swapRows] using GridState.mem_pointSet_relabelRows (Equiv.swap a b) x p

/-- Column swaps transport the point set by the column transposition. -/
theorem mem_pointSet_swapColumns (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapColumns a b).pointSet ↔ (Equiv.swap a b p.1, p.2) ∈ x.pointSet := by
  simp [swapColumns]

/-- A grid point is shared by a grid state and a column relabeling exactly when it is a
source-state grid point whose column is fixed by the relabeling permutation. -/
theorem mem_pointSet_inter_relabelColumns_iff (x : GridState n) (κ : Equiv.Perm (Fin n))
    (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ (x.relabelColumns κ).pointSet ↔ p ∈ x.pointSet ∧ κ p.1 = p.1 := by
  simp only [Finset.mem_inter, mem_pointSet, relabelColumns_apply, and_congr_right_iff]
  intro h
  rw [← h, x.toPerm.injective.eq_iff, Equiv.symm_apply_eq, eq_comm]

/-- Swapping the same pair of rows twice is the identity on grid states. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (x : GridState n) : (x.swapRows a b).swapRows a b = x := by
  ext c
  simp [swapRows]

/-- A grid point is shared by a grid state and the state with columns `a` and `b` swapped exactly
when it is a source-state grid point away from the two swapped columns. -/
theorem mem_pointSet_inter_swapColumns_iff (x : GridState n) {a b : Fin n} (h : a ≠ b)
    (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ (x.swapColumns a b).pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ a ∧ p.1 ≠ b := by
  rw [swapColumns, mem_pointSet_inter_relabelColumns_iff]
  constructor
  · rintro ⟨hx, hfixed⟩
    refine ⟨hx, ?_, ?_⟩
    · intro hpa
      rw [hpa, Equiv.swap_apply_left] at hfixed
      exact h hfixed.symm
    · intro hpb
      rw [hpb, Equiv.swap_apply_right] at hfixed
      exact h hfixed
  · rintro ⟨hx, ha, hb⟩
    exact ⟨hx, Equiv.swap_apply_of_ne_of_ne ha hb⟩

/-- The point set of a grid state is the shared part with a column swap, together with the two
source-state grid points in the swapped columns. -/
theorem pointSet_eq_insert_insert_inter_swapColumns (x : GridState n) (a b : Fin n) :
    x.pointSet =
      insert (a, x a) (insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  rcases eq_or_ne a b with rfl | h
  · simp [swapColumns]
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hx
    rcases eq_or_ne p.1 a with ha | ha
    · refine Or.inl ?_
      have : p.2 = x a := by
        simpa [ha] using ((mem_pointSet x p).mp hx).symm
      exact Prod.ext ha this
    · rcases eq_or_ne p.1 b with hb | hb
      · refine Or.inr (Or.inl ?_)
        have : p.2 = x b := by
          simpa [hb] using ((mem_pointSet x p).mp hx).symm
        exact Prod.ext hb this
      · exact Or.inr (Or.inr ((mem_pointSet_inter_swapColumns_iff x h p).mpr ⟨hx, ha, hb⟩))
  · rintro (rfl | rfl | hp)
    · simp
    · simp
    · exact Finset.mem_of_mem_inter_left hp

/-- The point set after swapping columns `a` and `b` is the shared part with the source state,
together with the two target-state grid points in the swapped columns. -/
theorem swapColumns_pointSet_eq_insert_insert_inter (x : GridState n) (a b : Fin n) :
    (x.swapColumns a b).pointSet =
      insert (a, x b) (insert (b, x a) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  simpa [Finset.inter_comm] using
    (x.swapColumns a b).pointSet_eq_insert_insert_inter_swapColumns a b

/-- A grid state and a swap of two distinct columns share exactly `n - 2` grid points. -/
theorem card_pointSet_inter_swapColumns (x : GridState n) {a b : Fin n} (h : a ≠ b) :
    (x.pointSet ∩ (x.swapColumns a b).pointSet).card = n - 2 := by
  have hne : (b, x b) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
    rw [mem_pointSet_inter_swapColumns_iff x h]
    rintro ⟨_, _, hb⟩
    exact hb rfl
  have hne' :
      (a, x a) ∉ insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet) := by
    rw [Finset.mem_insert]
    rintro (hab | ha)
    · exact absurd (congrArg Prod.fst hab) h
    · rw [mem_pointSet_inter_swapColumns_iff x h] at ha
      exact ha.2.1 rfl
  have hcard := congrArg Finset.card (pointSet_eq_insert_insert_inter_swapColumns x a b)
  rw [card_pointSet, Finset.card_insert_of_notMem hne',
    Finset.card_insert_of_notMem hne] at hcard
  omega

/-- The diagonal reflection of a grid state.

Reflecting the occupied grid points across the main diagonal exchanges columns and rows, so the new
permutation graph is the inverse of the old one. -/
def transpose (x : GridState n) : GridState n where
  toPerm := x.toPerm.symm

/-- The diagonal reflection evaluates by the inverse permutation graph. -/
@[simp]
theorem transpose_apply (x : GridState n) (c : Fin n) : x.transpose c = x.toPerm.symm c :=
  rfl

/-- The point of `x` in row `r` lies in column `x.transpose r`. -/
theorem apply_transpose_apply (x : GridState n) (r : Fin n) : x (x.transpose r) = r := by
  simpa only [transpose_apply] using x.toPerm.apply_symm_apply r

/-- The point of `x` in column `c` lies in row `x c`, so `x.transpose` sends that row back to
`c`. -/
theorem transpose_apply_apply (x : GridState n) (c : Fin n) : x.transpose (x c) = c := by
  simpa only [transpose_apply] using x.toPerm.symm_apply_apply c

/-- The diagonal reflection is an involution on grid states. -/
@[simp]
theorem transpose_transpose (x : GridState n) : x.transpose.transpose = x :=
  rfl

/-- Reflecting after a row relabeling is the same as column relabeling after reflecting. -/
@[simp]
theorem relabelRows_transpose (ρ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).transpose = x.transpose.relabelColumns ρ :=
  rfl

/-- Reflecting after a column relabeling is the same as row relabeling after reflecting. -/
@[simp]
theorem relabelColumns_transpose (κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).transpose = x.transpose.relabelRows κ :=
  rfl

/-- Reflecting after a row swap is the same as the corresponding column swap after reflecting. -/
@[simp]
theorem swapRows_transpose (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).transpose = x.transpose.swapColumns a b :=
  rfl

/-- Reflecting after a column swap is the same as the corresponding row swap after reflecting. -/
@[simp]
theorem swapColumns_transpose (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).transpose = x.transpose.swapRows a b :=
  rfl

/-- A grid point lies in the reflected state exactly when its diagonal reflection lies in the
original state. -/
theorem mem_pointSet_transpose (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.transpose.pointSet ↔ Prod.swap p ∈ x.pointSet := by
  simp only [mem_pointSet, transpose_apply]
  rw [Equiv.symm_apply_eq, eq_comm]
  rfl

/-- The point set of the reflected state is the diagonal reflection of the original point set. -/
theorem transpose_pointSet (x : GridState n) :
    x.transpose.pointSet = x.pointSet.image Prod.swap := by
  ext p
  rw [mem_pointSet_transpose, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨Prod.swap p, hp, Prod.swap_swap p⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [Prod.swap_swap]

end GridState

/-- An `n × n` grid diagram, encoded by the `O`-marking and `X`-marking permutation graphs.

The permutation fields enforce one `O` and one `X` in each row and column. The `disjoint`
field says no square contains both markings. With this encoding `GridDiagram 0`, the empty
diagram, is inhabited, while `GridDiagram 1` is empty: its only `O` and `X` permutations put
both markings in the single square. -/
@[ext]
structure GridDiagram (n : ℕ) where
  /-- The `O` marking in each column, encoded by its row. -/
  O : GridState n
  /-- The `X` marking in each column, encoded by its row. -/
  X : GridState n
  /-- No square contains both an `O` marking and an `X` marking. -/
  disjoint : ∀ c : Fin n, O c ≠ X c

/-- There is no grid diagram of size `1`: the unique `O` and `X` markings would have to
occupy the same square. -/
instance : IsEmpty (GridDiagram 1) where
  false := by
    intro G
    exact G.disjoint 0 (Subsingleton.elim _ _)

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The finite set of `O`-marked squares of a grid diagram. A pair `(c, r)` names the square whose
lower-left grid point is `(c, r)`. -/
def OSet : Finset (Fin n × Fin n) :=
  G.O.pointSet

/-- The finite set of `X`-marked squares of a grid diagram. A pair `(c, r)` names the square whose
lower-left grid point is `(c, r)`. -/
def XSet : Finset (Fin n × Fin n) :=
  G.X.pointSet

/-- The `O`-marking set is the grid-point set of the `O` permutation. -/
theorem OSet_def : G.OSet = G.O.pointSet :=
  rfl

/-- The `X`-marking set is the grid-point set of the `X` permutation. -/
theorem XSet_def : G.XSet = G.X.pointSet :=
  rfl

/-- Membership in the `O`-marking set is the graph condition for the `O` permutation. -/
@[simp]
theorem mem_OSet (p : Fin n × Fin n) : p ∈ G.OSet ↔ G.O p.1 = p.2 := by
  simp [OSet_def]

/-- Membership in the `X`-marking set is the graph condition for the `X` permutation. -/
@[simp]
theorem mem_XSet (p : Fin n × Fin n) : p ∈ G.XSet ↔ G.X p.1 = p.2 := by
  simp [XSet_def]

/-- The square `(c, r)` contains an `O` marking exactly when `G.O c = r`. -/
theorem mk_mem_OSet (c r : Fin n) : (c, r) ∈ G.OSet ↔ G.O c = r := by
  simp [OSet_def]

/-- The square `(c, r)` contains an `X` marking exactly when `G.X c = r`. -/
theorem mk_mem_XSet (c r : Fin n) : (c, r) ∈ G.XSet ↔ G.X c = r := by
  simp [XSet_def]

/-- A grid diagram has exactly `n` `O` markings. -/
@[simp]
theorem card_OSet : G.OSet.card = n := by
  simp [OSet_def]

/-- A grid diagram has exactly `n` `X` markings. -/
@[simp]
theorem card_XSet : G.XSet.card = n := by
  simp [XSet_def]

/-- The `O` and `X` marking sets of a grid diagram are disjoint. -/
theorem disjoint_OSet_XSet : Disjoint G.OSet G.XSet := by
  rw [OSet_def, XSet_def, GridState.disjoint_pointSet_iff]
  exact G.disjoint

/-- Relabel the rows of a grid diagram by relabeling both marking states. -/
@[simps O X]
def relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelRows ρ
  X := G.X.relabelRows ρ
  disjoint := by
    intro c h
    exact G.disjoint c (ρ.injective h)

/-- Relabel the columns of a grid diagram by relabeling both marking states. -/
@[simps O X]
def relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelColumns κ
  X := G.X.relabelColumns κ
  disjoint := by
    intro c h
    exact G.disjoint (κ.symm c) h

/-- Row relabeling evaluates on the `O` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_O_apply (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelRows ρ).O c = ρ (G.O c) :=
  rfl

/-- Row relabeling evaluates on the `X` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_X_apply (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelRows ρ).X c = ρ (G.X c) :=
  rfl

/-- Column relabeling evaluates on the `O` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_O_apply (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelColumns κ).O c = G.O (κ.symm c) :=
  rfl

/-- Column relabeling evaluates on the `X` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_X_apply (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelColumns κ).X c = G.X (κ.symm c) :=
  rfl

/-- Row relabeling transports the `O` marking set by the row permutation. -/
theorem mem_OSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).OSet ↔ (p.1, ρ.symm p.2) ∈ G.OSet := by
  rw [OSet_def, OSet_def]
  exact GridState.mem_pointSet_relabelRows ρ G.O p

/-- Row relabeling transports the `X` marking set by the row permutation. -/
theorem mem_XSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).XSet ↔ (p.1, ρ.symm p.2) ∈ G.XSet := by
  rw [XSet_def, XSet_def]
  exact GridState.mem_pointSet_relabelRows ρ G.X p

/-- Column relabeling transports the `O` marking set by the column permutation. -/
theorem mem_OSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).OSet ↔ (κ.symm p.1, p.2) ∈ G.OSet := by
  simp [OSet_def]

/-- Column relabeling transports the `X` marking set by the column permutation. -/
theorem mem_XSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).XSet ↔ (κ.symm p.1, p.2) ∈ G.XSet := by
  simp [XSet_def]

/-- A set of squares with rows relabeled back avoids the original X-markings exactly when
the set avoids the row-relabeled diagram's X-markings. -/
theorem disjoint_map_relabelRows_XSet_iff (ρ : Equiv.Perm (Fin n))
    (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map ((Equiv.refl (Fin n)).prodCongr ρ.symm).toEmbedding) G.XSet ↔
      Disjoint S (G.relabelRows ρ).XSet := by
  simpa only [XSet, relabelRows_X] using
    G.X.disjoint_map_relabelRows_pointSet_iff ρ S

/-- A set of squares relabeled back avoids the original X-markings exactly when the set
avoids the relabeled diagram's X-markings. -/
theorem disjoint_map_relabelColumns_XSet_iff (κ : Equiv.Perm (Fin n))
    (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map (κ.symm.prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet ↔
      Disjoint S (G.relabelColumns κ).XSet := by
  simpa only [XSet, relabelColumns_X] using
    G.X.disjoint_map_relabelColumns_pointSet_iff κ S

/-- Swapping two rows in a grid diagram. -/
def swapRows (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid diagram. -/
def swapColumns (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelColumns (Equiv.swap a b)

/-- The `O` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_O (a b : Fin n) : (G.swapRows a b).O = G.O.swapRows a b :=
  rfl

/-- The `X` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_X (a b : Fin n) : (G.swapRows a b).X = G.X.swapRows a b :=
  rfl

/-- The `O` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_O (a b : Fin n) : (G.swapColumns a b).O = G.O.swapColumns a b :=
  rfl

/-- The `X` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_X (a b : Fin n) : (G.swapColumns a b).X = G.X.swapColumns a b :=
  rfl

/-- Row swaps transport the `O` marking set by the row transposition. -/
theorem mem_OSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).OSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.OSet := by
  simpa [swapRows] using G.mem_OSet_relabelRows (Equiv.swap a b) p

/-- Row swaps transport the `X` marking set by the row transposition. -/
theorem mem_XSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).XSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.XSet := by
  simpa [swapRows] using G.mem_XSet_relabelRows (Equiv.swap a b) p

/-- Column swaps transport the `O` marking set by the column transposition. -/
theorem mem_OSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).OSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.OSet := by
  simp [swapColumns]

/-- Column swaps transport the `X` marking set by the column transposition. -/
theorem mem_XSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).XSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.XSet := by
  simp [swapColumns]

/-- A set of squares with rows swapped back avoids the original X-markings exactly when
the set avoids the row-swapped diagram's X-markings. -/
theorem disjoint_map_swapRows_XSet_iff (a b : Fin n) (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map ((Equiv.refl (Fin n)).prodCongr (Equiv.swap a b)).toEmbedding) G.XSet ↔
      Disjoint S (G.swapRows a b).XSet := by
  simpa only [swapRows, Equiv.symm_swap] using
    G.disjoint_map_relabelRows_XSet_iff (Equiv.swap a b) S

/-- A set of squares swapped back avoids the original X-markings exactly when the set
avoids the swapped diagram's X-markings. -/
theorem disjoint_map_swapColumns_XSet_iff (a b : Fin n) (S : Finset (Fin n × Fin n)) :
    Disjoint (S.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet ↔
      Disjoint S (G.swapColumns a b).XSet := by
  simpa only [swapColumns, Equiv.symm_swap] using
    G.disjoint_map_relabelColumns_XSet_iff (Equiv.swap a b) S

/-- Swapping the same pair of rows twice is the identity on grid diagrams. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) : (G.swapRows a b).swapRows a b = G := by
  ext c <;> simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid diagrams. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) : (G.swapColumns a b).swapColumns a b = G := by
  ext c <;> simp [swapColumns]

/-- Relabeling rows by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelRows_refl : G.relabelRows (Equiv.refl (Fin n)) = G :=
  rfl

/-- Relabeling columns by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelColumns_refl : G.relabelColumns (Equiv.refl (Fin n)) = G :=
  rfl

/-- Successive row relabelings compose on grid diagrams. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelRows σ = G.relabelRows (ρ.trans σ) :=
  rfl

/-- Successive column relabelings compose on grid diagrams. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).relabelColumns τ = G.relabelColumns (κ.trans τ) :=
  rfl

/-- Row and column relabeling commute on grid diagrams. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelColumns κ = (G.relabelColumns κ).relabelRows ρ :=
  rfl

/-- The diagonal reflection of a grid diagram, reflecting both the `O` and `X` marking states.

Reflection across the main diagonal is a bijection of squares, so it preserves the condition
that no square carries both markings. -/
@[simps O X]
def transpose (G : GridDiagram n) : GridDiagram n where
  O := G.O.transpose
  X := G.X.transpose
  disjoint := by
    intro c h
    simp only [GridState.transpose_apply] at h
    refine G.disjoint (G.O.toPerm.symm c) ?_
    rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]

/-- The diagonal reflection is an involution on grid diagrams. -/
@[simp]
theorem transpose_transpose : G.transpose.transpose = G :=
  rfl

/-- Reflecting after a row relabeling is the same as column relabeling after reflecting. -/
@[simp]
theorem relabelRows_transpose (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).transpose = G.transpose.relabelColumns ρ :=
  rfl

/-- Reflecting after a column relabeling is the same as row relabeling after reflecting. -/
@[simp]
theorem relabelColumns_transpose (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).transpose = G.transpose.relabelRows κ :=
  rfl

/-- Reflecting after a row swap is the same as the corresponding column swap after reflecting. -/
@[simp]
theorem swapRows_transpose (a b : Fin n) :
    (G.swapRows a b).transpose = G.transpose.swapColumns a b :=
  rfl

/-- Reflecting after a column swap is the same as the corresponding row swap after reflecting. -/
@[simp]
theorem swapColumns_transpose (a b : Fin n) :
    (G.swapColumns a b).transpose = G.transpose.swapRows a b :=
  rfl

/-- The `O`-marking set of the reflected diagram is the diagonal reflection of the original
`O`-marking set. -/
theorem transpose_OSet : G.transpose.OSet = G.OSet.image Prod.swap := by
  rw [OSet_def, OSet_def, transpose_O, GridState.transpose_pointSet]

/-- The `X`-marking set of the reflected diagram is the diagonal reflection of the original
`X`-marking set. -/
theorem transpose_XSet : G.transpose.XSet = G.XSet.image Prod.swap := by
  rw [XSet_def, XSet_def, transpose_X, GridState.transpose_pointSet]

/-- The marking swap of a grid diagram, obtained by exchanging the `O`- and `X`-marking states.

The defining no-double-marking condition is symmetric in the two marking states, so the swap is
again a grid diagram. -/
@[simps O X]
def swapMarkings (G : GridDiagram n) : GridDiagram n where
  O := G.X
  X := G.O
  disjoint c := (G.disjoint c).symm

/-- The `O`-marking set of the marking swap is the original `X`-marking set. -/
@[simp]
theorem swapMarkings_OSet : G.swapMarkings.OSet = G.XSet := rfl

/-- The `X`-marking set of the marking swap is the original `O`-marking set. -/
@[simp]
theorem swapMarkings_XSet : G.swapMarkings.XSet = G.OSet := rfl

/-- The marking swap is an involution. -/
@[simp]
theorem swapMarkings_swapMarkings : G.swapMarkings.swapMarkings = G :=
  rfl

/-- Row relabeling commutes with exchanging the two marking states. -/
@[simp]
theorem relabelRows_swapMarkings (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).swapMarkings = G.swapMarkings.relabelRows ρ :=
  rfl

/-- Column relabeling commutes with exchanging the two marking states. -/
@[simp]
theorem relabelColumns_swapMarkings (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).swapMarkings = G.swapMarkings.relabelColumns κ :=
  rfl

/-- Row swaps commute with exchanging the two marking states. -/
@[simp]
theorem swapRows_swapMarkings (a b : Fin n) :
    (G.swapRows a b).swapMarkings = G.swapMarkings.swapRows a b :=
  rfl

/-- Column swaps commute with exchanging the two marking states. -/
@[simp]
theorem swapColumns_swapMarkings (a b : Fin n) :
    (G.swapColumns a b).swapMarkings = G.swapMarkings.swapColumns a b :=
  rfl

/-- The marking swap commutes with the diagonal reflection of a grid diagram. -/
@[simp]
theorem swapMarkings_transpose : G.swapMarkings.transpose = G.transpose.swapMarkings :=
  rfl

end GridDiagram

end TauCeti
