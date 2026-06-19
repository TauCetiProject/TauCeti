/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic

/-!
# Grid diagrams and grid states

This file starts the grid-combinatorial lane of the Heegaard Floer roadmap. A grid state of
grid number `n` is a wrapper around a permutation of `Fin n`, sending each column to the
unique row occupied by the state in that column. A grid diagram is encoded by two such
permutation graphs, one for the `O` markings and one for the `X` markings, with the condition
that no square contains both markings.

The point-set API records the basic row, column, cardinality, and disjointness facts used
before defining rectangles, empty rectangles, and the grid differential.

## Main definitions

* `TauCeti.GridState`: a grid state with a permutation graph on `Fin n`.
* `TauCeti.GridState.pointSet`: the finite set of occupied squares of a grid state.
* `TauCeti.GridState.relabelRows`, `TauCeti.GridState.relabelColumns`: row and column
  relabelings of grid states.
* `TauCeti.GridState.swapRows`, `TauCeti.GridState.swapColumns`: row and column swaps of
  grid states.
* `TauCeti.GridDiagram`: an `n × n` grid diagram with `O` and `X` markings.
* `TauCeti.GridDiagram.OSet`, `TauCeti.GridDiagram.XSet`: the marking point sets.
* `TauCeti.GridDiagram.relabelRows`, `TauCeti.GridDiagram.relabelColumns`: row and column
  relabelings of grid diagrams.
* `TauCeti.GridDiagram.swapRows`, `TauCeti.GridDiagram.swapColumns`: row and column swaps of
  grid diagrams.

## References

This supplies the first prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.1, "Grid diagrams and grid states". The
encoding follows the standard grid-diagram convention from Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 3: one `O` and one `X` marking in each row and column,
and a grid state is one point in each row and column.
-/

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

/-- Apply a grid state to a column to get its occupied row. -/
instance : CoeFun (GridState n) fun _ => Fin n → Fin n where
  coe x := x.toPerm

/-- Grid states are extensional in their column-to-row functions. -/
@[ext]
theorem ext {x y : GridState n} (h : ∀ c : Fin n, x c = y c) : x = y := by
  cases x
  cases y
  congr
  ext c
  exact congrArg Fin.val (h c)

/-- The finite set of occupied squares of a grid state. The first coordinate is the column and
the second coordinate is the row. -/
def pointSet (x : GridState n) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun c => (c, x c)

/-- Membership in the point set of a grid state is the graph condition for its permutation. -/
@[simp]
theorem mem_pointSet (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.pointSet ↔ x p.1 = p.2 := by
  constructor
  · intro hp
    rw [pointSet] at hp
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hp
    rw [← Prod.mk.inj hc |>.1]
    exact Prod.mk.inj hc |>.2
  · intro hp
    rw [pointSet]
    exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, by ext <;> simp [hp]⟩

/-- The square `(c, r)` lies in a grid state's point set exactly when `x c = r`. -/
@[simp]
theorem mk_mem_pointSet (x : GridState n) (c r : Fin n) :
    (c, r) ∈ x.pointSet ↔ x c = r := by
  simp

/-- The point set of a grid state has exactly `n` occupied squares. -/
@[simp]
theorem card_pointSet (x : GridState n) : x.pointSet.card = n := by
  rw [pointSet, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    exact Prod.mk.inj hab |>.1

/-- A grid state has a unique occupied row in each column. -/
theorem existsUnique_row_of_column (x : GridState n) (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ x.pointSet := by
  refine ⟨x c, by simp, ?_⟩
  intro r hr
  exact ((mk_mem_pointSet x c r).mp hr).symm

/-- A grid state has a unique occupied column in each row. -/
theorem existsUnique_column_of_row (x : GridState n) (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ x.pointSet := by
  refine ⟨x.toPerm.symm r, by simp, ?_⟩
  intro c hc
  exact x.toPerm.injective (by simpa using hc)

/-- Point sets of grid states are equal exactly when the underlying permutations are equal. -/
@[simp]
theorem pointSet_inj {x y : GridState n} : x.pointSet = y.pointSet ↔ x = y := by
  constructor
  · intro h
    ext c
    have hx : (c, x c) ∈ y.pointSet := by simpa [h] using mk_mem_pointSet x c (x c) |>.mpr rfl
    exact congrArg Fin.val ((mk_mem_pointSet y c (x c)).mp hx).symm
  · intro h
    simp [h]

/-- A square lies in both state point sets exactly when both state permutations send its
column to its row. -/
@[simp]
theorem mem_pointSet_inter (x y : GridState n) (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ y.pointSet ↔ x p.1 = p.2 ∧ y p.1 = p.2 := by
  simp

/-- Two grid states have disjoint point sets exactly when they disagree in every column. -/
theorem disjoint_pointSet_iff (x y : GridState n) :
    Disjoint x.pointSet y.pointSet ↔ ∀ c : Fin n, x c ≠ y c := by
  rw [Finset.disjoint_iff_ne]
  constructor
  · intro h c hxy
    exact h (c, x c) (by simp) (c, x c) (by simp [hxy]) rfl
  · intro h p hpX q hpY hpq
    subst hpq
    exact h p.1 ((mem_pointSet x p).mp hpX |>.trans ((mem_pointSet y p).mp hpY).symm)

/-- Relabel the rows of a grid state by a permutation of `Fin n`.

If `ρ` is the row permutation, the point in column `c` moves from row `x c` to row
`ρ (x c)`. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => ρ (x c)
      invFun := fun r => x.toPerm.symm (ρ.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

/-- Relabel the columns of a grid state by a permutation of `Fin n`.

The point in the old column `c` appears in the new column `κ c`, so the row in a new column
`c` is read from the old column `κ.symm c`. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => x (κ.symm c)
      invFun := fun r => κ (x.toPerm.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

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
theorem relabelRows_refl (x : GridState n) : x.relabelRows (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Relabeling columns by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelColumns_refl (x : GridState n) :
    x.relabelColumns (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Successive row relabelings compose. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelRows σ = x.relabelRows (ρ.trans σ) := by
  ext c
  simp

/-- Successive column relabelings compose. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).relabelColumns τ = x.relabelColumns (κ.trans τ) := by
  ext c
  simp

/-- Row and column relabeling commute on grid states. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelColumns κ = (x.relabelColumns κ).relabelRows ρ := by
  ext c
  simp

/-- Membership in the point set after a row relabeling. -/
@[simp]
theorem mem_pointSet_relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n)
    (p : Fin n × Fin n) :
    p ∈ (x.relabelRows ρ).pointSet ↔ (p.1, ρ.symm p.2) ∈ x.pointSet := by
  simp only [mem_pointSet, relabelRows_apply]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Membership in the point set after a column relabeling. -/
@[simp]
theorem mem_pointSet_relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n)
    (p : Fin n × Fin n) :
    p ∈ (x.relabelColumns κ).pointSet ↔ (κ.symm p.1, p.2) ∈ x.pointSet := by
  simp

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

/-- Row swaps transport the point set by the row transposition. -/
@[simp]
theorem mem_pointSet_swapRows (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapRows a b).pointSet ↔ (p.1, Equiv.swap a b p.2) ∈ x.pointSet := by
  simpa [swapRows] using GridState.mem_pointSet_relabelRows (Equiv.swap a b) x p

/-- Column swaps transport the point set by the column transposition. -/
@[simp]
theorem mem_pointSet_swapColumns (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapColumns a b).pointSet ↔ (Equiv.swap a b p.1, p.2) ∈ x.pointSet := by
  simp [swapColumns]

/-- Swapping the same pair of rows twice is the identity on grid states. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).swapRows a b = x := by
  ext c
  simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid states. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp [swapColumns]

end GridState

/-- An `n × n` grid diagram, encoded by the `O`-marking and `X`-marking permutation graphs.

The permutation fields enforce one `O` and one `X` in each row and column. The `disjoint`
field says no square contains both markings. -/
@[ext]
structure GridDiagram (n : ℕ) where
  /-- The `O` marking in each column, encoded by its row. -/
  O : GridState n
  /-- The `X` marking in each column, encoded by its row. -/
  X : GridState n
  /-- No square contains both an `O` marking and an `X` marking. -/
  disjoint : ∀ c : Fin n, O c ≠ X c

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The finite set of `O` markings of a grid diagram. The first coordinate is the column and
the second coordinate is the row. -/
def OSet : Finset (Fin n × Fin n) :=
  G.O.pointSet

/-- The finite set of `X` markings of a grid diagram. The first coordinate is the column and
the second coordinate is the row. -/
def XSet : Finset (Fin n × Fin n) :=
  G.X.pointSet

/-- Membership in the `O`-marking set is the graph condition for the `O` permutation. -/
@[simp]
theorem mem_OSet (p : Fin n × Fin n) : p ∈ G.OSet ↔ G.O p.1 = p.2 := by
  simp [OSet]

/-- Membership in the `X`-marking set is the graph condition for the `X` permutation. -/
@[simp]
theorem mem_XSet (p : Fin n × Fin n) : p ∈ G.XSet ↔ G.X p.1 = p.2 := by
  simp [XSet]

/-- The square `(c, r)` contains an `O` marking exactly when `G.O c = r`. -/
@[simp]
theorem mk_mem_OSet (c r : Fin n) : (c, r) ∈ G.OSet ↔ G.O c = r := by
  simp [OSet]

/-- The square `(c, r)` contains an `X` marking exactly when `G.X c = r`. -/
@[simp]
theorem mk_mem_XSet (c r : Fin n) : (c, r) ∈ G.XSet ↔ G.X c = r := by
  simp [XSet]

/-- A grid diagram has exactly `n` `O` markings. -/
@[simp]
theorem card_OSet : G.OSet.card = n := by
  simp [OSet]

/-- A grid diagram has exactly `n` `X` markings. -/
@[simp]
theorem card_XSet : G.XSet.card = n := by
  simp [XSet]

/-- A grid diagram has a unique `O` marking in each column. -/
theorem existsUnique_ORow_of_column (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ G.OSet := by
  rw [OSet]
  exact G.O.existsUnique_row_of_column c

/-- A grid diagram has a unique `X` marking in each column. -/
theorem existsUnique_XRow_of_column (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ G.XSet := by
  rw [XSet]
  exact G.X.existsUnique_row_of_column c

/-- A grid diagram has a unique `O` marking in each row. -/
theorem existsUnique_OColumn_of_row (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ G.OSet := by
  rw [OSet]
  exact G.O.existsUnique_column_of_row r

/-- A grid diagram has a unique `X` marking in each row. -/
theorem existsUnique_XColumn_of_row (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ G.XSet := by
  rw [XSet]
  exact G.X.existsUnique_column_of_row r

/-- The `O` and `X` marking sets of a grid diagram are disjoint. -/
theorem disjoint_OSet_XSet : Disjoint G.OSet G.XSet := by
  rw [OSet, XSet, GridState.disjoint_pointSet_iff]
  exact G.disjoint

/-- No square contains both an `O` marking and an `X` marking. -/
theorem not_mem_OSet_and_mem_XSet (p : Fin n × Fin n) : ¬ (p ∈ G.OSet ∧ p ∈ G.XSet) := by
  intro hp
  exact Finset.disjoint_left.mp G.disjoint_OSet_XSet hp.1 hp.2

/-- A square with an `O` marking does not contain an `X` marking. -/
theorem not_mem_XSet_of_mem_OSet {p : Fin n × Fin n} (hp : p ∈ G.OSet) : p ∉ G.XSet := by
  intro hpX
  exact G.not_mem_OSet_and_mem_XSet p ⟨hp, hpX⟩

/-- A square with an `X` marking does not contain an `O` marking. -/
theorem not_mem_OSet_of_mem_XSet {p : Fin n × Fin n} (hp : p ∈ G.XSet) : p ∉ G.OSet := by
  intro hpO
  exact G.not_mem_OSet_and_mem_XSet p ⟨hpO, hp⟩

/-- Relabel the rows of a grid diagram by relabeling both marking states. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelRows ρ
  X := G.X.relabelRows ρ
  disjoint := by
    intro c h
    exact G.disjoint c (ρ.injective h)

/-- Relabel the columns of a grid diagram by relabeling both marking states. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelColumns κ
  X := G.X.relabelColumns κ
  disjoint := by
    intro c h
    exact G.disjoint (κ.symm c) h

/-- The `O` marking state of a row-relabeled grid diagram. -/
@[simp]
theorem relabelRows_O (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).O = G.O.relabelRows ρ :=
  rfl

/-- The `X` marking state of a row-relabelled grid diagram. -/
@[simp]
theorem relabelRows_X (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).X = G.X.relabelRows ρ :=
  rfl

/-- The `O` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_O (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).O = G.O.relabelColumns κ :=
  rfl

/-- The `X` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_X (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).X = G.X.relabelColumns κ :=
  rfl

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
@[simp]
theorem mem_OSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).OSet ↔ (p.1, ρ.symm p.2) ∈ G.OSet := by
  rw [OSet, OSet]
  exact GridState.mem_pointSet_relabelRows ρ G.O p

/-- Row relabeling transports the `X` marking set by the row permutation. -/
@[simp]
theorem mem_XSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).XSet ↔ (p.1, ρ.symm p.2) ∈ G.XSet := by
  rw [XSet, XSet]
  exact GridState.mem_pointSet_relabelRows ρ G.X p

/-- Column relabeling transports the `O` marking set by the column permutation. -/
@[simp]
theorem mem_OSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).OSet ↔ (κ.symm p.1, p.2) ∈ G.OSet := by
  simp [OSet]

/-- Column relabeling transports the `X` marking set by the column permutation. -/
@[simp]
theorem mem_XSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).XSet ↔ (κ.symm p.1, p.2) ∈ G.XSet := by
  simp [XSet]

/-- Swapping two rows in a grid diagram. -/
def swapRows (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid diagram. -/
def swapColumns (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelColumns (Equiv.swap a b)

/-- The `O` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_O (a b : Fin n) :
    (G.swapRows a b).O = G.O.swapRows a b :=
  rfl

/-- The `X` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_X (a b : Fin n) :
    (G.swapRows a b).X = G.X.swapRows a b :=
  rfl

/-- The `O` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_O (a b : Fin n) :
    (G.swapColumns a b).O = G.O.swapColumns a b :=
  rfl

/-- The `X` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_X (a b : Fin n) :
    (G.swapColumns a b).X = G.X.swapColumns a b :=
  rfl

/-- Row swaps transport the `O` marking set by the row transposition. -/
@[simp]
theorem mem_OSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).OSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.OSet := by
  simpa [swapRows] using G.mem_OSet_relabelRows (Equiv.swap a b) p

/-- Row swaps transport the `X` marking set by the row transposition. -/
@[simp]
theorem mem_XSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).XSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.XSet := by
  simpa [swapRows] using G.mem_XSet_relabelRows (Equiv.swap a b) p

/-- Column swaps transport the `O` marking set by the column transposition. -/
@[simp]
theorem mem_OSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).OSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.OSet := by
  simp [swapColumns]

/-- Column swaps transport the `X` marking set by the column transposition. -/
@[simp]
theorem mem_XSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).XSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.XSet := by
  simp [swapColumns]

/-- Swapping the same pair of rows twice is the identity on grid diagrams. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) :
    (G.swapRows a b).swapRows a b = G := by
  ext c <;> simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid diagrams. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) :
    (G.swapColumns a b).swapColumns a b = G := by
  ext c <;> simp [swapColumns]

/-- Relabeling rows by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelRows_refl : G.relabelRows (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Relabeling columns by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelColumns_refl : G.relabelColumns (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Successive row relabelings compose on grid diagrams. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelRows σ = G.relabelRows (ρ.trans σ) := by
  ext c <;> simp

/-- Successive column relabelings compose on grid diagrams. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).relabelColumns τ = G.relabelColumns (κ.trans τ) := by
  ext c <;> simp

/-- Row and column relabeling commute on grid diagrams. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelColumns κ = (G.relabelColumns κ).relabelRows ρ := by
  ext c <;> simp [GridState.relabelRows_relabelColumns]

end GridDiagram

end TauCeti
