/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array

/-!
# Cell and ordered-pair observations of arrays

A cell context records a hidden block and the row and column strips adjacent to an observed
cell. An ordered-pair context retains the contexts of both directed cells. Its square context
also records the two diagonal entries. These measurable observations supply the conditioning
variables for conditional laws of array entries.

The constructions apply to arbitrary arrays and arbitrary hidden enumerations, without
injectivity, distinctness, or symmetry assumptions. Their coordinate equations, measurability,
vertex-swap identities, and transport under relabellings fixing the hidden indices are provided
here; invariance of their laws requires separate hypotheses on the array law.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

/-! ## Cell contexts -/

/-- The hidden block and the two hidden strips adjacent to cell `(i,j)`. The first component
contains the block and the row strip, and the second contains the column strip. -/
def cellContext (e f : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    ((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α) :=
  ((fun p => x (e p.1, f p.2), fun b => x (i, f b)), fun a => x (e a, j))

omit [MeasurableSpace α] in
@[simp]
theorem cellContext_block_apply (e f : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (cellContext e f i j x).1.1 p = x (e p.1, f p.2) :=
  (rfl)

omit [MeasurableSpace α] in
@[simp]
theorem cellContext_rowStrip_apply (e f : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) (b : ℕ) :
    (cellContext e f i j x).1.2 b = x (i, f b) :=
  (rfl)

omit [MeasurableSpace α] in
@[simp]
theorem cellContext_colStrip_apply (e f : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) (a : ℕ) :
    (cellContext e f i j x).2 a = x (e a, j) :=
  (rfl)

/-- Reading a cell context from an array is measurable. -/
theorem measurable_cellContext (e f : ℕ → ℕ) (i j : ℕ) :
    Measurable (cellContext (α := α) e f i j) :=
  ((Measurable.of_eval fun p => measurable_pi_apply (e p.1, f p.2)).prodMk
    (Measurable.of_eval fun b => measurable_pi_apply (i, f b))).prodMk
      (Measurable.of_eval fun a => measurable_pi_apply (e a, j))

omit [MeasurableSpace α] in
/-- Reindexing while fixing the hidden indices transports the visible cell context to the
context at the reindexed cell. -/
theorem cellContext_pairReindex (e f : ℕ → ℕ) (i j : ℕ)
    (rowPerm colPerm : Equiv.Perm ℕ)
    (he : ∀ a, rowPerm (e a) = e a) (hf : ∀ b, colPerm (f b) = f b)
    (x : ℕ × ℕ → α) :
    cellContext e f i j (pairReindex rowPerm colPerm x) =
      cellContext e f (rowPerm i) (colPerm j) x := by
  simp only [cellContext, pairReindex_apply]
  congr 1
  · congr 1
    · funext p
      rw [he p.1, hf p.2]
    · funext b
      rw [hf b]
  · funext a
    rw [he a]

/-! ## Ordered-pair contexts -/

/-- The hidden block and the two adjacent vertex contexts of an ordered pair of visible
vertices. Both orientations are retained because a jointly exchangeable array need not be
symmetric. -/
def offDiagonalPairContext (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :=
  (cellContext e e i j x, cellContext e e j i x)

omit [MeasurableSpace α] in
/-- The first component is the context of the forward directed cell. -/
@[simp]
theorem offDiagonalPairContext_fst (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    (offDiagonalPairContext e i j x).1 = cellContext e e i j x := by
  simp only [offDiagonalPairContext]

omit [MeasurableSpace α] in
/-- The second component is the context of the reverse directed cell. -/
@[simp]
theorem offDiagonalPairContext_snd (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    (offDiagonalPairContext e i j x).2 = cellContext e e j i x := by
  simp only [offDiagonalPairContext]

omit [MeasurableSpace α] in
/-- Reversing the visible vertices swaps their two directed contexts. -/
theorem offDiagonalPairContext_swap (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    offDiagonalPairContext e j i x = (offDiagonalPairContext e i j x).swap := by
  simp only [offDiagonalPairContext, Prod.swap]

/-- Reading the context of an off-diagonal pair is measurable. -/
theorem measurable_offDiagonalPairContext (e : ℕ → ℕ) (i j : ℕ) :
    Measurable (offDiagonalPairContext (α := α) e i j) :=
  (measurable_cellContext e e i j).prodMk (measurable_cellContext e e j i)

omit [MeasurableSpace α] in
/-- A common relabelling fixing the hidden vertices transports the context of a visible pair. -/
theorem offDiagonalPairContext_pairReindex (e : ℕ → ℕ) (i j : ℕ)
    (perm : Equiv.Perm ℕ) (he : ∀ a, perm (e a) = e a) (x : ℕ × ℕ → α) :
    offDiagonalPairContext e i j (pairReindex perm perm x) =
      offDiagonalPairContext e (perm i) (perm j) x := by
  simp only [offDiagonalPairContext]
  exact Prod.ext (cellContext_pairReindex e e i j perm perm he he x)
    (cellContext_pairReindex e e j i perm perm he he x)

/-! ## Square contexts -/

/-- The square context of the ordered pair `(i, j)` of visible vertices: the contexts of both
directed cells, that is the hidden block and the strips of `i` and of `j` against the hidden
vertices, together with the two diagonal entries `x (i, i)` and `x (j, j)`. When `i` and `j` are
distinct and outside the hidden range, its entries are exactly those of the square spanned by
the hidden vertices and `i`, `j`, other than `(i, j)` and `(j, i)`. -/
def offDiagonalPairSquareContext (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :=
  (offDiagonalPairContext e i j x, (x (i, i), x (j, j)))

omit [MeasurableSpace α] in
/-- The first component of the square context is the context of the two directed cells. -/
@[simp]
theorem offDiagonalPairSquareContext_fst (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    (offDiagonalPairSquareContext e i j x).1 = offDiagonalPairContext e i j x :=
  (rfl)

omit [MeasurableSpace α] in
/-- The second component of the square context is the pair of diagonal entries. -/
@[simp]
theorem offDiagonalPairSquareContext_snd (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    (offDiagonalPairSquareContext e i j x).2 = (x (i, i), x (j, j)) :=
  (rfl)

omit [MeasurableSpace α] in
/-- Reversing the visible vertices swaps both the two directed contexts and the two diagonal
entries of the square context. -/
theorem offDiagonalPairSquareContext_swap (e : ℕ → ℕ) (i j : ℕ) (x : ℕ × ℕ → α) :
    offDiagonalPairSquareContext e j i x =
      Prod.map Prod.swap Prod.swap (offDiagonalPairSquareContext e i j x) := by
  simp only [offDiagonalPairSquareContext, offDiagonalPairContext_swap e i j, Prod.map, Prod.swap]

/-- Reading the square context of an off-diagonal pair is measurable. -/
theorem measurable_offDiagonalPairSquareContext (e : ℕ → ℕ) (i j : ℕ) :
    Measurable (offDiagonalPairSquareContext (α := α) e i j) :=
  (measurable_offDiagonalPairContext e i j).prodMk
    ((measurable_pi_apply (i, i)).prodMk (measurable_pi_apply (j, j)))

omit [MeasurableSpace α] in
/-- A common relabelling fixing the hidden vertices transports the square context of a visible
pair. -/
theorem offDiagonalPairSquareContext_pairReindex (e : ℕ → ℕ) (i j : ℕ)
    (perm : Equiv.Perm ℕ) (he : ∀ a, perm (e a) = e a) (x : ℕ × ℕ → α) :
    offDiagonalPairSquareContext e i j (pairReindex perm perm x) =
      offDiagonalPairSquareContext e (perm i) (perm j) x := by
  simp only [offDiagonalPairSquareContext, offDiagonalPairContext_pairReindex e i j perm he,
    pairReindex_apply]

end TauCeti.Probability
