/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import TauCeti.Probability.Kernel.Randomization

/-!
# A common conditional cell kernel for exchangeable arrays

Fix two sequences of hidden row and column indices, `e` and `f`. A visible cell `(i,j)` is
observed together with the hidden block, its row against the hidden columns, and its column
against the hidden rows. `cellContext e f i j` packages these three observations in the same
measurable space for every visible cell.

For a separately exchangeable array law, the joint law of this context and the cell is
independent of the choice of `i` and `j`, as long as they lie outside the two hidden index
ranges. In particular, Mathlib's canonical `condDistrib` yields **one and the same kernel**
for every visible cell. This is the kernel that a cell-noise randomization can use after the
hidden block and the row and column strips have been generated. The statement is about the
one-cell conditional law; conditional independence of different visible cells is a separate
input to their simultaneous coding.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

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

/-- The joint law of a cell and its hidden context is invariant under reindexing that fixes the
hidden rows and columns pointwise. -/
theorem SeparatelyExchangeable.map_cellContext_cell_eq_of_fixed
    {ρ : Measure (ℕ × ℕ → α)} (hρ : SeparatelyExchangeable ρ fun p x => x p)
    (e f : ℕ → ℕ) (i j : ℕ) (rowPerm colPerm : Equiv.Perm ℕ)
    (he : ∀ a, rowPerm (e a) = e a) (hf : ∀ b, colPerm (f b) = f b) :
    ρ.map (fun x => (cellContext e f (rowPerm i) (colPerm j) x,
      x (rowPerm i, colPerm j))) =
      ρ.map (fun x => (cellContext e f i j x, x (i, j))) := by
  have hread : Measurable (fun x : ℕ × ℕ → α => (cellContext e f i j x, x (i, j))) :=
    (measurable_cellContext e f i j).prodMk (measurable_pi_apply (i, j))
  have h := hρ.map_comp (fun p => (measurable_pi_apply p).aemeasurable)
    rowPerm colPerm hread
  have hfun :
      (fun x : ℕ × ℕ → α => (cellContext e f (rowPerm i) (colPerm j) x,
        x (rowPerm i, colPerm j))) =
        (fun x => (cellContext e f i j (pairReindex rowPerm colPerm x),
          (pairReindex rowPerm colPerm x) (i, j))) := by
    funext x
    apply Prod.ext (cellContext_pairReindex e f i j rowPerm colPerm he hf x).symm
    simp only [pairReindex_apply]
  rw [hfun]
  simpa only [pairReindex_def] using h

/-- All visible cells have the same joint law with their hidden block and adjacent hidden
strips. Neither hidden enumeration must be injective; the only requirement is that neither
visible index occurs in its corresponding hidden range. -/
theorem SeparatelyExchangeable.map_cellContext_cell_eq
    {ρ : Measure (ℕ × ℕ → α)} (hρ : SeparatelyExchangeable ρ fun p x => x p)
    (e f : ℕ → ℕ) {i i' j j' : ℕ}
    (hi : i ∉ Set.range e) (hi' : i' ∉ Set.range e)
    (hj : j ∉ Set.range f) (hj' : j' ∉ Set.range f) :
    ρ.map (fun x => (cellContext e f i' j' x, x (i', j'))) =
      ρ.map (fun x => (cellContext e f i j x, x (i, j))) := by
  have he (a : ℕ) : Equiv.swap i i' (e a) = e a :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hi ⟨a, h⟩) (fun h => hi' ⟨a, h⟩)
  have hf (b : ℕ) : Equiv.swap j j' (f b) = f b :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hj ⟨b, h⟩) (fun h => hj' ⟨b, h⟩)
  simpa only [Equiv.swap_apply_left] using
    hρ.map_cellContext_cell_eq_of_fixed e f i j (Equiv.swap i i') (Equiv.swap j j') he hf

/-- The regular conditional law of a visible cell given its hidden block and adjacent strips is
the same kernel at every visible position. The equality is of Mathlib's canonical kernel
versions, so it holds everywhere on the context space. -/
theorem SeparatelyExchangeable.condDistrib_cellContext_eq
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : SeparatelyExchangeable ρ fun p x => x p)
    (e f : ℕ → ℕ) {i i' j j' : ℕ}
    (hi : i ∉ Set.range e) (hi' : i' ∉ Set.range e)
    (hj : j ∉ Set.range f) (hj' : j' ∉ Set.range f) :
    condDistrib (fun x : ℕ × ℕ → α => x (i', j')) (cellContext e f i' j') ρ =
      condDistrib (fun x : ℕ × ℕ → α => x (i, j)) (cellContext e f i j) ρ := by
  -- `condDistrib` chooses its kernel from the joint law, which the preceding theorem identifies.
  simp only [condDistrib]
  simp only [hρ.map_cellContext_cell_eq e f hi hi' hj hj']

/-- **A single measurable cell coding realizes every visible cell's conditional law.** Given a
reference visible cell, the canonical conditional kernel of that cell can be randomized by a
uniform variable. The common-kernel theorem makes the same coding work at every other visible
position, with its own hidden block and adjacent strips as input. This statement concerns each
cell's conditional law separately; it does not assert independence of the randomizations. -/
theorem SeparatelyExchangeable.exists_common_cell_coding
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : SeparatelyExchangeable ρ fun p x => x p)
    (e f : ℕ → ℕ) {i₀ j₀ : ℕ}
    (hi₀ : i₀ ∉ Set.range e) (hj₀ : j₀ ∉ Set.range f) :
    ∃ g : (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) → I → α,
      Measurable (Function.uncurry g) ∧
        ∀ (i j : ℕ), i ∉ Set.range e → j ∉ Set.range f →
          ∀ z, (volume : Measure I).map (g z) =
            condDistrib (fun x : ℕ × ℕ → α => x (i, j)) (cellContext e f i j) ρ z := by
  obtain ⟨g, hg, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval
    (condDistrib (fun x : ℕ × ℕ → α => x (i₀, j₀)) (cellContext e f i₀ j₀) ρ)
  refine ⟨g, hg, ?_⟩
  intro i j hi hj z
  rw [hρ.condDistrib_cellContext_eq e f hi₀ hi hj₀ hj]
  exact hmap z

end TauCeti.Probability

end

end
