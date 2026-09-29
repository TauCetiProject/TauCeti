/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Strip.Cell.Context
public import TauCeti.GroupTheory.Perm.Basic

/-!
# A common conditional law for off-diagonal pairs

For a jointly exchangeable array, the entries at `(i,j)` and `(j,i)` must be generated together:
the two entries can be dependent, and the Aldous--Hoover coding gives their unordered pair a
single cell-noise variable. Fix a hidden sequence of vertices. The context of an ordered pair of
visible, distinct vertices records the hidden block and both vertices' strips against it.

Every such ordered pair has the same joint law with its context. Hence Mathlib's canonical
conditional distribution gives one kernel for all off-diagonal pairs, and a single measurable
randomization of that kernel works at every visible pair. This is the pair-valued counterpart of
`SeparatelyExchangeable.exists_common_cell_coding`; the diagonal has a different orbit and must
be treated separately. The randomization statement concerns each pair's conditional law; it does
not yet assert conditional independence between different pairs.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

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

/-- Joint exchangeability transports the law of a pair and its hidden context along any
permutation that fixes the hidden vertices. -/
theorem JointlyExchangeable.map_offDiagonalPairContext_entries_eq_of_fixed
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyExchangeable ρ fun p x => x p)
    (e : ℕ → ℕ) (i j : ℕ) (perm : Equiv.Perm ℕ) (he : ∀ a, perm (e a) = e a) :
    ρ.map (fun x => (offDiagonalPairContext e (perm i) (perm j) x,
      (x (perm i, perm j), x (perm j, perm i)))) =
    ρ.map (fun x => (offDiagonalPairContext e i j x, (x (i, j), x (j, i)))) := by
  have hread : Measurable (fun x : ℕ × ℕ → α =>
      (offDiagonalPairContext e i j x, (x (i, j), x (j, i)))) :=
    (measurable_offDiagonalPairContext e i j).prodMk
      ((measurable_pi_apply (i, j)).prodMk (measurable_pi_apply (j, i)))
  have h := hρ.map_comp (fun p => (measurable_pi_apply p).aemeasurable) perm hread
  have hfun : (fun x : ℕ × ℕ → α =>
      (offDiagonalPairContext e (perm i) (perm j) x,
        (x (perm i, perm j), x (perm j, perm i)))) =
      (fun x : ℕ × ℕ → α =>
        (offDiagonalPairContext e i j (pairReindex perm perm x),
          ((pairReindex perm perm x) (i, j), (pairReindex perm perm x) (j, i)))) := by
    funext x
    apply Prod.ext
    · exact (offDiagonalPairContext_pairReindex e i j perm he x).symm
    · simp only [pairReindex_apply]
  rw [hfun]
  simpa only [pairReindex_def, Measure.map_id'] using h

/-- The joint law of a hidden context and its two directed off-diagonal entries is independent
of the visible ordered pair, provided its vertices are distinct. -/
theorem JointlyExchangeable.map_offDiagonalPairContext_entries_eq
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyExchangeable ρ fun p x => x p)
    (e : ℕ → ℕ) {i j i' j' : ℕ} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    (hi' : i' ∉ Set.range e) (hj' : j' ∉ Set.range e) :
    ρ.map (fun x => (offDiagonalPairContext e i' j' x, (x (i', j'), x (j', i')))) =
    ρ.map (fun x => (offDiagonalPairContext e i j x, (x (i, j), x (j, i)))) := by
  obtain ⟨perm, he, hpermi, hpermj⟩ :=
    exists_pair_perm_fixed (Set.range e) hij hi'j' hi hj hi' hj'
  have he' (a : ℕ) : perm (e a) = e a := he (e a) ⟨a, rfl⟩
  simpa only [hpermi, hpermj] using
    hρ.map_offDiagonalPairContext_entries_eq_of_fixed e i j perm he'

/-- All off-diagonal visible pairs have the same canonical conditional kernel, including its
values on contexts outside the support of the observed law. -/
theorem JointlyExchangeable.condDistrib_offDiagonalPairContext_eq
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : JointlyExchangeable ρ fun p x => x p)
    (e : ℕ → ℕ) {i j i' j' : ℕ} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    (hi' : i' ∉ Set.range e) (hj' : j' ∉ Set.range e) :
    condDistrib (fun x : ℕ × ℕ → α => (x (i', j'), x (j', i')))
      (offDiagonalPairContext e i' j') ρ =
    condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
      (offDiagonalPairContext e i j) ρ := by
  simp only [condDistrib]
  simp only [hρ.map_offDiagonalPairContext_entries_eq e hij hi'j' hi hj hi' hj']

/-- One measurable randomization of the common conditional kernel generates either orientation
of every off-diagonal visible pair from its context and a fresh uniform variable. -/
theorem JointlyExchangeable.exists_common_offDiagonalPair_coding
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : JointlyExchangeable ρ fun p x => x p)
    (e : ℕ → ℕ) {i₀ j₀ : ℕ} (h₀ : i₀ ≠ j₀)
    (hi₀ : i₀ ∉ Set.range e) (hj₀ : j₀ ∉ Set.range e) :
    ∃ g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) ×
        (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) → I → α × α,
      Measurable (Function.uncurry g) ∧
        ∀ (i j : ℕ), i ≠ j → i ∉ Set.range e → j ∉ Set.range e →
          ∀ z, (volume : Measure I).map (g z) =
            condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
              (offDiagonalPairContext e i j) ρ z := by
  obtain ⟨g, hg, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval
    (condDistrib (fun x : ℕ × ℕ → α => (x (i₀, j₀), x (j₀, i₀)))
      (offDiagonalPairContext e i₀ j₀) ρ)
  refine ⟨g, hg, ?_⟩
  intro i j hij hi hj z
  rw [hρ.condDistrib_offDiagonalPairContext_eq e h₀ hij hi₀ hj₀ hi hj]
  exact hmap z

end TauCeti.Probability

end

end
