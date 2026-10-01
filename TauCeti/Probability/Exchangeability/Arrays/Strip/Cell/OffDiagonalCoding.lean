/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Strip.Cell.JointPair
public import Mathlib.Probability.Independence.Conditional
import TauCeti.MeasureTheory.Constructions.ProdProjective
import TauCeti.MeasureTheory.Measure.MapIte
import TauCeti.MeasureTheory.MeasurableSpace.Restrict
import TauCeti.Probability.Exchangeability.Arrays.Block.Independence
import TauCeti.Probability.Independence.Conditional
import TauCeti.Probability.Kernel.ConditionalRandomization

/-!
# One cell kernel codes every off-diagonal pair of a jointly exchangeable array

Fix an infinite set of *hidden* vertices of a jointly exchangeable array, enumerated by `e`; the
other vertices are *visible*. The Aldous–Hoover coding of such an array draws one cell variable per
unordered pair of vertices, so the two entries `x (i, j)` and `x (j, i)` at a visible off-diagonal
pair have to be generated together, from that one variable and the information carried by the
vertices `i` and `j`.

The information a pair sees is its **square context**: the hidden block, the strips of `i` and of
`j` against the hidden vertices, *and the two diagonal entries* `x (i, i)` and `x (j, j)`. These are
exactly the entries of the square spanned by the hidden vertices together with `i` and `j`, other
than the pair itself, so by local conditional independence the pair is conditionally independent of
everything else given its square context. The diagonal entries cannot be left out: no relabelling of
the vertices separates the pair `(i, j), (j, i)` from the diagonal entries at `i` and `j`, since all
four cells live on the same two vertices. In the representation the diagonal is therefore produced
at the vertex level, together with the strips, and the cell variables are indexed by the
off-diagonal unordered pairs, coded here.

Every visible ordered pair has the same joint law with its square context, so Mathlib's canonical
conditional distribution gives **one** kernel for all of them
(`JointlyExchangeable.condDistrib_offDiagonalPairSquareContext_eq` in `Cell/JointPair.lean`, where
the square context `offDiagonalPairSquareContext` is defined). Combined with the conditional
independence of distinct pairs given the crossing strips and the diagonal, the pair layer becomes a
genuine coding: a single measurable function of a square context and a uniform variable generates
every off-diagonal pair at once, each from its own context and its own fresh uniform variable,
jointly with the crossing strips and the diagonal. This is the jointly exchangeable counterpart of
`SeparatelyExchangeable.exists_common_visibleArray_coding`.

A joint Aldous–Hoover coding `f(U, U_vert i, U_vert j, U_cell {i, j})` sees the two vertices of a
pair through their noise, but not which of them comes first, while the pair coding above is
indexed by increasing representatives. The coding is therefore produced in an *oriented* form:
for any measurable set `O` of square contexts, it may be chosen so that whenever exactly one of a
context and its reversal lies in `O`, the coding of the reversed context is the reversed coding.
Off `O` the pair is coded as the reversal of the reversed pair; both codings have the same joint
law with the crossing strips and the diagonal, so switching between them along an event of the
strips and the diagonal changes nothing in law (`TauCeti.MeasureTheory.Measure.map_ite_mem_eq`).

## Main results

* `TauCeti.Probability.JointlyExchangeable.condIndepFun_offDiagonalPair_crossingStripsAndDiagonal`
  — a visible off-diagonal pair is conditionally independent of the crossing strips and the
  diagonal given its square context.
* `TauCeti.Probability.JointlyExchangeable.iCondIndepFun_offDiagonalPairs` — distinct visible
  off-diagonal pairs are conditionally independent given the crossing strips and the diagonal.
* `TauCeti.Probability.JointlyExchangeable.exists_common_offDiagonalPairs_coding` — one common
  coding function, oriented along any measurable set of square contexts, generates every finite
  family of visible off-diagonal pairs from their square contexts and independent uniform
  variables.
* `TauCeti.Probability.JointlyExchangeable.exists_common_offDiagonalArray_coding` — the same coding
  function generates all visible off-diagonal pairs at once, from i.i.d. uniform variables indexed
  by the visible unordered pairs.
* `TauCeti.Probability.offDiagonalPairSquareContextOfStripsAndDiagonal` — reads the square context
  of a pair off the crossing strips and the diagonal alone, so that an assembly generating those
  first can feed the pair coding.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

/-! ## Reading the square context off the crossing strips and the diagonal -/

section Context

variable (e : ℕ → ℕ) (i j : ℕ)

/-- The square context of `(i, j)` read off the crossing strips and the diagonal: every position
the context looks at lies in a hidden row, in a hidden column, or on the diagonal. -/
def offDiagonalPairSquareContextOfStripsAndDiagonal
    (y : (((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
      Set (ℕ × ℕ))) → α) :
    ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α) :=
  ((((fun q => y ⟨(e q.1, e q.2),
        Set.mem_union_left _ (Set.mem_union_right _ ⟨Set.mem_range_self q.1, Set.mem_univ _⟩)⟩,
      fun b => y ⟨(i, e b),
        Set.mem_union_left _ (Set.mem_union_left _ ⟨Set.mem_univ _, Set.mem_range_self b⟩)⟩),
      fun a => y ⟨(e a, j),
        Set.mem_union_left _ (Set.mem_union_right _ ⟨Set.mem_range_self a, Set.mem_univ _⟩)⟩),
    ((fun q => y ⟨(e q.1, e q.2),
        Set.mem_union_left _ (Set.mem_union_right _ ⟨Set.mem_range_self q.1, Set.mem_univ _⟩)⟩,
      fun b => y ⟨(j, e b),
        Set.mem_union_left _ (Set.mem_union_left _ ⟨Set.mem_univ _, Set.mem_range_self b⟩)⟩),
      fun a => y ⟨(e a, i),
        Set.mem_union_left _ (Set.mem_union_right _ ⟨Set.mem_range_self a, Set.mem_univ _⟩)⟩)),
    (y ⟨(i, i), Set.mem_union_right _ (Set.mem_ofPred.2 rfl)⟩,
      y ⟨(j, j), Set.mem_union_right _ (Set.mem_ofPred.2 rfl)⟩))

/-- Reading the square context off the crossing strips and the diagonal is measurable. -/
theorem measurable_offDiagonalPairSquareContextOfStripsAndDiagonal :
    Measurable (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j) :=
  ((((Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
      (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk
        (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk
    (((Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
      (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk
        (Measurable.of_eval fun _ => measurable_pi_apply _))).prodMk
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

omit [MeasurableSpace α] in
/-- Reading the square context off the crossing strips and the diagonal of an array recovers its
square context: this is how a coding of the strips and the diagonal feeds the pair coding. -/
@[simp]
theorem offDiagonalPairSquareContextOfStripsAndDiagonal_comp_domRestrict :
    offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j ∘
        ((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
          Set (ℕ × ℕ)).domRestrict =
      offDiagonalPairSquareContext e i j := by
  funext x
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp only [Function.comp_apply, offDiagonalPairSquareContext_fst, offDiagonalPairContext_fst]
    refine Prod.ext (Prod.ext (funext fun q => ?_) (funext fun b => ?_)) (funext fun a => ?_) <;>
      simp [offDiagonalPairSquareContextOfStripsAndDiagonal]
  · simp only [Function.comp_apply, offDiagonalPairSquareContext_fst, offDiagonalPairContext_snd]
    refine Prod.ext (Prod.ext (funext fun q => ?_) (funext fun b => ?_)) (funext fun a => ?_) <;>
      simp [offDiagonalPairSquareContextOfStripsAndDiagonal]
  · simp only [Function.comp_apply, offDiagonalPairSquareContext_snd]
    rfl

omit [MeasurableSpace α] in
/-- Reading the square context of the reversed pair off the crossing strips and the diagonal swaps
both the two directed contexts and the two diagonal entries. -/
theorem offDiagonalPairSquareContextOfStripsAndDiagonal_swap
    (y : (((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
      Set (ℕ × ℕ))) → α) :
    offDiagonalPairSquareContextOfStripsAndDiagonal e j i y =
      Prod.map Prod.swap Prod.swap (offDiagonalPairSquareContextOfStripsAndDiagonal e i j y) :=
  (rfl)

variable (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)

/-- The entries of the square spanned by the hidden vertices and `i`, `j`, other than the pair
`(i, j)`, `(j, i)`, read off the square context by inverting the hidden enumeration. -/
private def squareStripsOfContext
    (z : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α)) :
    ((insert i (insert j (Set.range e)) ×ˢ insert i (insert j (Set.range e)) \ {(i, j), (j, i)} :
      Set (ℕ × ℕ))) → α :=
  fun q =>
    if q.1.1 = i then (if q.1.2 = i then z.2.1 else z.1.1.1.2 (Function.invFun e q.1.2))
    else if q.1.1 = j then (if q.1.2 = j then z.2.2 else z.1.2.1.2 (Function.invFun e q.1.2))
    else if q.1.2 = i then z.1.2.2 (Function.invFun e q.1.1)
    else if q.1.2 = j then z.1.1.2 (Function.invFun e q.1.1)
    else z.1.1.1.1 (Function.invFun e q.1.1, Function.invFun e q.1.2)

private theorem measurable_squareStripsOfContext :
    Measurable (squareStripsOfContext (α := α) e i j) := by
  refine Measurable.of_eval fun q => ?_
  simp only [squareStripsOfContext]
  split_ifs <;> fun_prop

omit [MeasurableSpace α] in
include hij hi hj in
private theorem squareStripsOfContext_comp :
    squareStripsOfContext (α := α) e i j ∘ offDiagonalPairSquareContext e i j =
      (insert i (insert j (Set.range e)) ×ˢ insert i (insert j (Set.range e)) \ {(i, j), (j, i)} :
        Set (ℕ × ℕ)).domRestrict := by
  funext x q
  obtain ⟨⟨q₁, q₂⟩, hq, hqC⟩ := q
  simp only [Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
    Prod.mk.injEq, not_or] at hq hqC
  obtain ⟨hq₁, hq₂⟩ := hq
  simp only [Function.comp_apply, Set.domRestrict_apply, squareStripsOfContext,
    offDiagonalPairSquareContext_fst, offDiagonalPairSquareContext_snd, offDiagonalPairContext_fst,
    offDiagonalPairContext_snd]
  have hei (a : ℕ) : e a ≠ i := fun h => hi ⟨a, h⟩
  have hej (a : ℕ) : e a ≠ j := fun h => hj ⟨a, h⟩
  -- Rows and columns of the square are `i`, `j`, or hidden; the pair itself is excluded.
  rcases hq₁ with rfl | rfl | ⟨a, rfl⟩ <;> rcases hq₂ with rfl | rfl | ⟨b, rfl⟩
  · simp
  · exact absurd ⟨rfl, rfl⟩ hqC.1
  · simp [hei b, Function.invFun_eq (⟨b, rfl⟩ : ∃ b', e b' = e b)]
  · exact absurd ⟨rfl, rfl⟩ hqC.2
  · simp [hij.symm]
  · simp [hij.symm, hej b, Function.invFun_eq (⟨b, rfl⟩ : ∃ b', e b' = e b)]
  · simp [hei a, hej a, Function.invFun_eq (⟨a, rfl⟩ : ∃ a', e a' = e a)]
  · simp [hij.symm, hei a, hej a, Function.invFun_eq (⟨a, rfl⟩ : ∃ a', e a' = e a)]
  · simp [hei a, hej a, hei b, hej b, Function.invFun_eq (⟨a, rfl⟩ : ∃ a', e a' = e a),
      Function.invFun_eq (⟨b, rfl⟩ : ∃ b', e b' = e b)]

end Context

/-! ## Conditional independence -/

variable [StandardBorelSpace α] {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- **A visible off-diagonal pair sees the crossing strips and the diagonal only through its square
context.** Let `e` enumerate infinitely many hidden vertices of a jointly exchangeable array and
let `i ≠ j` be visible vertices. Given the hidden block, the strips of `i` and `j` against the
hidden vertices and the two diagonal entries `x (i, i)`, `x (j, j)`, the pair `(x (i, j), x (j, i))`
is conditionally independent of *all* entries in hidden rows, in hidden columns, or on the
diagonal. -/
theorem JointlyExchangeable.condIndepFun_offDiagonalPair_crossingStripsAndDiagonal
    (hρ : JointlyExchangeable ρ fun p x => x p) {e : ℕ → ℕ} (he : (Set.range e).Infinite)
    {i j : ℕ} (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e) :
    CondIndepFun (MeasurableSpace.comap (offDiagonalPairSquareContext e i j) inferInstance)
      (measurable_offDiagonalPairSquareContext e i j).comap_le
      (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
      ((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
        Set (ℕ × ℕ)).domRestrict ρ := by
  set S : Set ℕ := insert i (insert j (Set.range e)) with hS
  set C : Set (ℕ × ℕ) := {(i, j), (j, i)} with hC
  set D : Set (ℕ × ℕ) :=
    (Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} with hD
  -- The square context and the entries of the square other than the pair generate the same
  -- information, and that information is part of the crossing strips and the diagonal.
  have hRC : MeasurableSpace.comap ((S ×ˢ S \ C).domRestrict (π := fun _ => α)) inferInstance ≤
      MeasurableSpace.comap (offDiagonalPairSquareContext (α := α) e i j) inferInstance := by
    rw [← squareStripsOfContext_comp (α := α) e i j hij hi hj, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_squareStripsOfContext e i j).comap_le
  have hCH : MeasurableSpace.comap (offDiagonalPairSquareContext (α := α) e i j) inferInstance ≤
      MeasurableSpace.comap (D.domRestrict (π := fun _ => α)) inferInstance := by
    rw [← offDiagonalPairSquareContextOfStripsAndDiagonal_comp_domRestrict (α := α) e i j,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e i j).comap_le
  -- The pair is conditionally independent of everything outside it, given the rest of the square
  -- spanned by the hidden vertices together with `i` and `j`.
  have hCsub : C ⊆ S ×ˢ S := by
    rintro p hp
    simp only [hC, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp [hS]
  have hbase := hρ.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset (S := S)
    (he.mono fun a ha => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ha)) (B := C)
    (Set.toFinite C) Set.Subset.rfl hCsub
  rw [condIndepFun_iff_condIndep] at hbase
  have hDsub : D ⊆ Cᶜ := by
    rintro p hp hpC
    simp only [hC, Set.mem_insert_iff, Set.mem_singleton_iff] at hpC
    rcases hpC with rfl | rfl <;> rcases hp with (hp | hp) | hp
    · exact hj hp.2
    · exact hi hp.1
    · exact hij hp
    · exact hi hp.2
    · exact hj hp.1
    · exact hij hp.symm
  have hDC : MeasurableSpace.comap (D.domRestrict (π := fun _ => α)) inferInstance ≤
      MeasurableSpace.comap (Cᶜ.domRestrict (π := fun _ => α)) inferInstance := by
    rw [← Set.domRestrict₂_comp_domRestrict hDsub, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hDsub).comap_le
  have hpair := TauCeti.MeasureTheory.comap_pair_le_comap_domRestrict (π := fun _ => α) C
    (Set.mem_insert (i, j) _) (Set.mem_insert_of_mem _ (Set.mem_singleton (j, i)))
  have hstep := condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left hbase hpair) hDC
  rw [condIndepFun_iff_condIndep]
  exact condIndep_of_condIndep_of_le_of_le
    ((measurable_pi_apply (i, j)).prodMk (measurable_pi_apply (j, i))).comap_le
    (Set.measurable_restrict _).comap_le (Set.measurable_restrict _).comap_le hstep hRC hCH

/-- **Distinct visible off-diagonal pairs are conditionally independent given the crossing strips
and the diagonal.** Let `S` be an infinite set of hidden vertices of a jointly exchangeable array.
Index the visible off-diagonal unordered pairs by their increasing representatives `p.1 < p.2`, and
read each as the pair of entries `(x p, x p.swap)`. Given all entries in a hidden row, in a hidden
column, or on the diagonal, these pairs form a conditionally independent family. -/
theorem JointlyExchangeable.iCondIndepFun_offDiagonalPairs
    (hρ : JointlyExchangeable ρ fun p x => x p) {S : Set ℕ} (hS : S.Infinite) :
    let H : Set (ℕ × ℕ) := (Set.univ ×ˢ S) ∪ (S ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
    let V₂ : Set (ℕ × ℕ) := {p | p.1 ∉ S ∧ p.2 ∉ S ∧ p.1 < p.2}
    iCondIndepFun (MeasurableSpace.comap H.domRestrict inferInstance)
      (Set.measurable_restrict H).comap_le
      (fun p : V₂ => fun x : ℕ × ℕ → α => (x p.1, x p.1.swap)) ρ := by
  dsimp only
  let H : Set (ℕ × ℕ) := (Set.univ ×ˢ S) ∪ (S ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
  let V₂ : Set (ℕ × ℕ) := {p | p.1 ∉ S ∧ p.2 ∉ S ∧ p.1 < p.2}
  let m' : MeasurableSpace (ℕ × ℕ → α) :=
    MeasurableSpace.comap H.domRestrict (inferInstanceAs (MeasurableSpace (H → α)))
  let m : V₂ → MeasurableSpace (ℕ × ℕ → α) := fun p =>
    MeasurableSpace.comap (fun x => (x p.1, x p.1.swap)) (inferInstanceAs (MeasurableSpace (α × α)))
  have hm' : m' ≤ (MeasurableSpace.pi : MeasurableSpace (ℕ × ℕ → α)) :=
    (Set.measurable_restrict (X := fun _ : ℕ × ℕ => α) H).comap_le
  have hm (p : V₂) : m p ≤ (MeasurableSpace.pi : MeasurableSpace (ℕ × ℕ → α)) :=
    ((measurable_pi_apply (X := fun _ : ℕ × ℕ => α) p.1).prodMk
      (measurable_pi_apply (X := fun _ : ℕ × ℕ => α) p.1.swap)).comap_le
  apply (iCondIndepFun_iff_iCondIndep (mΩ := MeasurableSpace.pi) m' hm'
    (fun _ : V₂ => inferInstance) (fun p : V₂ => fun x : ℕ × ℕ → α => (x p.1, x p.1.swap)) ρ).2
  apply iCondIndep_of_condIndep_compl (mΩ := MeasurableSpace.pi) hm' hm
  intro p
  obtain ⟨⟨i, j⟩, hp⟩ := p
  have hi : i ∉ S := hp.1
  have hj : j ∉ S := hp.2.1
  have hij : i < j := hp.2.2
  -- The pair is conditionally independent of everything outside it given the rest of the square
  -- spanned by the hidden vertices and its two vertices; that rest lies in `H`, which avoids the
  -- pair, so the conditioning may be enlarged to `H`.
  let C : Set (ℕ × ℕ) := {(i, j), (j, i)}
  let S' : Set ℕ := insert i (insert j S)
  have hCsub : C ⊆ S' ×ˢ S' := by
    rintro q hq
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl <;> simp [S']
  have hlocal := hρ.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset (S := S')
    (hS.mono fun a ha => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ha)) (B := C)
    (Set.toFinite C) Set.Subset.rfl hCsub
  have hRH : S' ×ˢ S' \ C ⊆ H := by
    rintro ⟨q₁, q₂⟩ ⟨hq, hqC⟩
    simp only [S', Set.mem_prod, Set.mem_insert_iff] at hq
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or] at hqC
    obtain ⟨hq₁, hq₂⟩ := hq
    rcases hq₁ with rfl | rfl | hq₁ <;> rcases hq₂ with rfl | rfl | hq₂
    · exact Or.inr rfl
    · exact absurd ⟨rfl, rfl⟩ hqC.1
    · exact Or.inl (Or.inl ⟨trivial, hq₂⟩)
    · exact absurd ⟨rfl, rfl⟩ hqC.2
    · exact Or.inr rfl
    · exact Or.inl (Or.inl ⟨trivial, hq₂⟩)
    all_goals exact Or.inl (Or.inr ⟨hq₁, trivial⟩)
  have hHD : H ⊆ Cᶜ := by
    rintro q hq hqC
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hqC
    rcases hqC with rfl | rfl <;> rcases hq with (hq | hq) | hq
    · exact hj hq.2
    · exact hi hq.1
    · exact hij.ne hq
    · exact hi hq.2
    · exact hj hq.1
    · exact hij.ne' hq
  have hbase : CondIndep m' (MeasurableSpace.comap C.domRestrict inferInstance)
      (MeasurableSpace.comap Cᶜ.domRestrict inferInstance) hm' ρ :=
    (condIndepFun_iff_condIndep m' hm' C.domRestrict Cᶜ.domRestrict ρ).1
      (condIndepFun_domRestrict_of_subset (Set.measurable_restrict C) hlocal hRH hHD)
  have hleft : m ⟨(i, j), hp⟩ ≤ MeasurableSpace.comap C.domRestrict inferInstance :=
    TauCeti.MeasureTheory.comap_pair_le_comap_domRestrict C (Set.mem_insert _ _) (by simp [C])
  -- Every other increasing representative, and its swap, avoids both entries of the pair.
  have hright : (⨆ q : {q : V₂ // q ≠ ⟨(i, j), hp⟩}, m q.1) ≤
      MeasurableSpace.comap Cᶜ.domRestrict inferInstance := by
    refine iSup_le fun q => ?_
    obtain ⟨-, -, hqlt⟩ := q.1.2
    have hne : q.1.1 ≠ (i, j) := fun h => q.2 (Subtype.ext h)
    have hne' : q.1.1 ≠ (j, i) := fun h => by
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
      omega
    refine TauCeti.MeasureTheory.comap_pair_le_comap_domRestrict Cᶜ ?_ ?_
    · simp only [C, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hne'⟩
    · simp only [C, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
      exact ⟨hne', hne⟩
  exact condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left hbase hleft) hright

/-! ## The common coding -/

variable [Nonempty α]

/-- The coding of a single visible off-diagonal pair from the crossing strips and the diagonal:
feeding the pair's square context and one fresh uniform variable to a realization of the common
conditional kernel reproduces the joint law of the crossing strips, the diagonal and that pair. -/
private theorem map_prod_pairCoding_eq
    (hρ : JointlyExchangeable ρ fun p x => x p) {e : ℕ → ℕ} (he : (Set.range e).Infinite)
    {i j : ℕ} (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    {g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α) →
      I → α × α} (hg : Measurable (Function.uncurry g))
    (hgmap : ∀ z, (volume : Measure I).map (g z) =
      condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
        (offDiagonalPairSquareContext e i j) ρ z) :
    ((ρ.map ((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
          Set (ℕ × ℕ)).domRestrict).prod (volume : Measure I)).map
        (fun q => (q.1, g (offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1) q.2)) =
      ρ.map fun x => (((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪
        {p : ℕ × ℕ | p.1 = p.2} : Set (ℕ × ℕ)).domRestrict x, (x (i, j), x (j, i))) := by
  set H : Set (ℕ × ℕ) :=
    (Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
  have hZ : Measurable (H.domRestrict (π := fun _ : ℕ × ℕ => α)) := Set.measurable_restrict H
  have hΦ : Measurable (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j) :=
    measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e i j
  have hψ : Measurable fun y : H → α =>
      (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j y, y) :=
    hΦ.prodMk measurable_id
  have hX : Measurable fun x : ℕ × ℕ → α => (x (i, j), x (j, i)) :=
    (measurable_pi_apply (i, j)).prodMk (measurable_pi_apply (j, i))
  have hctx := measurable_offDiagonalPairSquareContext (α := α) e i j
  set κ := condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
    (offDiagonalPairSquareContext e i j) ρ
  -- Conditionally on its square context, the pair forgets the rest of the crossing strips and the
  -- diagonal, so the joint law of the context, the strips and the pair disintegrates through the
  -- context kernel.
  have hjoint : ρ.map (fun x => ((offDiagonalPairSquareContext e i j x, H.domRestrict x),
      (x (i, j), x (j, i)))) =
      (ρ.map fun x => (offDiagonalPairSquareContext e i j x, H.domRestrict x)) ⊗ₘ
        κ.prodMkRight (H → α) := by
    refine (condDistrib_ae_eq_iff_measure_eq_compProd ((hctx.prodMk hZ).aemeasurable)
      hX.aemeasurable _).1 ?_
    exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hX hZ hctx).1
      (hρ.condIndepFun_offDiagonalPair_crossingStripsAndDiagonal he hij hi hj).symm
  -- One uniform variable realizes that kernel, uniformly in the context.
  have hcode : ((ρ.map fun x => (offDiagonalPairSquareContext e i j x, H.domRestrict x)).prod
      (volume : Measure I)).map (fun q => (q.1, g q.1.1 q.2)) =
      (ρ.map fun x => (offDiagonalPairSquareContext e i j x, H.domRestrict x)) ⊗ₘ
        κ.prodMkRight (H → α) :=
    (κ.prodMkRight (H → α)).map_prod_eq_compProd_of_map _ (fun w => g w.1)
      (hg.comp (measurable_fst.prodMap measurable_id)) fun w => hgmap w.1
  -- The context is a function of the strips and the diagonal, so it can be dropped from the joint
  -- law.
  have hlaw : (ρ.map fun x => (offDiagonalPairSquareContext e i j x, H.domRestrict x)) =
      (ρ.map H.domRestrict).map
        fun y => (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j y, y) := by
    rw [Measure.map_map hψ hZ]
    congr 1
    rw [← offDiagonalPairSquareContextOfStripsAndDiagonal_comp_domRestrict (α := α) e i j]
    rfl
  have hprod : ((ρ.map H.domRestrict).map
        fun y => (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j y, y)).prod
          (volume : Measure I) =
      ((ρ.map H.domRestrict).prod (volume : Measure I)).map
        (Prod.map
          (fun y : H → α => (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j y, y))
          id) := by
    simpa using Measure.map_prod_map (ρ.map H.domRestrict) (volume : Measure I) hψ measurable_id
  -- measurability of the three maps the calculation pushes measures along
  have hdrop : Measurable fun w : ((((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) ×
      (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α)) × (H → α)) × (α × α) => (w.1.2, w.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hpair : Measurable fun q : ((((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) ×
      (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α)) × (H → α)) × I => (q.1, g q.1.1 q.2) :=
    measurable_fst.prodMk (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hjointMeas : Measurable fun x : ℕ × ℕ → α =>
      ((offDiagonalPairSquareContext e i j x, H.domRestrict x), (x (i, j), x (j, i))) :=
    (hctx.prodMk hZ).prodMk hX
  calc ((ρ.map H.domRestrict).prod (volume : Measure I)).map
        (fun q => (q.1, g (offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1) q.2))
      = ((((ρ.map H.domRestrict).map
            fun y => (offDiagonalPairSquareContextOfStripsAndDiagonal (α := α) e i j y, y)).prod
          (volume : Measure I)).map (fun q => (q.1, g q.1.1 q.2))).map
            fun w => (w.1.2, w.2) := by
        rw [hprod, Measure.map_map hpair (hψ.prodMap measurable_id), Measure.map_map hdrop
          (hpair.comp (hψ.prodMap measurable_id))]
        rfl
    _ = (ρ.map fun x => ((offDiagonalPairSquareContext e i j x, H.domRestrict x),
          (x (i, j), x (j, i)))).map fun w => (w.1.2, w.2) := by
        rw [← hlaw, hcode, hjoint]
    _ = ρ.map fun x => (H.domRestrict x, (x (i, j), x (j, i))) := by
        rw [Measure.map_map hdrop hjointMeas]
        rfl

/-- The coding of a single visible off-diagonal pair may be oriented along any measurable set `O`
of square contexts: on contexts in `O` the pair is coded from its own square context, and off `O`
it is coded as the reversal of the coding of the reversed pair. Both codings reproduce the joint
law of the crossing strips, the diagonal and the pair, and they are switched along an event of the
strips and the diagonal alone. -/
private theorem map_prod_orientedPairCoding_eq
    (hρ : JointlyExchangeable ρ fun p x => x p) {e : ℕ → ℕ} (he : (Set.range e).Infinite)
    {i j : ℕ} (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    {g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α) →
      I → α × α} (hg : Measurable (Function.uncurry g))
    (hgij : ∀ z, (volume : Measure I).map (g z) =
      condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
        (offDiagonalPairSquareContext e i j) ρ z)
    (hgji : ∀ z, (volume : Measure I).map (g z) =
      condDistrib (fun x : ℕ × ℕ → α => (x (j, i), x (i, j)))
        (offDiagonalPairSquareContext e j i) ρ z)
    {O : Set (((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) ×
      (α × α))} [DecidablePred (· ∈ O)] (hO : MeasurableSet O) :
    ((ρ.map ((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2} :
          Set (ℕ × ℕ)).domRestrict).prod (volume : Measure I)).map
        (fun q => (q.1,
          if offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1 ∈ O then
            g (offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1) q.2
          else (g (Prod.map Prod.swap Prod.swap
            (offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1)) q.2).swap)) =
      ρ.map fun x => (((Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪
        {p : ℕ × ℕ | p.1 = p.2} : Set (ℕ × ℕ)).domRestrict x, (x (i, j), x (j, i))) := by
  set H : Set (ℕ × ℕ) :=
    (Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
  have hcoding (k l : ℕ) : Measurable fun q : (H → α) × I =>
      (q.1, g (offDiagonalPairSquareContextOfStripsAndDiagonal e k l q.1) q.2) :=
    measurable_fst.prodMk (hg.comp
      (((measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e k l).comp
        measurable_fst).prodMk measurable_snd))
  have hswap : Measurable (Prod.map (id : (H → α) → H → α) (Prod.swap : α × α → α × α)) :=
    measurable_id.prodMap measurable_swap
  -- The coding of the pair from its own square context, and the reversal of the coding of the
  -- reversed pair from the reversed square context, have the same law.
  have hfwd := map_prod_pairCoding_eq hρ he hij hi hj hg hgij
  have hbwd : ((ρ.map H.domRestrict).prod (volume : Measure I)).map
      (fun q => (q.1, (g (offDiagonalPairSquareContextOfStripsAndDiagonal e j i q.1) q.2).swap)) =
      ρ.map fun x => (H.domRestrict x, (x (i, j), x (j, i))) := by
    have h := congrArg (Measure.map (Prod.map id Prod.swap))
      (map_prod_pairCoding_eq hρ he hij.symm hj hi hg hgji)
    rwa [Measure.map_map hswap (hcoding j i), Measure.map_map hswap
      (Set.measurable_restrict H |>.prodMk
        ((measurable_pi_apply (j, i)).prodMk (measurable_pi_apply (i, j))))] at h
  have hO' : MeasurableSet {w : (H → α) × (α × α) |
      offDiagonalPairSquareContextOfStripsAndDiagonal e i j w.1 ∈ O} :=
    (measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e i j).comp measurable_fst hO
  rw [← hfwd]
  refine Eq.trans (congrArg (Measure.map · _) (funext fun q => ?_))
    (TauCeti.MeasureTheory.Measure.map_ite_mem_eq (hcoding i j) (hswap.comp (hcoding j i)) hO'
      (Filter.Eventually.of_forall fun _ => Iff.rfl) (hfwd.trans hbwd.symm))
  by_cases hq : offDiagonalPairSquareContextOfStripsAndDiagonal e i j q.1 ∈ O <;>
    simp [hq, offDiagonalPairSquareContextOfStripsAndDiagonal_swap e i j]

/-- **Every finite family of visible off-diagonal pairs of a jointly exchangeable array is generated
from their square contexts by one common coding function and independent uniform variables.** Let
`e` enumerate infinitely many hidden vertices. Index the visible off-diagonal unordered pairs by
their increasing representatives `p.1 < p.2`. There is a single measurable `g` such that, for every
finite family of such pairs, feeding each pair's square context and its own independent uniform
variable to `g` reproduces the joint law of the crossing strips, the diagonal and that whole family
of pairs `(x p, x p.swap)`.

The coding can moreover be oriented along any measurable set `O` of square contexts: whenever
exactly one of a context `c` and its reversal `Prod.map Prod.swap Prod.swap c` lies in `O`, the
coding of the reversal is the reversed coding of `c`. Reversing a square context is reversing the
pair (`offDiagonalPairSquareContext_swap`), so on such contexts `g` produces the two orientations
of one pair from one uniform variable consistently.

The coding function does not depend on the position of the pair, which is what lets it serve as
the cell noise `U {i, j}` of a jointly exchangeable Aldous–Hoover representation. -/
theorem JointlyExchangeable.exists_common_offDiagonalPairs_coding
    (hρ : JointlyExchangeable ρ fun p x => x p) {e : ℕ → ℕ} (he : (Set.range e).Infinite)
    {O : Set (((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) ×
      (α × α))} (hO : MeasurableSet O) :
    let H : Set (ℕ × ℕ) :=
      (Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
    let V₂ : Set (ℕ × ℕ) := {p | p.1 ∉ Set.range e ∧ p.2 ∉ Set.range e ∧ p.1 < p.2}
    ∃ g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α) →
        I → α × α, Measurable (Function.uncurry g) ∧
      (∀ c u, (c ∈ O ↔ Prod.map Prod.swap Prod.swap c ∉ O) →
        g (Prod.map Prod.swap Prod.swap c) u = (g c u).swap) ∧
      ∀ F : Finset V₂,
        (ρ.prod (Measure.pi fun _ : F => (volume : Measure I))).map
            (fun q => (H.domRestrict q.1,
              fun p : F => g (offDiagonalPairSquareContext e p.1.1.1 p.1.1.2 q.1) (q.2 p))) =
          ρ.map fun x => (H.domRestrict x, fun p : F => (x p.1.1, x p.1.1.swap)) := by
  intro H V₂
  rcases Set.eq_empty_or_nonempty V₂ with hV | ⟨⟨i₀, j₀⟩, hi₀, hj₀, hij₀⟩
  · -- If the hidden vertices leave at most one visible vertex, there is no visible off-diagonal
    -- pair: every finite family is then empty and the claim only compares the law of the crossing
    -- strips and the diagonal with itself, so any measurable constant symmetric coding serves.
    have : IsEmpty V₂ := Set.isEmpty_coe_sort.2 hV
    refine ⟨fun _ _ => (Classical.arbitrary α, Classical.arbitrary α), measurable_const,
      fun _ _ _ => rfl, fun F => ?_⟩
    have : IsEmpty F := ⟨fun p => isEmptyElim p.1⟩
    have hstrips : Measurable fun x : ℕ × ℕ → α =>
        (H.domRestrict x, fun p : F => (x p.1.1, x p.1.1.swap)) :=
      (Set.measurable_restrict H).prodMk (Measurable.of_eval fun p =>
        (measurable_pi_apply p.1.1).prodMk (measurable_pi_apply p.1.1.swap))
    have hfactor : (fun q : (ℕ × ℕ → α) × (F → I) =>
          (H.domRestrict q.1, fun _ : F => (Classical.arbitrary α, Classical.arbitrary α))) =
        (fun x : ℕ × ℕ → α => (H.domRestrict x, fun p : F => (x p.1.1, x p.1.1.swap))) ∘
          Prod.fst :=
      funext fun q => Prod.ext rfl (Subsingleton.elim _ _)
    rw [hfactor, ← Measure.map_map hstrips measurable_fst, Measure.map_fst_prod]
    simp
  classical
  -- The canonical conditional kernel of a reference pair is realized by a uniform variable; the
  -- common-kernel theorem makes the same realization work at every visible off-diagonal pair, in
  -- either orientation.
  obtain ⟨g₀, hg₀, hgmap⟩ := Kernel.exists_measurable_map_eq_unitInterval
    (condDistrib (fun x : ℕ × ℕ → α => (x (i₀, j₀), x (j₀, i₀)))
      (offDiagonalPairSquareContext e i₀ j₀) ρ)
  have hgmap' {i j : ℕ} (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e) (z) :
      (volume : Measure I).map (g₀ z) =
        condDistrib (fun x : ℕ × ℕ → α => (x (i, j), x (j, i)))
          (offDiagonalPairSquareContext e i j) ρ z := by
    rw [hρ.condDistrib_offDiagonalPairSquareContext_eq e hij₀.ne hij hi₀ hj₀ hi hj]
    exact hgmap z
  -- Off `O`, a context is coded as the reversal of the coding of the reversed context.
  let g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) ×
      (α × α) → I → α × α :=
    fun c u => if c ∈ O then g₀ c u else (g₀ (Prod.map Prod.swap Prod.swap c) u).swap
  have hg : Measurable (Function.uncurry g) :=
    Measurable.ite (measurable_fst hO) hg₀ (measurable_swap.comp (hg₀.comp
      (((measurable_swap.prodMap measurable_swap).comp measurable_fst).prodMk measurable_snd)))
  have hswap : ∀ c u, (c ∈ O ↔ Prod.map Prod.swap Prod.swap c ∉ O) →
      g (Prod.map Prod.swap Prod.swap c) u = (g c u).swap := by
    intro c u hc
    have hcc : Prod.map Prod.swap Prod.swap (Prod.map Prod.swap Prod.swap c) = c := by
      simp [Prod.map]
    by_cases h : c ∈ O
    · simp only [g, ite_eq_left h, ite_eq_right (hc.1 h), hcc]
    · simp only [g, ite_eq_right h, ite_eq_left (not_not.1 (mt hc.2 h)), Prod.swap_swap]
  refine ⟨g, hg, hswap, fun F => ?_⟩
  have hZ : Measurable (H.domRestrict (π := fun _ : ℕ × ℕ => α)) := Set.measurable_restrict H
  -- Distinct visible off-diagonal pairs are conditionally independent given the crossing strips
  -- and the diagonal.
  have hall := hρ.iCondIndepFun_offDiagonalPairs he
  have hF : iCondIndepFun (MeasurableSpace.comap H.domRestrict inferInstance)
      (Set.measurable_restrict H).comap_le
      (fun p : F => fun x : ℕ × ℕ → α => (x p.1.1, x p.1.1.swap)) ρ :=
    Kernel.iIndepFun.precomp Subtype.val_injective hall
  -- Each of them is coded from its own square context by the common coding function.
  have hglue := hF.map_prod_pi_eq_of_map_prod_eq hZ
    (fun p : F => (measurable_pi_apply p.1.1).prodMk (measurable_pi_apply p.1.1.swap))
    (ρ := fun _ : F => (volume : Measure I))
    (f := fun p : F => fun y u =>
      g (offDiagonalPairSquareContextOfStripsAndDiagonal e p.1.1.1 p.1.1.2 y) u)
    (fun p => hg.comp
      ((measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e p.1.1.1 p.1.1.2).comp
        measurable_fst |>.prodMk measurable_snd))
    fun p => map_prod_orientedPairCoding_eq hρ he p.1.2.2.2.ne p.1.2.1 p.1.2.2.1 hg₀
      (hgmap' p.1.2.2.2.ne p.1.2.1 p.1.2.2.1) (hgmap' p.1.2.2.2.ne' p.1.2.2.1 p.1.2.1) hO
  have hcoded : Measurable fun p : (H → α) × (F → I) =>
      (p.1, fun r : F =>
        g (offDiagonalPairSquareContextOfStripsAndDiagonal e r.1.1.1 r.1.1.2 p.1) (p.2 r)) :=
    measurable_fst.prodMk (Measurable.of_eval fun r => hg.comp
      (((measurable_offDiagonalPairSquareContextOfStripsAndDiagonal e r.1.1.1 r.1.1.2).comp
        measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)))
  -- The strips are read off `ρ` itself, so the law of the strips paired with the uniform family
  -- is the image of `ρ` paired with that family: the restriction only acts on the first factor.
  have hprod : (ρ.map H.domRestrict).prod (Measure.pi fun _ : F => (volume : Measure I)) =
      (ρ.prod (Measure.pi fun _ : F => (volume : Measure I))).map (Prod.map H.domRestrict id) := by
    simpa using
      Measure.map_prod_map ρ (Measure.pi fun _ : F => (volume : Measure I)) hZ measurable_id
  rw [hprod, Measure.map_map hcoded (hZ.prodMap measurable_id)] at hglue
  refine Eq.trans (congrArg (Measure.map · _) ?_) hglue
  funext q
  refine Prod.ext rfl (funext fun p => ?_)
  exact congrArg (g · (q.2 p))
    (congrFun
      (offDiagonalPairSquareContextOfStripsAndDiagonal_comp_domRestrict (α := α) e p.1.1.1 p.1.1.2)
      q.1).symm

/-- **One common coding generates all visible off-diagonal pairs of a jointly exchangeable array.**
Let `e` enumerate infinitely many hidden vertices. There is a single measurable `g` such that
feeding every visible off-diagonal pair's square context and its own fresh uniform variable to `g`,
the uniform variables being i.i.d. over *all* visible increasing pairs, reproduces the joint law of
the crossing strips, the diagonal and all the pairs `(x p, x p.swap)` at once.

As in `JointlyExchangeable.exists_common_offDiagonalPairs_coding`, the coding can be oriented along
any measurable set `O` of square contexts: whenever exactly one of a context `c` and its reversal
lies in `O`, the coding of the reversal is the reversed coding of `c`.

Together with the crossing strips and the diagonal, these pairs are the whole array, so this is the
cell layer of a jointly exchangeable Aldous–Hoover representation. The orientation is what lets a
coding that sees the two vertices of a pair but not their order produce both entries of the pair
consistently. -/
theorem JointlyExchangeable.exists_common_offDiagonalArray_coding
    (hρ : JointlyExchangeable ρ fun p x => x p) {e : ℕ → ℕ} (he : (Set.range e).Infinite)
    {O : Set (((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) ×
      (α × α))} (hO : MeasurableSet O) :
    let H : Set (ℕ × ℕ) :=
      (Set.univ ×ˢ Set.range e) ∪ (Set.range e ×ˢ Set.univ) ∪ {p : ℕ × ℕ | p.1 = p.2}
    let V₂ : Set (ℕ × ℕ) := {p | p.1 ∉ Set.range e ∧ p.2 ∉ Set.range e ∧ p.1 < p.2}
    ∃ g : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α))) × (α × α) →
        I → α × α, Measurable (Function.uncurry g) ∧
      (∀ c u, (c ∈ O ↔ Prod.map Prod.swap Prod.swap c ∉ O) →
        g (Prod.map Prod.swap Prod.swap c) u = (g c u).swap) ∧
      (ρ.prod (Measure.infinitePi fun _ : V₂ => (volume : Measure I))).map
          (fun q => (H.domRestrict q.1,
            fun p : V₂ => g (offDiagonalPairSquareContext e p.1.1 p.1.2 q.1) (q.2 p))) =
        ρ.map fun x => (H.domRestrict x, fun p : V₂ => (x p.1, x p.1.swap)) := by
  intro H V₂
  obtain ⟨g, hg, hswap, hF⟩ := hρ.exists_common_offDiagonalPairs_coding he hO
  refine ⟨g, hg, hswap, ?_⟩
  have hZ : Measurable (H.domRestrict (π := fun _ : ℕ × ℕ => α)) := Set.measurable_restrict H
  have hcode : Measurable fun q : (ℕ × ℕ → α) × (V₂ → I) =>
      (H.domRestrict q.1,
        fun p : V₂ => g (offDiagonalPairSquareContext e p.1.1 p.1.2 q.1) (q.2 p)) :=
    (hZ.comp measurable_fst).prodMk (Measurable.of_eval fun p => hg.comp
      (((measurable_offDiagonalPairSquareContext e p.1.1 p.1.2).comp measurable_fst).prodMk
        ((measurable_pi_apply p).comp measurable_snd)))
  have hread : Measurable fun x : ℕ × ℕ → α =>
      (H.domRestrict x, fun p : V₂ => (x p.1, x p.1.swap)) :=
    hZ.prodMk (Measurable.of_eval fun p =>
      (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.1.swap))
  -- Jointly with the crossing strips and the diagonal, the finite-dimensional marginals in the
  -- pairs are those of `exists_common_offDiagonalPairs_coding`, which determine the law.
  refine TauCeti.MeasureTheory.Measure.ext_prod_pi_of_forall_finset_map_restrict_eq fun F => ?_
  have hFr : Measurable (Prod.map (id : (H → α) → H → α) (F.restrict (π := fun _ => α × α))) :=
    measurable_id.prodMap (Finset.measurable_restrict F)
  have hIr : Measurable (Prod.map (id : (ℕ × ℕ → α) → ℕ × ℕ → α)
      (F.restrict (π := fun _ => I))) :=
    measurable_id.prodMap (Finset.measurable_restrict F)
  have hcodeF : Measurable fun q : (ℕ × ℕ → α) × (F → I) =>
      (H.domRestrict q.1,
        fun p : F => g (offDiagonalPairSquareContext e p.1.1.1 p.1.1.2 q.1) (q.2 p)) :=
    (hZ.comp measurable_fst).prodMk (Measurable.of_eval fun p => hg.comp
      (((measurable_offDiagonalPairSquareContext e p.1.1.1 p.1.1.2).comp measurable_fst).prodMk
        ((measurable_pi_apply p).comp measurable_snd)))
  rw [Measure.map_map hFr hcode, Measure.map_map hFr hread]
  -- Restricting the coded pairs to `F` only reads the uniform variables indexed by `F`.
  have hcomm : Prod.map id F.restrict ∘ (fun q : (ℕ × ℕ → α) × (V₂ → I) =>
        (H.domRestrict q.1,
          fun p : V₂ => g (offDiagonalPairSquareContext e p.1.1 p.1.2 q.1) (q.2 p))) =
      (fun q : (ℕ × ℕ → α) × (F → I) =>
        (H.domRestrict q.1,
          fun p : F => g (offDiagonalPairSquareContext e p.1.1.1 p.1.1.2 q.1) (q.2 p))) ∘
        Prod.map id F.restrict :=
    rfl
  rw [hcomm, ← Measure.map_map hcodeF hIr, ← Measure.map_prod_map _ _ measurable_id
    (Finset.measurable_restrict F), Measure.map_id, Measure.infinitePi_map_restrict, hF F]
  rfl

end TauCeti.Probability

end

end
