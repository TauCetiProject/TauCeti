/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.TemperleyLieb.Basic
import Mathlib.Data.List.Chain
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Combinatorics.PlanarMatching.HalfDiagram

/-!
# Jones normal form and the Catalan rank bound for Temperley–Lieb algebras

Every element of the Temperley–Lieb algebra `TemperleyLieb R δ n` on `n` strands, over any
commutative semiring `R` and at any loop value `δ : R`, is an `R`-linear combination of words in
**Jones normal form**: products of descending generator runs
`(e i₁ * e (i₁ - 1) * ⋯ * e j₁) * ⋯ * (e iₚ * e (iₚ - 1) * ⋯ * e jₚ)` with `jₖ ≤ iₖ`,
strictly increasing upper indices `i₁ < ⋯ < iₚ`, and strictly increasing lower indices
`j₁ < ⋯ < jₚ` (`TauCeti.TemperleyLieb.NormalWord`). There are `catalan n` such normal words
(`TauCeti.TemperleyLieb.NormalWord.card_eq_catalan`), so `TemperleyLieb R δ n` is a finitely
generated `R`-module of rank at most `catalan n` (`TauCeti.TemperleyLieb.finrank_le_catalan`).

## Counting normal words

In `NormalWord (n + 2)`, strict monotonicity of upper endpoints forces `Fin.last n` to appear at
most as the upper endpoint of the final run. Splitting according to whether `Fin.last n` appears
(`TauCeti.TemperleyLieb.NormalWord.stepEquiv`) identifies `NormalWord (n + 2)` with the disjoint
union of `NormalWord (n + 1)` and extensions `(w, j)` with `(w.lowerBound : ℕ) ≤ j`. Stratified by
`lowerBound`, the cumulative counts match Catalan's triangle via `TauCeti.halfCount`.

## Reduction and low-strand bases

Any generator word `l` decomposes uniquely into maximal descending-by-one runs with
`(iₖ₊₁ : ℕ) + 1 ≠ jₖ`. If `l` is not in Jones normal form, its first adjacent pair `(i₁, j₁)`,
`(i₂, j₂)` violating `i₁ < i₂ ∧ j₁ < j₂` reduces by distant commutation (`(i₂ : ℕ) + 2 ≤ j₁`,
preserving length and strictly decreasing lexicographic rank), quadratic absorption (`i₂ = j₁`,
decreasing length by `1`), or left/right zig-zag absorption (`e i * e (i ± 1) * e i = e i`,
decreasing length by `2`). On `n ≤ 3` strands, reading off the first column of the matrix
representations (`algEquivOfLeOne`, `twoStrandRep`, and the `5 × 5` left-regular representation
`threeStrandRep`) supplies an `R`-linear left inverse, proving that `NormalWord n` forms an
`R`-basis of `TemperleyLieb R δ n` over every commutative semiring `R` (`basisOfLeThree`).

## Main definitions and results

* `TauCeti.TemperleyLieb.wordProd`, `TauCeti.TemperleyLieb.descendingRun`: generator word products
  and descending index runs `[i, …, j]`.
* `TauCeti.TemperleyLieb.NormalWord`, `NormalWord.eval`, `NormalWord.strandIncl`,
  `NormalWord.stepEquiv`: Jones normal words, their evaluation, strand inclusion, and Catalan
  branching equivalence.
* `TauCeti.TemperleyLieb.NormalWord.toList_injective`,
  `TauCeti.TemperleyLieb.NormalWord.card_eq_catalan`: normal words spell distinct generator lists
  and have cardinality `catalan n`.
* `TauCeti.TemperleyLieb.span_range_eval_eq_top`, `TauCeti.TemperleyLieb.rank_le_catalan`,
  `TauCeti.TemperleyLieb.finrank_le_catalan`: spanning by normal words and the Catalan rank bound.
* `TauCeti.TemperleyLieb.threeStrandRep`, `TauCeti.TemperleyLieb.basisTwo`,
  `TauCeti.TemperleyLieb.basisThree`, `TauCeti.TemperleyLieb.basisOfLeThree`: exact bases on up to
  three strands, yielding `finrank_two`, `finrank_three`, `e_ne_zero_three`, and
  `strandIncl_injective_of_le_one`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §4.1.4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8, Proposition 2.8.5.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Exercises 4.1.2–4.1.3.
-/

public section

namespace TauCeti.TemperleyLieb

open Finset

/-! ### Generator words and descending runs -/

section WordProd

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The product `e δ i₁ * ⋯ * e δ iₖ` of Temperley–Lieb generators spelled by a word
`l : List (Fin (n - 1))`. -/
def wordProd (δ : R) (l : List (Fin (n - 1))) : TemperleyLieb R δ n :=
  (l.map (e δ)).prod

/-- The empty generator word evaluates to `1`. -/
@[simp]
theorem wordProd_nil (δ : R) : wordProd (R := R) (n := n) δ [] = 1 := (rfl)

/-- Prepending a generator index left-multiplies by the corresponding generator. -/
@[simp]
theorem wordProd_cons (δ : R) (i : Fin (n - 1)) (l : List (Fin (n - 1))) :
    wordProd δ (i :: l) = e δ i * wordProd δ l := by simp [wordProd]

/-- A single-letter generator word evaluates to that generator. -/
theorem wordProd_singleton (δ : R) (i : Fin (n - 1)) : wordProd δ [i] = e δ i := by simp [wordProd]

/-- Concatenating generator words multiplies their evaluations. -/
@[simp]
theorem wordProd_append (δ : R) (l₁ l₂ : List (Fin (n - 1))) :
    wordProd δ (l₁ ++ l₂) = wordProd δ l₁ * wordProd δ l₂ := by
  simp [wordProd, List.map_append, List.prod_append]

/-- Including a generator word along `strandIncl` shifts every generator index by `Fin.castSucc`. -/
@[simp]
theorem strandIncl_wordProd (δ : R) (l : List (Fin n)) :
    strandIncl (wordProd (R := R) (n := n + 1) δ l) = wordProd δ (l.map Fin.castSucc) := by
  induction l with
  | nil => simp [wordProd]
  | cons i l ih => rw [wordProd_cons, map_mul, strandIncl_e, ih, List.map_cons, wordProd_cons]

/-- The augmentation is `1` on the empty word and vanishes on every nonempty generator word. -/
@[simp]
theorem aug_wordProd (δ : R) (l : List (Fin (n - 1))) :
    aug (wordProd (R := R) δ l) = if l.isEmpty then 1 else 0 := by
  cases l <;> simp

/-- Products of generators span `TemperleyLieb R δ n` as an `R`-module. -/
theorem span_range_wordProd_eq_top (δ : R) :
    Submodule.span R (Set.range (wordProd (R := R) (n := n) δ)) = ⊤ := by
  set M := Submodule.span R (Set.range (wordProd (R := R) (n := n) δ))
  have hword (l : List (Fin (n - 1))) : wordProd δ l ∈ M := Submodule.subset_span ⟨l, rfl⟩
  have hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨l₁, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem _ hy => obtain ⟨l₂, rfl⟩ := hy; simpa only [← wordProd_append] using hword (l₁ ++ l₂)
      | zero => simp
      | add _ _ _ _ ha hb => simpa only [mul_add] using M.add_mem ha hb
      | smul r _ _ ha => simpa only [mul_smul_comm] using M.smul_mem r ha
    | zero => simp
    | add _ _ _ _ ha hb => simpa only [add_mul] using M.add_mem ha hb
    | smul r _ _ ha => simpa only [smul_mul_assoc] using M.smul_mem r ha
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  induction x using TemperleyLieb.induction with
  | e i => simpa using hword [i]
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← wordProd_nil δ]
    exact M.smul_mem r (hword [])
  | add _ _ hx hy => exact M.add_mem hx hy
  | mul _ _ hx hy => exact hmul _ hx _ hy

/-- If every letter of `l` is at distance at least `2` from `x`, then `e δ x` commutes past
`wordProd δ l`. -/
private theorem wordProd_mul_e_comm {δ : R} {x : Fin (n - 1)} {l : List (Fin (n - 1))}
    (h : ∀ a ∈ l, (a : ℕ) + 2 ≤ x ∨ (x : ℕ) + 2 ≤ a) :
    wordProd δ l * e δ x = e δ x * wordProd δ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := (commute_e (δ := δ) (h a List.mem_cons_self)).eq
    rw [wordProd_cons, mul_assoc, ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb),
      ← mul_assoc, ha, mul_assoc]

end WordProd

section DescendingRun

variable {m : ℕ}

/-- The descending run `[i, i - 1, …, j]` in `Fin m` (with `i.val + 1 - j.val` entries, so
nonempty whenever `j ≤ i`). -/
def descendingRun (i j : Fin m) : List (Fin m) :=
  (List.range (i.val + 1 - j.val)).map fun k ↦
    ⟨i.val - k, (Nat.sub_le i.val k).trans_lt i.isLt⟩

/-- A descending run from `i` to `i` is the singleton `[i]`. -/
@[simp]
theorem descendingRun_self (i : Fin m) : descendingRun i i = [i] := by
  have h : i.val + 1 - i.val = 1 := by omega
  rw [descendingRun, h, List.range_one]; simp

/-- The length of `descendingRun i j` is `i.val + 1 - j.val`. -/
@[simp]
theorem length_descendingRun (i j : Fin m) : (descendingRun i j).length = i.val + 1 - j.val := by
  simp [descendingRun]

/-- For `j ≤ i`, the entries of `descendingRun i j` are the indices between `j` and `i`. -/
theorem mem_descendingRun {i j a : Fin m} (h : j ≤ i) :
    a ∈ descendingRun i j ↔ j ≤ a ∧ a ≤ i := by
  simp only [descendingRun, List.mem_map, List.mem_range, Fin.ext_iff, Fin.le_def]
  refine ⟨fun ⟨k, hk, hka⟩ ↦ ?_, fun ⟨_, _⟩ ↦ ⟨i.val - a.val, by omega, by omega⟩⟩
  have : j.val ≤ i.val := h
  omega

/-- Splitting a descending run `[i, …, j]` at an intermediate cut `k` with `j < k ≤ i`. -/
theorem descendingRun_split {i k j : Fin m} (hik : k ≤ i) (hjk : j < k) :
    descendingRun i j =
      descendingRun i k ++ descendingRun ⟨k.val - 1, by have := k.isLt; omega⟩ j := by
  have _ : k.val ≤ i.val := hik
  have _ : j.val < k.val := hjk
  apply List.ext_getElem
  · simp only [List.length_append, length_descendingRun]; omega
  · intro t ht₁ ht₂
    rw [List.getElem_append]
    simp only [descendingRun, List.length_map, List.length_range, List.getElem_map,
      List.getElem_range]
    split_ifs with hlt
    · rfl
    · ext; dsimp only; omega

/-- Peeling the first entry `i` off `descendingRun i j` when `j < i`. -/
theorem descendingRun_cons {i j : Fin m} (h : j < i) :
    descendingRun i j = i :: descendingRun ⟨i.val - 1, by have := i.isLt; omega⟩ j := by
  simpa using descendingRun_split le_rfl h

/-- Peeling the last entry `j` off `descendingRun i j` when `j < i`. -/
theorem descendingRun_concat {i j : Fin m} (h : j < i) :
    descendingRun i j = descendingRun i ⟨j.val + 1, by have := i.isLt; omega⟩ ++ [j] := by
  have hk : (⟨j.val + 1, by have := i.isLt; omega⟩ : Fin m) ≤ i := h
  have hjk : j < (⟨j.val + 1, by have := i.isLt; omega⟩ : Fin m) := Nat.lt_succ_self j.val
  simpa using descendingRun_split hk hjk

/-- Mapping `Fin.castSucc` across a descending run gives the descending run of cast endpoints. -/
@[simp]
theorem map_castSucc_descendingRun (i j : Fin m) :
    (descendingRun i j).map Fin.castSucc = descendingRun i.castSucc j.castSucc := by
  simp [descendingRun, List.map_map, Function.comp_def]

end DescendingRun

/-! ### Words in Jones normal form and their Catalan count -/

/-- A word in **Jones normal form** on `n` strands: a sequence of `(upper, lower)` generator index
pairs `(i₁, j₁), …, (iₚ, jₚ)` in `Fin (n - 1)` with `jₖ ≤ iₖ` for each `k`, strictly increasing
upper indices `i₁ < ⋯ < iₚ`, and strictly increasing lower indices `j₁ < ⋯ < jₚ`. -/
@[ext]
structure NormalWord (n : ℕ) where
  /-- The `(upper, lower)` generator index pairs `(iₖ, jₖ)` of the descending runs. -/
  runs : List (Fin (n - 1) × Fin (n - 1))
  /-- Every run descends: its lower index does not exceed its upper index. -/
  lower_le_upper : ∀ r ∈ runs, r.2 ≤ r.1
  /-- The upper indices of the runs are strictly increasing. -/
  pairwise_upper : (runs.map Prod.fst).Pairwise (· < ·)
  /-- The lower indices of the runs are strictly increasing. -/
  pairwise_lower : (runs.map Prod.snd).Pairwise (· < ·)

namespace NormalWord

variable {n : ℕ}

instance : DecidableEq (NormalWord n) :=
  fun a b ↦ decidable_of_iff (a.runs = b.runs) NormalWord.ext_iff.symm

/-- The empty normal word on `n` strands, spelling `1`. -/
def empty : NormalWord n := ⟨[], by simp, by simp, by simp⟩

instance : Inhabited (NormalWord n) := ⟨empty⟩

/-- The normal word consisting of a single descending run `[i, …, j]` with `j ≤ i`. -/
def run {i j : Fin (n - 1)} (h : j ≤ i) : NormalWord n :=
  ⟨[(i, j)], by simpa using h, by simp, by simp⟩

/-- The single-letter normal word `[i]`, spelling the generator `e δ i`. -/
def single (i : Fin (n - 1)) : NormalWord n := run (le_refl i)

/-- The flat list of generator indices spelled by a normal word, obtained by concatenating its
descending runs. -/
def toList (w : NormalWord n) : List (Fin (n - 1)) :=
  w.runs.flatMap fun r ↦ descendingRun r.1 r.2

/-- The element of `TemperleyLieb R δ n` represented by a normal word `w`. -/
def eval {R : Type*} [CommSemiring R] (δ : R) (w : NormalWord n) : TemperleyLieb R δ n :=
  wordProd δ w.toList

/-- The empty normal word has no runs. -/
@[simp]
theorem runs_empty : (empty : NormalWord n).runs = [] := (rfl)

/-- The empty normal word spells the empty generator list. -/
@[simp]
theorem toList_empty : (empty : NormalWord n).toList = [] := (rfl)

/-- The empty normal word evaluates to `1`. -/
@[simp]
theorem eval_empty {R : Type*} [CommSemiring R] (δ : R) :
    (empty : NormalWord n).eval δ = 1 := (rfl)

/-- A single-run normal word spells `descendingRun i j`. -/
@[simp]
theorem toList_run {i j : Fin (n - 1)} (h : j ≤ i) : (run h).toList = descendingRun i j := by
  simp [toList, run]

/-- Evaluating a single-run normal word evaluates its descending run. -/
@[simp]
theorem eval_run {R : Type*} [CommSemiring R] (δ : R) {i j : Fin (n - 1)} (h : j ≤ i) :
    (run h).eval δ = wordProd δ (descendingRun i j) := by simp [eval]

/-- A single-letter normal word spells the singleton list `[i]`. -/
@[simp]
theorem toList_single (i : Fin (n - 1)) : (single i).toList = [i] := by simp [single]

/-- A single-letter normal word evaluates to the generator `e δ i`. -/
@[simp]
theorem eval_single {R : Type*} [CommSemiring R] (δ : R) (i : Fin (n - 1)) :
    (single i).eval δ = e δ i := by simp [eval]

/-- Include a normal word on `n + 1` strands into `n + 2` strands by shifting all generator indices
along `Fin.castSucc`. -/
def strandIncl (w : NormalWord (n + 1)) : NormalWord (n + 2) where
  runs := w.runs.map (Prod.map Fin.castSucc Fin.castSucc)
  lower_le_upper := by
    intro r hr
    simp only [List.mem_map, Prod.exists] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact Fin.castSucc_le_castSucc_iff.mpr (w.lower_le_upper (i, j) hij)
  pairwise_upper := by
    rw [List.map_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    simpa using List.pairwise_iff_getElem.mp w.pairwise_upper a b (by simpa using ha)
      (by simpa using hb) hab
  pairwise_lower := by
    rw [List.map_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    simpa using List.pairwise_iff_getElem.mp w.pairwise_lower a b (by simpa using ha)
      (by simpa using hb) hab

/-- `NormalWord.strandIncl` is injective. -/
theorem strandIncl_injective : Function.Injective (strandIncl (n := n)) := by
  intro w₁ w₂ h
  have hinj : Function.Injective (Prod.map (Fin.castSucc (n := n)) (Fin.castSucc (n := n))) := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hpair
    exact Prod.ext (Fin.castSucc_injective n (congrArg Prod.fst hpair))
      (Fin.castSucc_injective n (congrArg Prod.snd hpair))
  ext1
  exact List.map_injective_iff.mpr hinj (congrArg NormalWord.runs h)

/-- Including a normal word shifts its underlying generator list by `Fin.castSucc`. -/
@[simp]
theorem toList_strandIncl (w : NormalWord (n + 1)) :
    w.strandIncl.toList = w.toList.map Fin.castSucc := by
  simp [toList, strandIncl, List.flatMap_map, List.map_flatMap]

/-- Evaluating an included normal word agrees with `TemperleyLieb.strandIncl`. -/
@[simp]
theorem eval_strandIncl {R : Type*} [CommSemiring R] (δ : R) (w : NormalWord (n + 1)) :
    w.strandIncl.eval δ = TemperleyLieb.strandIncl (w.eval δ) := by
  rw [eval, eval, toList_strandIncl, strandIncl_wordProd]

/-- One more than the lower endpoint of the last run of `w`, or `0` when `w` is empty. Any run
appended to `w` with a strictly larger upper endpoint must have lower endpoint at least
`w.lowerBound`. -/
def lowerBound (w : NormalWord (n + 1)) : Fin (n + 1) :=
  match w.runs.getLast? with
  | none => 0
  | some r => r.2.succ

/-- The empty normal word has `lowerBound = 0`. -/
@[simp]
theorem lowerBound_empty : (empty : NormalWord (n + 1)).lowerBound = 0 := (rfl)

/-- Including a normal word casts its `lowerBound` via `Fin.castSucc`. -/
@[simp]
theorem lowerBound_strandIncl (w : NormalWord (n + 1)) :
    w.strandIncl.lowerBound = w.lowerBound.castSucc := by
  unfold lowerBound strandIncl
  cases h : w.runs.getLast? <;> simp [List.getLast?_map, h]

/-- Every run of `w` has lower endpoint strictly below `k` whenever `(w.lowerBound : ℕ) ≤ k`. -/
private theorem lower_lt_of_lowerBound_le {w : NormalWord (n + 1)} {k : ℕ}
    (hk : (w.lowerBound : ℕ) ≤ k) {r : Fin n × Fin n} (hr : r ∈ w.runs) :
    (r.2 : ℕ) < k := by
  have hne : w.runs ≠ [] := List.ne_nil_of_mem hr
  have hget : w.runs.getLast? = some (w.runs.getLast hne) :=
    List.getLast?_eq_getLast_of_ne_nil hne
  have hbound : ((w.runs.getLast hne).2 : ℕ) + 1 ≤ k := by simpa [lowerBound, hget] using hk
  have hsplit := List.dropLast_append_getLast hne
  rw [← hsplit, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · have hpw := w.pairwise_lower
    rw [← hsplit, List.map_append, List.pairwise_append] at hpw
    have hlt : (r.2 : ℕ) < ((w.runs.getLast hne).2 : ℕ) :=
      hpw.2.2 r.2 (List.mem_map_of_mem hr) (w.runs.getLast hne).2 (by simp)
    omega
  · omega

/-- Append a final descending run `(Fin.last n, j)` to an included normal word `w` satisfying
`(w.lowerBound : ℕ) ≤ j`. -/
def snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1)) (hw : (w.lowerBound : ℕ) ≤ j) :
    NormalWord (n + 2) where
  runs := w.strandIncl.runs ++ [((Fin.last n, j) : Fin (n + 2 - 1) × Fin (n + 2 - 1))]
  lower_le_upper := by
    intro r hr
    rw [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact w.strandIncl.lower_le_upper r hr
    · exact Fin.le_last j
  pairwise_upper := by
    rw [List.map_append, List.map_singleton, List.pairwise_append]
    refine ⟨w.strandIncl.pairwise_upper, by simp, fun a ha b hb ↦ ?_⟩
    rw [strandIncl, List.map_map, List.mem_map] at ha
    obtain ⟨r, _, rfl⟩ := ha
    rw [List.mem_singleton] at hb
    rcases hb with rfl
    exact Fin.castSucc_lt_last r.1
  pairwise_lower := by
    rw [List.map_append, List.map_singleton, List.pairwise_append]
    refine ⟨w.strandIncl.pairwise_lower, by simp, fun a ha b hb ↦ ?_⟩
    rw [strandIncl, List.map_map, List.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    rw [List.mem_singleton] at hb
    rcases hb with rfl
    exact lower_lt_of_lowerBound_le hw hr

/-- Appending `(Fin.last n, j)` sets `lowerBound` to `j.succ`. -/
@[simp]
theorem lowerBound_snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1))
    (hw : (w.lowerBound : ℕ) ≤ j) :
    (snocLast j w hw).lowerBound = j.succ := by
  simp [lowerBound, snocLast]

/-- Unshift a normal word on `n + 2` strands whose runs never use `Fin.last n` as an upper
endpoint. -/
private def unstrandIncl (u : NormalWord (n + 2))
    (hu : ∀ r ∈ u.runs, r.1 ≠ Fin.last n) : NormalWord (n + 1) where
  runs := u.runs.attach.map fun ⟨r, hr⟩ ↦
    have hi : r.1 ≠ Fin.last n := hu r hr
    have hj : r.2 ≠ Fin.last n :=
      ((u.lower_le_upper r hr).trans_lt (Fin.lt_last_iff_ne_last.mpr hi)).ne
    (r.1.castPred hi, r.2.castPred hj)
  lower_le_upper := by
    intro r' hr'
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    dsimp only
    exact Fin.castPred_le_castPred_iff.mpr (u.lower_le_upper r hr)
  pairwise_upper := by
    rw [List.map_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    have hlt := List.pairwise_iff_getElem.mp u.pairwise_upper a b (by simpa using ha)
      (by simpa using hb) hab
    simp only [List.getElem_map, List.getElem_attach, Function.comp_apply] at hlt ⊢
    exact Fin.castPred_lt_castPred_iff.mpr hlt
  pairwise_lower := by
    rw [List.map_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    have hlt := List.pairwise_iff_getElem.mp u.pairwise_lower a b (by simpa using ha)
      (by simpa using hb) hab
    simp only [List.getElem_map, List.getElem_attach, Function.comp_apply] at hlt ⊢
    exact Fin.castPred_lt_castPred_iff.mpr hlt

private theorem strandIncl_unstrandIncl (u : NormalWord (n + 2))
    (hu : ∀ r ∈ u.runs, r.1 ≠ Fin.last n) :
    (unstrandIncl u hu).strandIncl = u := by
  ext1
  simp only [strandIncl, unstrandIncl, List.map_map, Function.comp_def, Prod.map_apply,
    Fin.castSucc_castPred]
  exact List.attach_map_subtype_val u.runs

private theorem unstrandIncl_strandIncl (w : NormalWord (n + 1)) (hw) :
    unstrandIncl w.strandIncl hw = w :=
  strandIncl_injective (strandIncl_unstrandIncl w.strandIncl hw)

/-- Drop the final run of a normal word. -/
private def dropLastRun (u : NormalWord (n + 2)) : NormalWord (n + 2) where
  runs := u.runs.dropLast
  lower_le_upper := fun r hr ↦ u.lower_le_upper r (List.mem_of_mem_dropLast hr)
  pairwise_upper := u.pairwise_upper.sublist ((List.dropLast_sublist _).map _)
  pairwise_lower := u.pairwise_lower.sublist ((List.dropLast_sublist _).map _)

private theorem dropLastRun_upper_ne_last (u : NormalWord (n + 2)) :
    ∀ r ∈ (dropLastRun u).runs, r.1 ≠ Fin.last n := by
  intro r hr
  have hne : u.runs ≠ [] := fun h ↦ by simp [dropLastRun, h] at hr
  have hpw := u.pairwise_upper
  rw [← List.dropLast_append_getLast hne, List.map_append, List.pairwise_append] at hpw
  have hlt : r.1 < (u.runs.getLast hne).1 :=
    hpw.2.2 r.1 (List.mem_map_of_mem hr) (u.runs.getLast hne).1 (by simp)
  exact (hlt.trans_le (Fin.le_last _)).ne

private theorem dropLastRun_lowerBound_le (u : NormalWord (n + 2)) (hne : u.runs ≠ []) :
    ((unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)).lowerBound : ℕ) ≤
      (u.runs.getLast hne).2 := by
  have hw₀ := strandIncl_unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)
  have hbound : ((unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)).lowerBound : ℕ) =
      ((dropLastRun u).lowerBound : ℕ) := by
    simpa [lowerBound_strandIncl] using congrArg (fun w ↦ (w.lowerBound : ℕ)) hw₀
  rw [hbound]
  unfold lowerBound dropLastRun
  cases hdl : u.runs.dropLast.getLast? with
  | none => exact Nat.zero_le _
  | some r =>
    have hrmem : r ∈ u.runs.dropLast := List.mem_of_getLast? hdl
    have hpw := u.pairwise_lower
    rw [← List.dropLast_append_getLast hne, List.map_append, List.pairwise_append] at hpw
    exact hpw.2.2 r.2 (List.mem_map_of_mem hrmem) (u.runs.getLast hne).2 (by simp)

/-- Inverse map of `stepEquiv`, splitting off a final `(Fin.last n, j)` run when present. -/
private def stepEquivInv (u : NormalWord (n + 2)) :
    NormalWord (n + 1) ⊕
      (Σ j : Fin (n + 1), {w : NormalWord (n + 1) // (w.lowerBound : ℕ) ≤ j}) :=
  if hne : u.runs = [] then
    Sum.inl empty
  else if hlast : (u.runs.getLast hne).1 = Fin.last n then
    Sum.inr ⟨(u.runs.getLast hne).2,
      unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u),
      dropLastRun_lowerBound_le u hne⟩
  else
    Sum.inl <| unstrandIncl u fun r hr ↦ by
      rw [← List.dropLast_append_getLast hne, List.mem_append, List.mem_singleton] at hr
      exact hr.elim (dropLastRun_upper_ne_last u r) fun h ↦ h ▸ hlast

/-- Branching equivalence for normal words on `n + 2` strands according to whether `Fin.last n`
occurs as the upper endpoint of the last run. -/
def stepEquiv (n : ℕ) :
    NormalWord (n + 1) ⊕
      (Σ j : Fin (n + 1), {w : NormalWord (n + 1) // (w.lowerBound : ℕ) ≤ j}) ≃
      NormalWord (n + 2) where
  toFun
    | Sum.inl w => w.strandIncl
    | Sum.inr ⟨j, w, hw⟩ => snocLast j w hw
  invFun := stepEquivInv
  left_inv := by
    have hsigma : ∀ {j₁ j₂ : Fin (n + 1)} {w₁ w₂ : NormalWord (n + 1)}
        {h₁ : (w₁.lowerBound : ℕ) ≤ j₁} {h₂ : (w₂.lowerBound : ℕ) ≤ j₂},
        j₁ = j₂ → w₁ = w₂ →
        (⟨j₁, ⟨w₁, h₁⟩⟩ : Σ j : Fin (n + 1), {w : NormalWord (n + 1) // (w.lowerBound : ℕ) ≤ j}) =
          ⟨j₂, ⟨w₂, h₂⟩⟩ := by
      rintro _ _ _ _ _ _ rfl rfl; rfl
    rintro (w | ⟨j, w, hw⟩) <;> unfold stepEquivInv
    · split_ifs with hne hlast
      · exact congrArg Sum.inl (NormalWord.ext (by simpa [strandIncl] using hne)).symm
      · exfalso
        have hmem := List.getLast_mem hne
        simp only [strandIncl, List.mem_map, Prod.exists] at hmem
        obtain ⟨i, _, _, hEq⟩ := hmem
        exact Fin.castSucc_ne_last i ((congrArg Prod.fst hEq).trans hlast)
      · exact congrArg Sum.inl (unstrandIncl_strandIncl w _)
    · split_ifs with hne hlast
      · simp [snocLast] at hne
      · have hget : (snocLast j w hw).runs.getLast hne =
            ((Fin.last n, j) : Fin (n + 2 - 1) × Fin (n + 2 - 1)) := by simp [snocLast]
        have hdrop : dropLastRun (snocLast j w hw) = w.strandIncl := by
          ext1; simp [dropLastRun, snocLast]
        congr 1
        refine hsigma (congrArg Prod.snd hget) ?_
        simp only [hdrop, unstrandIncl_strandIncl]
      · exact absurd (by simp [snocLast]) hlast
  right_inv u := by
    unfold stepEquivInv
    split_ifs with hne hlast
    · exact NormalWord.ext hne.symm
    · ext1
      simp only [snocLast, strandIncl_unstrandIncl, dropLastRun]
      have hpair : ((Fin.last n, (u.runs.getLast hne).2) :
          Fin (n + 2 - 1) × Fin (n + 2 - 1)) = u.runs.getLast hne :=
        Prod.ext hlast.symm rfl
      rw [hpair, List.dropLast_append_getLast hne]
    · exact strandIncl_unstrandIncl u _

/-- On at most one strand there are no generators, so the empty word is the unique normal word. -/
@[instance_reducible]
def uniqueOfLeOne (h : n ≤ 1) : Unique (NormalWord n) where
  default := empty
  uniq w := by
    ext1
    cases hruns : w.runs with
    | nil => rfl
    | cons r _ => exact absurd r.1.isLt (by omega)

instance : Fintype (NormalWord n) := by
  induction n with
  | zero =>
    letI := uniqueOfLeOne (n := 0) (Nat.zero_le 1)
    exact Fintype.ofSubsingleton empty
  | succ m ih =>
    cases m with
    | zero =>
      letI := uniqueOfLeOne (n := 1) le_rfl
      exact Fintype.ofSubsingleton empty
    | succ k =>
      letI : Fintype (NormalWord (k + 1)) := ih
      exact Fintype.ofEquiv _ (stepEquiv k)

/-- Cumulative count of normal words on `m + 1` strands with `lowerBound ≤ b`. -/
private def countLe (m b : ℕ) : ℕ :=
  #{w : NormalWord (m + 1) | (w.lowerBound : ℕ) ≤ b}

private theorem countLe_zero_zero : countLe 0 0 = 1 := by
  have huniq : ∀ w : NormalWord 1, w = empty := (uniqueOfLeOne le_rfl).uniq
  have huniv : (Finset.univ : Finset (NormalWord 1)) = {empty} := by
    ext w; simp [huniq w]
  simp [countLe, huniv]

private theorem countLe_succ (m b : ℕ) :
    countLe (m + 1) b =
      countLe m b +
        ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) ↦ (j : ℕ) + 1 ≤ b), countLe m j := by
  unfold countLe
  simp_rw [← Fintype.card_subtype]
  let P (u : NormalWord (m + 2)) : Prop := (u.lowerBound : ℕ) ≤ b
  have hcongr : Fintype.card {u : NormalWord (m + 2) // P u} =
      Fintype.card {s : NormalWord (m + 1) ⊕
        (Σ j : Fin (m + 1), {w : NormalWord (m + 1) // (w.lowerBound : ℕ) ≤ j}) //
        P (stepEquiv m s)} :=
    Fintype.card_congr (Equiv.subtypeEquiv (stepEquiv m).symm fun _ ↦ by simp)
  rw [hcongr]
  let eSum : {s : NormalWord (m + 1) ⊕
      (Σ j : Fin (m + 1), {w : NormalWord (m + 1) // (w.lowerBound : ℕ) ≤ j}) //
      P (stepEquiv m s)} ≃
      {w : NormalWord (m + 1) // (w.lowerBound : ℕ) ≤ b} ⊕
      (Σ j : {j : Fin (m + 1) // (j : ℕ) + 1 ≤ b},
        {w : NormalWord (m + 1) // (w.lowerBound : ℕ) ≤ j.1}) :=
    { toFun := fun
        | ⟨Sum.inl w, hw⟩ => Sum.inl ⟨w, by simpa [stepEquiv, P] using hw⟩
        | ⟨Sum.inr ⟨j, w, hjw⟩, hw⟩ =>
          Sum.inr ⟨⟨j, by simpa [stepEquiv, P] using hw⟩, ⟨w, hjw⟩⟩
      invFun := fun
        | Sum.inl ⟨w, hw⟩ => ⟨Sum.inl w, by simpa [stepEquiv, P] using hw⟩
        | Sum.inr ⟨⟨j, hj⟩, ⟨w, hjw⟩⟩ => ⟨Sum.inr ⟨j, w, hjw⟩, by simpa [stepEquiv, P] using hj⟩
      left_inv := by rintro (⟨w | ⟨j, w, _⟩, _⟩) <;> rfl
      right_inv := by rintro (⟨w, _⟩ | ⟨⟨j, _⟩, ⟨w, _⟩⟩) <;> rfl }
  rw [Fintype.card_congr eSum, Fintype.card_sum, Fintype.card_sigma]
  congr 1
  exact (Finset.sum_subtype _ (by simp)
    fun j : Fin (m + 1) ↦ Fintype.card {w : NormalWord (m + 1) // (w.lowerBound : ℕ) ≤ j}).symm

private theorem countLe_of_ge (m : ℕ) {b : ℕ} (hb : m ≤ b) :
    countLe m b = Fintype.card (NormalWord (m + 1)) := by
  rw [countLe, filter_true_of_mem fun w _ ↦ (Nat.lt_succ_iff.mp w.lowerBound.isLt).trans hb,
    card_univ]

private theorem countLe_succ_succ (m c : ℕ) (hc : c ≤ m) :
    countLe (m + 1) (c + 1) = countLe (m + 1) c + countLe m (c + 1) := by
  have hfilter :
      Finset.univ.filter (fun j : Fin (m + 1) ↦ (j : ℕ) + 1 ≤ c + 1) =
        insert ⟨c, by omega⟩ (Finset.univ.filter (fun j : Fin (m + 1) ↦ (j : ℕ) + 1 ≤ c)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [countLe_succ, countLe_succ, hfilter, sum_insert (by simp)]
  dsimp only
  rcases lt_or_eq_of_le hc with _ | rfl
  · omega
  · rw [countLe_of_ge c (Nat.le_succ c), countLe_of_ge c le_rfl]
    omega

/-- The cumulative counts `countLe m b` match Catalan's triangle via `TauCeti.halfCount`. -/
private theorem countLe_eq_halfCount :
    ∀ (m b : ℕ), b ≤ m → countLe m b = halfCount (m + 1 + b) (m + 1 - b)
  | 0, 0, _ => by rw [countLe_zero_zero, halfCount_self]
  | 0, _ + 1, hb => by omega
  | m + 1, 0, _ => by
    rw [countLe_succ, filter_false_of_mem (by intro j _; omega), sum_empty, add_zero,
      countLe_eq_halfCount m 0 (Nat.zero_le m)]
    simp only [Nat.add_zero, Nat.sub_zero, halfCount_self]
  | m + 1, c + 1, hb => by
    rw [countLe_succ_succ m c (by omega), countLe_eq_halfCount (m + 1) c (by omega)]
    rcases lt_or_eq_of_le hb with hlt | heq
    · rw [countLe_eq_halfCount m (c + 1) (by omega),
        show m + 1 + 1 + (c + 1) = (m + 2 + c) + 1 by omega,
        show m + 1 + 1 - (c + 1) = (m - c) + 1 by omega,
        show m + 1 + (c + 1) = m + 2 + c by omega,
        show m + 1 - (c + 1) = m - c by omega,
        show m + 1 + 1 - c = (m - c) + 2 by omega, halfCount_succ_succ, add_comm]
    · have hcm : c = m := by omega
      subst hcm
      rw [countLe_of_ge c (Nat.le_succ c), ← countLe_of_ge c le_rfl,
        countLe_eq_halfCount c c le_rfl]
      have hzero : halfCount (c + 1 + c) 1 = halfCount (2 * c + 2) 0 := by
        rw [show 2 * c + 2 = (c + 1 + c) + 1 by omega, halfCount_succ_zero]
      rw [show c + 1 + 1 + (c + 1) = (2 * c + 2) + 1 by omega,
        show c + 1 + 1 - (c + 1) = 1 by omega, show c + 1 + 1 + c = 2 * c + 2 by omega,
        show c + 1 + 1 - c = 2 by omega, show c + 1 - c = 1 by omega, hzero, add_comm]
      exact (halfCount_succ_succ (2 * c + 2) 0).symm

/-- **Catalan count of Jones normal words.** There are `catalan n` words in Jones normal form on
`n` strands. -/
@[simp]
theorem card_eq_catalan (n : ℕ) : Fintype.card (NormalWord n) = catalan n := by
  cases n with
  | zero =>
    rw [catalan_zero, Fintype.card_eq_one_iff]
    exact ⟨empty, (uniqueOfLeOne (Nat.zero_le 1)).uniq⟩
  | succ m =>
    rw [← countLe_of_ge m le_rfl, countLe_eq_halfCount m m le_rfl,
      show m + 1 + m = 2 * m + 1 by omega, show m + 1 - m = 1 by omega, ← halfCount_succ_zero,
      show 2 * m + 1 + 1 = 2 * (m + 1) by omega, halfCount_two_mul_zero]

end NormalWord

/-! ### Run decomposition, reduction, and the Catalan rank bound -/

section Reduction

variable {m : ℕ}

/-- Decompose a generator word into maximal descending-by-one runs `(i, j)`. -/
private def parseRuns : List (Fin m) → List (Fin m × Fin m)
  | [] => []
  | [x] => [(x, x)]
  | x :: y :: rest =>
    match parseRuns (y :: rest) with
    | [] => [(x, x)]
    | (i, j) :: rs =>
      if (y : ℕ) + 1 = x then (x, j) :: rs else (x, x) :: (i, j) :: rs

private theorem parseRuns_cons_nonempty (y : Fin m) (rest : List (Fin m)) :
    ∃ j rs, parseRuns (y :: rest) = (y, j) :: rs := by
  induction rest generalizing y with
  | nil => exact ⟨y, [], rfl⟩
  | cons z rest ih =>
    obtain ⟨j, rs, h⟩ := ih z
    simp only [parseRuns, h]
    split_ifs <;> exact ⟨_, _, rfl⟩

private theorem lower_le_upper_parseRuns (l : List (Fin m)) :
    ∀ r ∈ parseRuns l, r.2 ≤ r.1 := by
  induction l with
  | nil => simp [parseRuns]
  | cons x rest ih =>
    cases rest with
    | nil => simp [parseRuns]
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      have hj : j ≤ y := ih (y, j) (by simp [h])
      have hrs : ∀ r ∈ rs, r.2 ≤ r.1 := fun r hr ↦ ih r (by simp [h, hr])
      simp only [parseRuns, h]
      split_ifs with hyx
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · have : j.val ≤ y.val := hj
          rw [Fin.le_def]; dsimp only; omega
        · exact hrs r hr
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | hr
        · exact le_rfl
        · exact hj
        · exact hrs r hr

private theorem flatMap_parseRuns (l : List (Fin m)) :
    (parseRuns l).flatMap (fun r ↦ descendingRun r.1 r.2) = l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => simp [parseRuns]
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      have hj : j ≤ y := lower_le_upper_parseRuns (y :: tl) (y, j) (by simp [h])
      simp only [parseRuns, h, List.flatMap_cons] at ih ⊢
      split_ifs with hyx
      · have hlt : j < x := by
          have : j.val ≤ y.val := hj
          rw [Fin.lt_def]; omega
        have hpred : (⟨x.val - 1, by have := x.isLt; omega⟩ : Fin m) = y := by
          ext; dsimp only; omega
        rw [List.flatMap_cons, descendingRun_cons hlt, hpred, List.cons_append, ih]
      · simpa [List.flatMap_cons] using ih

/-- Adjacent runs `(i₁, j₁), (i₂, j₂)` produced by `parseRuns` never satisfy `i₂ + 1 = j₁`. -/
private theorem isChain_parseRuns (l : List (Fin m)) :
    (parseRuns l).IsChain fun r₁ r₂ ↦ (r₂.1 : ℕ) + 1 ≠ r₁.2 := by
  induction l with
  | nil => simp [parseRuns]
  | cons x rest ih =>
    cases rest with
    | nil => simp [parseRuns]
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      rw [h] at ih
      simp only [parseRuns, h]
      split_ifs with hyx
      · cases rs with
        | nil => simp
        | cons _ _ =>
          rw [List.isChain_cons_cons] at ih ⊢
          exact ih
      · exact List.isChain_cons_cons.mpr ⟨hyx, ih⟩

/-- Prepending a descending run `[i, …, j]` before `rest` prepends `(i, j)` to `parseRuns` whenever
the first letter of `rest` is not `j - 1`. -/
private theorem parseRuns_descendingRun_append {i j : Fin m} (hji : j ≤ i) {rest : List (Fin m)}
    (hsep : ∀ y rest', rest = y :: rest' → (y : ℕ) + 1 ≠ j) :
    parseRuns (descendingRun i j ++ rest) = (i, j) :: parseRuns rest := by
  obtain ⟨d, hd⟩ : ∃ d, i.val - j.val = d := ⟨_, rfl⟩
  induction d generalizing i with
  | zero =>
    have hij : i = j := by have : j.val ≤ i.val := hji; ext; omega
    subst hij
    rw [descendingRun_self, List.singleton_append]
    cases rest with
    | nil => rfl
    | cons y rest' =>
      obtain ⟨j₂, rs, h⟩ := parseRuns_cons_nonempty y rest'
      simp [parseRuns, h, hsep y rest' rfl]
  | succ d ih =>
    have hlt : j < i := by rw [Fin.lt_def]; omega
    let i' : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hji' : j ≤ i' := by rw [Fin.le_def]; dsimp only [i']; omega
    rw [descendingRun_cons hlt, List.cons_append]
    have hrec := ih hji' (by dsimp only [i']; omega)
    rcases hdl : descendingRun i' j with _ | ⟨y, zs⟩
    · have := congrArg List.length hdl
      simp [length_descendingRun] at this; omega
    · have hy : y = i' := by
        rcases eq_or_lt_of_le hji' with hEq | hlt'
        · rw [← hEq, descendingRun_self, List.cons.injEq] at hdl
          exact hdl.1.symm.trans hEq
        · rw [descendingRun_cons hlt', List.cons.injEq] at hdl
          exact hdl.1.symm
      rw [hdl, List.cons_append] at hrec
      rw [List.cons_append]
      have hyi : (y : ℕ) + 1 = i := by rw [hy]; dsimp only [i']; omega
      simp [parseRuns, hrec, hyi]

/-- Re-parsing the flat generator list of a `NormalWord` recovers its exact list of runs. -/
private theorem parseRuns_toList {n : ℕ} (w : NormalWord n) :
    parseRuns w.toList = w.runs := by
  obtain ⟨runs, hle, hup, hlow⟩ := w
  dsimp only [NormalWord.toList]
  induction runs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.pairwise_cons] at hup hlow
    have hr : r.2 ≤ r.1 := hle r List.mem_cons_self
    rw [List.flatMap_cons, parseRuns_descendingRun_append hr,
      ih (fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)) hup.2 hlow.2]
    intro y rest' hrest
    cases rs with
    | nil => simp at hrest
    | cons r₂ rs' =>
      have hr₂ : r₂.2 ≤ r₂.1 := hle r₂ (List.mem_cons_of_mem _ List.mem_cons_self)
      have hy : y = r₂.1 := by
        rw [List.flatMap_cons] at hrest
        rcases eq_or_lt_of_le hr₂ with hEq | hlt
        · rw [← hEq, descendingRun_self, List.singleton_append, List.cons.injEq] at hrest
          exact hrest.1.symm.trans hEq
        · rw [descendingRun_cons hlt, List.cons_append, List.cons.injEq] at hrest
          exact hrest.1.symm
      have hlt : r.1 < r₂.1 := hup.1 r₂.1 (by simp)
      have _ : r.2.val ≤ r.1.val := hr
      have _ : r.1.val < r₂.1.val := hlt
      rw [hy]; omega

/-- **Distinct normal words spell distinct generator words.** -/
theorem NormalWord.toList_injective {n : ℕ} :
    Function.Injective (NormalWord.toList (n := n)) := by
  intro w₁ w₂ h
  ext1
  rw [← parseRuns_toList w₁, ← parseRuns_toList w₂, h]

/-- Base-`m` lexicographic code of a word in `Fin m`, strictly monotone under lexicographic order
among words of the same length. -/
private def lexCode {m : ℕ} : List (Fin m) → ℕ
  | [] => 0
  | x :: xs => x.val * m ^ xs.length + lexCode xs

private theorem lexCode_lt_pow {m : ℕ} (hm : 0 < m) :
    ∀ l : List (Fin m), lexCode l < m ^ l.length
  | [] => by simp [lexCode]
  | x :: xs => by
    calc
      x.val * m ^ xs.length + lexCode xs < x.val * m ^ xs.length + m ^ xs.length :=
        Nat.add_lt_add_left (lexCode_lt_pow hm xs) _
      _ = (x.val + 1) * m ^ xs.length := by ring
      _ ≤ m * m ^ xs.length := Nat.mul_le_mul_right _ x.isLt
      _ = m ^ (x :: xs).length := by simp [pow_succ']

private theorem lexCode_cons_lt {m : ℕ} {x y : Fin m} (hxy : x < y) {xs ys : List (Fin m)}
    (hlen : xs.length = ys.length) :
    lexCode (x :: xs) < lexCode (y :: ys) := by
  have hm : 0 < m := (Nat.zero_le x.val).trans_lt x.isLt
  simp only [lexCode]
  calc
    x.val * m ^ xs.length + lexCode xs < x.val * m ^ xs.length + m ^ xs.length :=
      Nat.add_lt_add_left (lexCode_lt_pow hm xs) _
    _ = (x.val + 1) * m ^ ys.length := by rw [hlen]; ring
    _ ≤ y.val * m ^ ys.length := Nat.mul_le_mul_right _ hxy
    _ ≤ y.val * m ^ ys.length + lexCode ys := Nat.le_add_right _ _

private theorem lexCode_append {m : ℕ} (u v : List (Fin m)) :
    lexCode (u ++ v) = lexCode u * m ^ v.length + lexCode v := by
  induction u with
  | nil => simp [lexCode]
  | cons x xs ih =>
    simp only [List.cons_append, lexCode, List.length_append, ih, pow_add]
    ring

/-- Strictly smaller `lexCode` on equal-length subwords is preserved by flanking with a common
prefix and suffix. -/
private theorem lexCode_append_lt_append {m : ℕ} (pre : List (Fin m)) {u v : List (Fin m)}
    (post : List (Fin m)) (huv : u.length = v.length) (hlt : lexCode u < lexCode v) :
    lexCode (pre ++ u ++ post) < lexCode (pre ++ v ++ post) := by
  have hm : 0 < m := by
    cases u with
    | nil => cases v <;> simp [lexCode] at huv hlt
    | cons x _ => exact (Nat.zero_le x.val).trans_lt x.isLt
  have hpow : 0 < m ^ post.length := Nat.pow_pos hm
  simp only [lexCode_append, huv]
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left hlt _) hpow) _

section AlgebraicSteps

variable {R : Type*} [CommSemiring R] {δ : R} {n : ℕ}

/-- Distant commutation step: when `(i₂ : ℕ) + 2 ≤ j₁ ≤ i₁`, the leading generator `i₂` of the
second run commutes left past the first run, preserving word length and placing `i₂ < i₁` first. -/
private theorem reduce_distant {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (h₂ : j₂ ≤ i₂) (hdist : (i₂ : ℕ) + 2 ≤ j₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) = wordProd δ mid ∧
      mid.length = (descendingRun i₁ j₁ ++ descendingRun i₂ j₂).length ∧
      lexCode mid < lexCode (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) := by
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, descendingRun i₁ j₁ = i₁ :: t₁ :=
    (eq_or_lt_of_le h₁).elim (fun h ↦ ⟨[], h ▸ descendingRun_self i₁⟩)
      fun h ↦ ⟨_, descendingRun_cons h⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, descendingRun i₂ j₂ = i₂ :: t₂ :=
    (eq_or_lt_of_le h₂).elim (fun h ↦ ⟨[], h ▸ descendingRun_self i₂⟩)
      fun h ↦ ⟨_, descendingRun_cons h⟩
  refine ⟨i₂ :: (descendingRun i₁ j₁ ++ t₂), ?_, ?_, ?_⟩
  · have hcomm := wordProd_mul_e_comm (δ := δ) (x := i₂) (l := descendingRun i₁ j₁)
      fun a ha ↦ Or.inr (hdist.trans (mem_descendingRun h₁ |>.mp ha).1)
    rw [ht₂, wordProd_append, wordProd_cons, ← mul_assoc, hcomm, mul_assoc,
      ← wordProd_append, ← wordProd_cons]
  · simp only [ht₂, List.length_cons, List.length_append]
    omega
  · have hlt : i₂ < i₁ := by have : j₁.val ≤ i₁.val := h₁; rw [Fin.lt_def]; omega
    rw [ht₁, List.cons_append]
    exact lexCode_cons_lt hlt
      (by simp only [ht₂, List.append_eq, List.length_cons, List.length_append]; omega)

/-- Core left zig-zag step: for `j₁ < x`, `descendingRun x j₁` times `e δ x` reduces in length. -/
private theorem reduce_left_zigzag_core {x j₁ : Fin (n - 1)} (h : j₁ < x) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (descendingRun x j₁) * e δ x = wordProd δ mid ∧
      mid.length < (descendingRun x j₁).length + 1 := by
  have _ : j₁.val < x.val := h
  let x₁ : Fin (n - 1) := ⟨x.val - 1, by have := x.isLt; omega⟩
  have hx₁ : (x₁ : ℕ) + 1 = x := by dsimp only [x₁]; omega
  rcases eq_or_lt_of_le (show j₁ ≤ x₁ by rw [Fin.le_def]; dsimp only [x₁]; omega) with hEq | hlt
  · refine ⟨[x], ?_, by simp only [List.length_singleton, length_descendingRun]; omega⟩
    rw [descendingRun_cons h]
    change wordProd δ (x :: descendingRun x₁ j₁) * e δ x = wordProd δ [x]
    rw [hEq, descendingRun_self, wordProd_cons, wordProd_singleton, wordProd_singleton,
      e_mul_e_mul_e (Or.inr hx₁)]
  · let x₂ : Fin (n - 1) := ⟨x.val - 2, by have := x.isLt; omega⟩
    have hx₂ : (⟨x₁.val - 1, by have := x₁.isLt; omega⟩ : Fin (n - 1)) = x₂ := by
      ext; dsimp only [x₁, x₂]; omega
    refine ⟨x :: descendingRun x₂ j₁, ?_, ?_⟩
    · have hcomm := wordProd_mul_e_comm (δ := δ) (x := x) (l := descendingRun x₂ j₁)
        fun a ha ↦ Or.inl <| by
          have ha_le := (mem_descendingRun (show j₁ ≤ x₂ by rw [Fin.le_def]; dsimp only [x₂]; omega)
            |>.mp ha).2
          have : a.val ≤ x₂.val := ha_le
          dsimp only [x₂] at this; omega
      rw [descendingRun_cons h]
      change wordProd δ (x :: descendingRun x₁ j₁) * e δ x = wordProd δ (x :: descendingRun x₂ j₁)
      rw [descendingRun_cons hlt, hx₂, wordProd_cons, wordProd_cons,
        mul_assoc (e δ x), mul_assoc (e δ x₁), hcomm, ← mul_assoc (e δ x₁),
        ← mul_assoc (e δ x), ← mul_assoc (e δ x) (e δ x₁) (e δ x),
        e_mul_e_mul_e (Or.inr hx₁), ← wordProd_cons]
    · simp only [List.length_cons, length_descendingRun]
      have hltv : j₁.val < x₁.val := hlt
      dsimp only [x₁, x₂] at hltv ⊢; omega

/-- Core right zig-zag step: for `j₁ < i₂`, `e δ j₁` times `descendingRun i₂ j₁` reduces in
length. -/
private theorem reduce_right_zigzag_core {i₂ j₁ : Fin (n - 1)} (h : j₁ < i₂) :
    ∃ mid : List (Fin (n - 1)),
      e δ j₁ * wordProd δ (descendingRun i₂ j₁) = wordProd δ mid ∧
      mid.length < (descendingRun i₂ j₁).length + 1 := by
  have _ : j₁.val < i₂.val := h
  let j' : Fin (n - 1) := ⟨j₁.val + 1, by have := i₂.isLt; omega⟩
  have hj' : (j₁ : ℕ) + 1 = j' := rfl
  rcases eq_or_lt_of_le (show j' ≤ i₂ from h) with hEq | hlt
  · refine ⟨[j₁], ?_, by simp only [List.length_singleton, length_descendingRun]; omega⟩
    rw [descendingRun_concat h]
    change e δ j₁ * wordProd δ (descendingRun i₂ j' ++ [j₁]) = wordProd δ [j₁]
    rw [← hEq, descendingRun_self, wordProd_append, wordProd_singleton,
      wordProd_singleton, ← mul_assoc, e_mul_e_mul_e (Or.inl hj')]
  · let j'' : Fin (n - 1) := ⟨j₁.val + 2, by have := i₂.isLt; omega⟩
    have hj'' : (⟨j'.val + 1, by have := i₂.isLt; omega⟩ : Fin (n - 1)) = j'' := rfl
    refine ⟨descendingRun i₂ j'' ++ [j₁], ?_, ?_⟩
    · have hcomm := (wordProd_mul_e_comm (δ := δ) (x := j₁) (l := descendingRun i₂ j'')
        fun a ha ↦ Or.inr (mem_descendingRun (show j'' ≤ i₂ from hlt) |>.mp ha).1).symm
      rw [descendingRun_concat h]
      change e δ j₁ * wordProd δ (descendingRun i₂ j' ++ [j₁]) =
        wordProd δ (descendingRun i₂ j'' ++ [j₁])
      rw [descendingRun_concat hlt, hj'', wordProd_append, wordProd_append,
        wordProd_singleton, wordProd_singleton, ← mul_assoc (e δ j₁),
        ← mul_assoc (e δ j₁) (wordProd δ _), hcomm, mul_assoc (wordProd δ _),
        mul_assoc (wordProd δ _), e_mul_e_mul_e (Or.inl hj'),
        ← wordProd_singleton δ j₁, ← wordProd_append]
    · simp only [List.length_append, List.length_singleton, length_descendingRun]
      have hltv : j'.val < i₂.val := hlt
      dsimp only [j', j''] at hltv ⊢; omega

/-- Left zig-zag reduction on two adjacent runs when `j₁ < i₂ ≤ i₁`. -/
private theorem reduce_left_zigzag {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₂ : j₂ ≤ i₂) (hj₁ : j₁ < i₂) (hi₂ : i₂ ≤ i₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) = wordProd δ mid ∧
      mid.length < (descendingRun i₁ j₁ ++ descendingRun i₂ j₂).length := by
  obtain ⟨tail₂, htail₂⟩ : ∃ tail₂, descendingRun i₂ j₂ = i₂ :: tail₂ :=
    (eq_or_lt_of_le h₂).elim (fun h ↦ ⟨[], h ▸ descendingRun_self i₂⟩)
      fun h ↦ ⟨_, descendingRun_cons h⟩
  obtain ⟨pre₁, hpre₁⟩ : ∃ pre₁, descendingRun i₁ j₁ = pre₁ ++ descendingRun i₂ j₁ := by
    rcases eq_or_lt_of_le hi₂ with rfl | hlt
    · exact ⟨[], rfl⟩
    · let k : Fin (n - 1) := ⟨i₂.val + 1, by have := i₁.isLt; omega⟩
      have hjk : j₁ < k := hj₁.trans (Nat.lt_succ_self i₂.val)
      have hkpred : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin (n - 1)) = i₂ := rfl
      refine ⟨descendingRun i₁ k, ?_⟩
      simpa only [hkpred] using descendingRun_split (show k ≤ i₁ from hlt) hjk
  obtain ⟨mid₀, hmid₀, hlen₀⟩ := reduce_left_zigzag_core (δ := δ) hj₁
  refine ⟨pre₁ ++ mid₀ ++ tail₂, ?_, ?_⟩
  · rw [hpre₁, htail₂, wordProd_append, wordProd_append, wordProd_cons,
      mul_assoc (wordProd δ pre₁), ← mul_assoc (wordProd δ (descendingRun i₂ j₁)), hmid₀,
      ← wordProd_append, ← wordProd_append, List.append_assoc]
  · simp only [hpre₁, htail₂, List.length_append, List.length_cons]
    omega

/-- Right zig-zag reduction on two adjacent runs when `j₂ ≤ j₁ < i₂`. -/
private theorem reduce_right_zigzag {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (hj₁ : j₁ < i₂) (hj₂ : j₂ ≤ j₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) = wordProd δ mid ∧
      mid.length < (descendingRun i₁ j₁ ++ descendingRun i₂ j₂).length := by
  obtain ⟨init₁, hinit₁⟩ : ∃ init₁, descendingRun i₁ j₁ = init₁ ++ [j₁] :=
    (eq_or_lt_of_le h₁).elim (fun h ↦ ⟨[], by simp [h]⟩) fun h ↦ ⟨_, descendingRun_concat h⟩
  obtain ⟨post₂, hpost₂⟩ : ∃ post₂, descendingRun i₂ j₂ = descendingRun i₂ j₁ ++ post₂ :=
    (eq_or_lt_of_le hj₂).elim (fun h ↦ ⟨[], by simp [h]⟩)
      fun h ↦ ⟨_, descendingRun_split hj₁.le h⟩
  obtain ⟨mid₀, hmid₀, hlen₀⟩ := reduce_right_zigzag_core (δ := δ) hj₁
  refine ⟨init₁ ++ mid₀ ++ post₂, ?_, ?_⟩
  · rw [hinit₁, hpost₂, wordProd_append, wordProd_append, wordProd_append, wordProd_singleton,
      mul_assoc (wordProd δ init₁), ← mul_assoc (e δ j₁) (wordProd δ (descendingRun i₂ j₁)),
      hmid₀, ← wordProd_append, ← wordProd_append, List.append_assoc]
  · simp only [hinit₁, hpost₂, List.length_append, List.length_singleton]
    omega

/-- Any adjacent pair of runs `(i₁, j₁), (i₂, j₂)` from `parseRuns` violating `i₁ < i₂ ∧ j₁ < j₂`
reduces either to a scalar multiple of a strictly shorter word or to an equal-length word with a
strictly smaller lexicographic code. -/
private theorem reduce_bad_pair {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (h₂ : j₂ ≤ i₂) (hsep : (i₂ : ℕ) + 1 ≠ j₁) (hbad : ¬ (i₁ < i₂ ∧ j₁ < j₂)) :
    (∃ (c : R) (mid : List (Fin (n - 1))),
        wordProd δ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) = c • wordProd δ mid ∧
        mid.length < (descendingRun i₁ j₁ ++ descendingRun i₂ j₂).length) ∨
      (∃ mid : List (Fin (n - 1)),
        wordProd δ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) = wordProd δ mid ∧
        mid.length = (descendingRun i₁ j₁ ++ descendingRun i₂ j₂).length ∧
        lexCode mid < lexCode (descendingRun i₁ j₁ ++ descendingRun i₂ j₂)) := by
  by_cases hdist : (i₂ : ℕ) + 2 ≤ j₁
  · exact Or.inr (reduce_distant h₁ h₂ hdist)
  · left
    by_cases heq : i₂ = j₁
    · subst heq
      obtain ⟨init₁, hinit₁⟩ : ∃ init₁, descendingRun i₁ i₂ = init₁ ++ [i₂] :=
        (eq_or_lt_of_le h₁).elim (fun h ↦ ⟨[], by simp [h]⟩) fun h ↦ ⟨_, descendingRun_concat h⟩
      obtain ⟨tail₂, htail₂⟩ : ∃ tail₂, descendingRun i₂ j₂ = i₂ :: tail₂ :=
        (eq_or_lt_of_le h₂).elim (fun h ↦ ⟨[], h ▸ descendingRun_self i₂⟩)
          fun h ↦ ⟨_, descendingRun_cons h⟩
      refine ⟨δ, init₁ ++ i₂ :: tail₂, ?_, by simp [hinit₁, htail₂]⟩
      rw [hinit₁, htail₂, wordProd_append, wordProd_append, wordProd_singleton, wordProd_cons,
        mul_assoc (wordProd δ init₁), ← mul_assoc (e δ i₂), e_mul_self, smul_mul_assoc,
        mul_smul_comm, ← wordProd_cons, ← wordProd_append]
    · have hj₁_lt_i₂ : j₁ < i₂ := by
        have : i₂.val ≠ j₁.val := Fin.val_ne_of_ne heq
        rw [Fin.lt_def]; omega
      by_cases hi₂_le_i₁ : i₂ ≤ i₁
      · obtain ⟨mid, hmid, hlen⟩ := reduce_left_zigzag (δ := δ) h₂ hj₁_lt_i₂ hi₂_le_i₁
        exact ⟨1, mid, by simpa using hmid, hlen⟩
      · rw [not_and_or, not_lt, not_lt] at hbad
        obtain ⟨mid, hmid, hlen⟩ := reduce_right_zigzag (δ := δ) h₁ hj₁_lt_i₂
          (hbad.resolve_left hi₂_le_i₁)
        exact ⟨1, mid, by simpa using hmid, hlen⟩

/-- Extract the first adjacent pair violating `P` when `IsChain P rs` fails. -/
private theorem exists_append_not_rel_of_not_isChain {α : Type*} {P : α → α → Prop} :
    ∀ {rs : List α}, ¬ rs.IsChain P → ∃ pre a b post, rs = pre ++ a :: b :: post ∧ ¬ P a b
  | [], h => absurd List.IsChain.nil h
  | [_], h => absurd (List.IsChain.singleton _) h
  | a :: b :: rest, h => by
    classical
    rw [List.isChain_cons_cons] at h
    by_cases hab : P a b
    · obtain ⟨pre, x, y, post, heq, hxy⟩ :=
        exists_append_not_rel_of_not_isChain (fun hc ↦ h ⟨hab, hc⟩)
      exact ⟨a :: pre, x, y, post, by simp [heq], hxy⟩
    · exact ⟨[], a, b, rest, rfl, hab⟩

/-- A word `l` whose runs are not strictly increasing in both endpoints reduces globally either in
word length or in lexicographic code. -/
private theorem reduce_not_isChain (δ : R) {l : List (Fin (n - 1))}
    (hgood : ¬ (parseRuns l).IsChain fun r₁ r₂ ↦ r₁.1 < r₂.1 ∧ r₁.2 < r₂.2) :
    (∃ (c : R) (l' : List (Fin (n - 1))), wordProd δ l = c • wordProd δ l' ∧
        l'.length < l.length) ∨
      (∃ l' : List (Fin (n - 1)), wordProd δ l = wordProd δ l' ∧
        l'.length = l.length ∧ lexCode l' < lexCode l) := by
  obtain ⟨rsPre, ⟨i₁, j₁⟩, ⟨i₂, j₂⟩, rsPost, hrs_eq, hbad⟩ :=
    exists_append_not_rel_of_not_isChain hgood
  have hle := lower_le_upper_parseRuns l
  have h₁ : j₁ ≤ i₁ := hle (i₁, j₁) (by rw [hrs_eq]; simp)
  have h₂ : j₂ ≤ i₂ := hle (i₂, j₂) (by rw [hrs_eq]; simp)
  have hchain := isChain_parseRuns l
  rw [hrs_eq, List.isChain_append] at hchain
  have hsep : (i₂ : ℕ) + 1 ≠ j₁ := (List.isChain_cons_cons.mp hchain.2.1).1
  let pre := rsPre.flatMap fun r ↦ descendingRun r.1 r.2
  let post := rsPost.flatMap fun r ↦ descendingRun r.1 r.2
  have hl_eq : l = pre ++ (descendingRun i₁ j₁ ++ descendingRun i₂ j₂) ++ post := by
    have hf := flatMap_parseRuns l
    rw [hrs_eq, List.flatMap_append, List.flatMap_cons, List.flatMap_cons] at hf
    simpa [pre, post, List.append_assoc] using hf.symm
  rcases reduce_bad_pair (δ := δ) h₁ h₂ hsep hbad with
    ⟨c, mid, hmid_eq, hmid_len⟩ | ⟨mid, hmid_eq, hmid_len, hmid_lex⟩
  · refine Or.inl ⟨c, pre ++ mid ++ post, ?_, ?_⟩
    · rw [hl_eq, wordProd_append, wordProd_append, hmid_eq, mul_smul_comm, smul_mul_assoc,
        ← wordProd_append, ← wordProd_append]
    · rw [hl_eq]
      simp only [List.length_append] at hmid_len ⊢
      omega
  · refine Or.inr ⟨pre ++ mid ++ post, ?_, ?_, ?_⟩
    · rw [hl_eq, wordProd_append, wordProd_append, hmid_eq, ← wordProd_append, ← wordProd_append]
    · rw [hl_eq]
      simp only [List.length_append] at hmid_len ⊢
      omega
    · rw [hl_eq]
      exact lexCode_append_lt_append pre post hmid_len hmid_lex

/-- Every generator word lies in the `R`-span of the evaluations of `NormalWord n`. -/
theorem wordProd_mem_span_range_eval (δ : R) :
    ∀ l : List (Fin (n - 1)),
      wordProd δ l ∈ Submodule.span R (Set.range (NormalWord.eval (R := R) (n := n) δ)) := by
  set M := Submodule.span R (Set.range (NormalWord.eval (R := R) (n := n) δ))
  suffices ∀ len code : ℕ, ∀ l : List (Fin (n - 1)),
      l.length = len → lexCode l = code → wordProd δ l ∈ M from
    fun l ↦ this l.length (lexCode l) l rfl rfl
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih_len =>
    intro code
    induction code using Nat.strong_induction_on with
    | _ code ih_code =>
      intro l hlen hcode
      by_cases hgood : (parseRuns l).IsChain fun r₁ r₂ ↦ r₁.1 < r₂.1 ∧ r₁.2 < r₂.2
      · have hup : ((parseRuns l).map Prod.fst).Pairwise (· < ·) :=
          List.isChain_iff_pairwise.mp (List.isChain_map _ |>.mpr (hgood.imp fun _ _ h ↦ h.1))
        have hlow : ((parseRuns l).map Prod.snd).Pairwise (· < ·) :=
          List.isChain_iff_pairwise.mp (List.isChain_map _ |>.mpr (hgood.imp fun _ _ h ↦ h.2))
        let w : NormalWord n := ⟨parseRuns l, lower_le_upper_parseRuns l, hup, hlow⟩
        have hw : w.eval δ = wordProd δ l := by
          simp [NormalWord.eval, NormalWord.toList, w, flatMap_parseRuns]
        exact hw ▸ Submodule.subset_span ⟨w, rfl⟩
      · rcases reduce_not_isChain δ hgood with
          ⟨c, l', hprod, hlt_len⟩ | ⟨l', hprod, heq_len, hlt_lex⟩
        · rw [hprod]
          exact M.smul_mem c (ih_len l'.length (hlen ▸ hlt_len) (lexCode l') l' rfl rfl)
        · rw [hprod]
          exact ih_code (lexCode l') (hcode ▸ hlt_lex) l' (heq_len.trans hlen) rfl

/-- **Jones normal form spanning theorem.** Over every commutative semiring `R` and for every loop
value `δ : R`, the evaluations of `NormalWord n` span `TemperleyLieb R δ n` as an `R`-module. -/
theorem span_range_eval_eq_top (δ : R) (n : ℕ) :
    Submodule.span R (Set.range (NormalWord.eval (R := R) (n := n) δ)) = ⊤ := by
  rw [eq_top_iff, ← span_range_wordProd_eq_top (R := R) (n := n) δ, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact wordProd_mem_span_range_eval δ l

/-- `TemperleyLieb R δ n` is a finitely generated `R`-module for every commutative semiring `R`,
loop parameter `δ`, and strand count `n`. -/
instance (δ : R) (n : ℕ) : Module.Finite R (TemperleyLieb R δ n) := by
  classical
  exact ⟨⟨Finset.univ.image (NormalWord.eval δ), by simp [span_range_eval_eq_top]⟩⟩

/-- **Catalan rank bound** (cardinal form): over a commutative semiring satisfying
`StrongRankCondition`, the `R`-rank of `TemperleyLieb R δ n` is at most `catalan n`. -/
theorem rank_le_catalan [StrongRankCondition R] (δ : R) (n : ℕ) :
    Module.rank R (TemperleyLieb R δ n) ≤ catalan n := by
  rw [← rank_top, ← span_range_eval_eq_top (R := R) δ n]
  have hcard : Cardinal.mk (Set.range (NormalWord.eval (R := R) (n := n) δ)) ≤ catalan n := by
    simpa [NormalWord.card_eq_catalan] using
      Cardinal.mk_range_le_lift (f := NormalWord.eval (R := R) (n := n) δ)
  exact (rank_span_le _).trans hcard

/-- **Catalan dimension bound.** Over a commutative semiring satisfying `StrongRankCondition`, the
`finrank` of `TemperleyLieb R δ n` is at most `catalan n`. -/
theorem finrank_le_catalan [StrongRankCondition R] (δ : R) (n : ℕ) :
    Module.finrank R (TemperleyLieb R δ n) ≤ catalan n := by
  simpa only [NormalWord.card_eq_catalan] using
    finrank_le_of_span_eq_top (span_range_eval_eq_top (R := R) δ n)

end AlgebraicSteps

end Reduction

/-! ### Exact normal-word bases on up to three strands -/

section SmallBases

variable {R : Type*} [CommSemiring R]

/-- Build a finite `Module.Basis` from a spanning family `v` and a linear coordinate map sending
`v i` to `Pi.single i 1`. -/
private noncomputable def basisOfSpanOfCoord {M ι : Type*} [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι] (v : ι → M) (hspan : Submodule.span R (Set.range v) = ⊤)
    (coord : M →ₗ[R] (ι → R)) (hcoord : ∀ i, coord (v i) = Pi.single i 1) :
    Module.Basis ι R M := by
  let rMap : M →ₗ[R] (ι →₀ R) :=
    (Finsupp.linearEquivFunOnFinite R R ι).symm.toLinearMap.comp coord
  have hleft : ∀ c : ι →₀ R, rMap (Finsupp.linearCombination R v c) = c := by
    have hcomp : rMap.comp (Finsupp.linearCombination R v) = LinearMap.id := by
      ext i j
      simp [rMap, hcoord, Finsupp.single_apply]
    exact fun c ↦ LinearMap.congr_fun hcomp c
  have hright : ∀ x : M, Finsupp.linearCombination R v (rMap x) = x := by
    intro x
    have hx : x ∈ LinearMap.range (Finsupp.linearCombination R v) := by
      rw [Finsupp.range_linearCombination, hspan]; trivial
    obtain ⟨c, rfl⟩ := hx
    rw [hleft]
  exact Module.Basis.ofRepr
    { rMap with
      invFun := Finsupp.linearCombination R v
      left_inv := hright
      right_inv := hleft }

@[simp]
private theorem coe_basisOfSpanOfCoord {M ι : Type*} [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι] (v : ι → M) (hspan : Submodule.span R (Set.range v) = ⊤)
    (coord : M →ₗ[R] (ι → R)) (hcoord : ∀ i, coord (v i) = Pi.single i 1) :
    ⇑(basisOfSpanOfCoord v hspan coord hcoord) = v := by
  ext i
  rw [basisOfSpanOfCoord, Module.Basis.coe_ofRepr]
  simp

/-- On at most one strand, `NormalWord n` forms an `R`-basis of `TemperleyLieb R δ n`. -/
private noncomputable def basisOfLeOne (δ : R) {n : ℕ} (hn : n ≤ 1) :
    Module.Basis (NormalWord n) R (TemperleyLieb R δ n) :=
  basisOfSpanOfCoord (NormalWord.eval δ) (span_range_eval_eq_top δ n)
    { toFun := fun x _ ↦ aug x
      map_add' := fun x y ↦ by ext; simp
      map_smul' := fun r x ↦ by ext; simp }
    fun w ↦ by
      have huniq (v : NormalWord n) : v = NormalWord.empty := (NormalWord.uniqueOfLeOne hn).uniq v
      ext u
      rw [huniq w, huniq u]
      simp

/-- Enumeration `(1, e 0)` of the two normal words on two strands. -/
private def twoStrandWord : Fin 2 → NormalWord 2
  | 0 => NormalWord.empty
  | 1 => NormalWord.single 0

/-- Computable index of a normal word on two strands: `0` for `1`, `1` for `e 0`. -/
private def twoStrandIdx (w : NormalWord 2) : Fin 2 :=
  if w.runs.isEmpty then 0 else 1

private theorem twoStrandIdx_twoStrandWord (k : Fin 2) : twoStrandIdx (twoStrandWord k) = k := by
  fin_cases k <;> rfl

private theorem twoStrandWord_surjective : Function.Surjective twoStrandWord := by
  have hinj : Function.Injective twoStrandWord :=
    Function.LeftInverse.injective twoStrandIdx_twoStrandWord
  have hcard : Fintype.card (Fin 2) = Fintype.card (NormalWord 2) := by
    rw [Fintype.card_fin, NormalWord.card_eq_catalan, catalan_eq_centralBinom_div]; decide
  exact ((Fintype.bijective_iff_injective_and_card twoStrandWord).mpr ⟨hinj, hcard⟩).2

/-- On two strands, the normal words `(1, e δ 0)` form an `R`-basis of `TemperleyLieb R δ 2` over
every commutative semiring `R`. -/
noncomputable def basisTwo (δ : R) : Module.Basis (NormalWord 2) R (TemperleyLieb R δ 2) :=
  basisOfSpanOfCoord (NormalWord.eval δ) (span_range_eval_eq_top δ 2)
    { toFun := fun x w ↦ twoStrandRep δ x (twoStrandIdx w) 0
      map_add' := fun x y ↦ by ext w; simp
      map_smul' := fun r x ↦ by ext w; simp }
    fun w ↦ by
      ext u
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      obtain ⟨i, rfl⟩ := twoStrandWord_surjective w
      obtain ⟨j, rfl⟩ := twoStrandWord_surjective u
      have hinj : Function.Injective twoStrandWord :=
        Function.LeftInverse.injective twoStrandIdx_twoStrandWord
      rw [twoStrandIdx_twoStrandWord, Pi.single_apply]
      simp only [hinj.eq_iff]
      fin_cases i <;> fin_cases j <;> simp [twoStrandWord]

/-- `basisTwo` evaluates each normal word via `NormalWord.eval`. -/
@[simp]
theorem coe_basisTwo (δ : R) : ⇑(basisTwo (R := R) δ) = NormalWord.eval δ :=
  coe_basisOfSpanOfCoord _ _ _ _

/-- The `5 × 5` matrix of left multiplication by `e δ 0` on
`(1, e 0, e 1, e 0 * e 1, e 1 * e 0)`. -/
private def threeStrandMatZero (δ : R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, 0, 0; 1, δ, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 1, δ, 0; 0, 0, 0, 0, 0]

/-- The `5 × 5` matrix of left multiplication by `e δ 1` on
`(1, e 0, e 1, e 0 * e 1, e 1 * e 0)`. -/
private def threeStrandMatOne (δ : R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 1, 0, δ, 1, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, δ]

/-- The five-dimensional left-regular matrix representation of `TemperleyLieb R δ 3` on the five
normal words `(1, e 0, e 1, e 0 * e 1, e 1 * e 0)`. -/
def threeStrandRep (δ : R) : TemperleyLieb R δ 3 →ₐ[R] Matrix (Fin 5) (Fin 5) R :=
  lift ![threeStrandMatZero δ, threeStrandMatOne δ]
    (fun i ↦ by
      fin_cases i <;>
        (ext r c; fin_cases r <;> fin_cases c <;> simp [threeStrandMatZero, threeStrandMatOne]))
    (fun {i j} h ↦ by
      fin_cases i <;> fin_cases j
      · simp at h
      · ext r c; fin_cases r <;> fin_cases c <;> simp [threeStrandMatZero, threeStrandMatOne]
      · ext r c; fin_cases r <;> fin_cases c <;> simp [threeStrandMatZero, threeStrandMatOne]
      · simp at h)
    (fun {i j} h ↦ by fin_cases i <;> fin_cases j <;> simp at h)

/-- `threeStrandRep` sends `e δ 0` to its `5 × 5` left-multiplication matrix. -/
@[simp]
theorem threeStrandRep_e_zero (δ : R) :
    threeStrandRep δ (e δ 0) =
      !![0, 0, 0, 0, 0; 1, δ, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 1, δ, 0; 0, 0, 0, 0, 0] := by
  rw [threeStrandRep, lift_e]; simp [threeStrandMatZero]

/-- `threeStrandRep` sends `e δ 1` to its `5 × 5` left-multiplication matrix. -/
@[simp]
theorem threeStrandRep_e_one (δ : R) :
    threeStrandRep δ (e δ 1) =
      !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 1, 0, δ, 1, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, δ] := by
  rw [threeStrandRep, lift_e]; simp [threeStrandMatOne]

/-- Enumeration `(1, e 0, e 1, e 0 * e 1, e 1 * e 0)` of the five normal words on three strands. -/
private def threeStrandWord : Fin 5 → NormalWord 3
  | 0 => NormalWord.empty
  | 1 => NormalWord.single 0
  | 2 => NormalWord.single 1
  | 3 => ⟨[(0, 0), (1, 1)], by decide, by decide, by decide⟩
  | 4 => NormalWord.run (i := 1) (j := 0) (by decide)

/-- Computable index of a normal word on three strands in `(1, e 0, e 1, e 0 * e 1, e 1 * e 0)`. -/
private def threeStrandIdx (w : NormalWord 3) : Fin 5 :=
  match w.runs with
  | [] => 0 | [(0, 0)] => 1 | [(1, 1)] => 2 | [(0, 0), (1, 1)] => 3 | _ => 4

private theorem threeStrandIdx_threeStrandWord (k : Fin 5) :
    threeStrandIdx (threeStrandWord k) = k := by fin_cases k <;> rfl

private theorem threeStrandWord_surjective : Function.Surjective threeStrandWord := by
  have hinj : Function.Injective threeStrandWord :=
    Function.LeftInverse.injective threeStrandIdx_threeStrandWord
  have hcard : Fintype.card (Fin 5) = Fintype.card (NormalWord 3) := by
    rw [Fintype.card_fin, NormalWord.card_eq_catalan, catalan_eq_centralBinom_div]; decide
  exact ((Fintype.bijective_iff_injective_and_card threeStrandWord).mpr ⟨hinj, hcard⟩).2

private theorem eval_threeStrandWord (δ : R) :
    ((threeStrandWord 0).eval δ = 1) ∧ ((threeStrandWord 1).eval δ = e δ 0) ∧
    ((threeStrandWord 2).eval δ = e δ 1) ∧ ((threeStrandWord 3).eval δ = e δ 0 * e δ 1) ∧
    ((threeStrandWord 4).eval δ = e δ 1 * e δ 0) := by
  refine ⟨by simp [threeStrandWord], by simp [threeStrandWord], by simp [threeStrandWord], ?_, ?_⟩
  · simp [threeStrandWord, NormalWord.eval, NormalWord.toList, wordProd]
  · have hdr : descendingRun (1 : Fin (3 - 1)) 0 = [1, 0] := by
      rw [descendingRun_cons (by decide)]; rfl
    simp [threeStrandWord, hdr, wordProd]

/-- On three strands, the five normal words `(1, e 0, e 1, e 0 * e 1, e 1 * e 0)` form an `R`-basis
of `TemperleyLieb R δ 3` over every commutative semiring `R` and at every loop value `δ`. -/
noncomputable def basisThree (δ : R) : Module.Basis (NormalWord 3) R (TemperleyLieb R δ 3) :=
  basisOfSpanOfCoord (NormalWord.eval δ) (span_range_eval_eq_top δ 3)
    { toFun := fun x w ↦ threeStrandRep δ x (threeStrandIdx w) 0
      map_add' := fun x y ↦ by ext w; simp
      map_smul' := fun r x ↦ by ext w; simp }
    fun w ↦ by
      ext u
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      obtain ⟨i, rfl⟩ := threeStrandWord_surjective w
      obtain ⟨j, rfl⟩ := threeStrandWord_surjective u
      have hinj : Function.Injective threeStrandWord :=
        Function.LeftInverse.injective threeStrandIdx_threeStrandWord
      have hev := eval_threeStrandWord δ
      rw [threeStrandIdx_threeStrandWord, Pi.single_apply]
      simp only [hinj.eq_iff]
      fin_cases i <;> fin_cases j <;>
        simp [hev.1, hev.2.1, hev.2.2.1, hev.2.2.2.1, hev.2.2.2.2]

/-- `basisThree` evaluates each normal word via `NormalWord.eval`. -/
@[simp]
theorem coe_basisThree (δ : R) : ⇑(basisThree (R := R) δ) = NormalWord.eval δ :=
  coe_basisOfSpanOfCoord _ _ _ _

/-- For `n ≤ 3`, the normal words `NormalWord n` form an `R`-basis of `TemperleyLieb R δ n` over
every commutative semiring `R` and for every loop value `δ`. -/
noncomputable def basisOfLeThree (δ : R) {n : ℕ} (hn : n ≤ 3) :
    Module.Basis (NormalWord n) R (TemperleyLieb R δ n) :=
  match n, hn with
  | 0, _ => basisOfLeOne δ (Nat.zero_le 1)
  | 1, _ => basisOfLeOne δ le_rfl
  | 2, _ => basisTwo δ
  | 3, _ => basisThree δ

/-- `basisOfLeThree` evaluates each normal word via `NormalWord.eval`. -/
@[simp]
theorem coe_basisOfLeThree (δ : R) {n : ℕ} (hn : n ≤ 3) :
    ⇑(basisOfLeThree (R := R) δ hn) = NormalWord.eval δ := by
  unfold basisOfLeThree
  rcases n with _ | _ | _ | _ | _
  · exact coe_basisOfSpanOfCoord _ _ _ _
  · exact coe_basisOfSpanOfCoord _ _ _ _
  · exact coe_basisTwo δ
  · exact coe_basisThree δ
  · omega

/-- On at most three strands, `TemperleyLieb R δ n` is a free `R`-module for every commutative
semiring `R` and loop value `δ`. -/
theorem free_of_le_three (δ : R) {n : ℕ} (hn : n ≤ 3) : Module.Free R (TemperleyLieb R δ n) :=
  Module.Free.of_basis (basisOfLeThree δ hn)

/-- On at most three strands, `TemperleyLieb R δ n` has `finrank` equal to `catalan n` over every
commutative semiring satisfying `StrongRankCondition` (in particular over every nontrivial
commutative ring or field). -/
theorem finrank_eq_catalan_of_le_three [StrongRankCondition R] (δ : R) {n : ℕ} (hn : n ≤ 3) :
    Module.finrank R (TemperleyLieb R δ n) = catalan n := by
  rw [Module.finrank_eq_card_basis (basisOfLeThree (R := R) δ hn), NormalWord.card_eq_catalan]

/-- The two-strand Temperley–Lieb algebra has dimension `2` at every loop parameter `δ`. -/
@[simp]
theorem finrank_two [StrongRankCondition R] (δ : R) :
    Module.finrank R (TemperleyLieb R δ 2) = 2 := by
  rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_eq_centralBinom_div]; decide

/-- The three-strand Temperley–Lieb algebra has dimension `5` at every loop parameter `δ`. -/
@[simp]
theorem finrank_three [StrongRankCondition R] (δ : R) :
    Module.finrank R (TemperleyLieb R δ 3) = 5 := by
  rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_eq_centralBinom_div]; decide

/-- Both generators of the three-strand Temperley–Lieb algebra are nonzero over any nontrivial
commutative semiring. -/
theorem e_ne_zero_three [Nontrivial R] {δ : R} (i : Fin (3 - 1)) : e δ i ≠ 0 := by
  intro h
  fin_cases i
  · have h0 : threeStrandRep δ (e δ 0) 1 0 = threeStrandRep δ 0 1 0 :=
      congrArg (fun x ↦ threeStrandRep δ x 1 0) h
    simp at h0
  · have h1 : threeStrandRep δ (e δ 1) 2 0 = threeStrandRep δ 0 2 0 :=
      congrArg (fun x ↦ threeStrandRep δ x 2 0) h
    simp at h1

/-- Adding a straight strand is injective from `1` to `2` strands and from `2` to `3` strands, over
every commutative semiring `R` and at every loop value `δ`. -/
theorem strandIncl_injective_of_le_one (δ : R) {n : ℕ} (hn : n ≤ 1) :
    Function.Injective (strandIncl (R := R) (δ := δ) (n := n)) := by
  let b₁ := basisOfLeThree (R := R) δ (n := n + 1) (by omega)
  let b₂ := basisOfLeThree (R := R) δ (n := n + 2) (by omega)
  let f : TemperleyLieb R δ (n + 1) →ₗ[R] (NormalWord (n + 1) → R) :=
    { toFun := fun x w ↦ b₂.repr (strandIncl x) w.strandIncl
      map_add' := fun x y ↦ by ext w; simp
      map_smul' := fun r x ↦ by ext w; simp }
  let g : TemperleyLieb R δ (n + 1) →ₗ[R] (NormalWord (n + 1) → R) :=
    { toFun := fun x w ↦ b₁.repr x w
      map_add' := fun x y ↦ by ext w; simp
      map_smul' := fun r x ↦ by ext w; simp }
  have hfg : f = g := b₁.ext fun u ↦ by
    ext w
    have hb : strandIncl (b₁ u) = b₂ u.strandIncl := by simp [b₁, b₂]
    simp [f, g, hb, Finsupp.single_apply, NormalWord.strandIncl_injective.eq_iff]
  intro x y hxy
  apply b₁.repr.injective
  ext w
  have hx : f x = f y := by simp [f, hxy]
  rw [hfg] at hx
  exact congr_fun hx w

end SmallBases

end TauCeti.TemperleyLieb
