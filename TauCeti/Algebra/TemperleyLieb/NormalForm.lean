/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Algebra.TemperleyLieb.Basic
public import TauCeti.Data.Fin.DescendingRun
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Shortlex
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Nonsingular
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

Any generator word `l` decomposes uniquely into maximal descending-by-one runs via
`List.parseDescendingRuns` with `(iₖ₊₁ : ℕ) + 1 ≠ jₖ`. If `l` is not in Jones normal form, its first
adjacent pair `(i₁, j₁)`, `(i₂, j₂)` violating `i₁ < i₂ ∧ j₁ < j₂` reduces strictly in
`List.Shortlex`: by distant commutation (`(i₂ : ℕ) + 2 ≤ j₁`, preserving length and strictly
decreasing lexicographic order), quadratic absorption (`i₂ = j₁`, decreasing length by `1`), or
left/right zig-zag absorption (`e i * e (i ± 1) * e i = e i`, decreasing length by `2`), expressing
every generator word as `δ ^ k • w.eval δ` (`exists_wordProd_eq_pow_smul_eval`). On `n ≤ 3` strands,
reading off the first column of the faithful matrix representations (`algEquivOfLeOne`,
`twoStrandRep`, and the `5 × 5` left-regular representation `threeStrandRep`) supplies an `R`-linear
left inverse, proving that `NormalWord n` forms an `R`-basis of `TemperleyLieb R δ n` over every
commutative semiring `R` (`basisOfLeThree`).

## Main definitions and results

* `TauCeti.TemperleyLieb.wordProd`: generator word products `(l.map (e δ)).prod` on
  `List (Fin (n - 1))`.
* `TauCeti.TemperleyLieb.NormalWord`, `NormalWord.eval`, `NormalWord.strandIncl`,
  `NormalWord.snocLast`, `NormalWord.stepEquiv`: Jones normal words, their evaluation, strand
  inclusion, final-run extension, and Catalan branching equivalence.
* `TauCeti.TemperleyLieb.NormalWord.toList_injective`,
  `TauCeti.TemperleyLieb.NormalWord.card_eq_catalan`: normal words spell distinct generator lists
  and have cardinality `catalan n`.
* `TauCeti.TemperleyLieb.exists_wordProd_eq_pow_smul_eval`,
  `TauCeti.TemperleyLieb.span_range_eval_eq_top`, `TauCeti.TemperleyLieb.rank_le_catalan`,
  `TauCeti.TemperleyLieb.finrank_le_catalan`: monomial reduction to Jones normal form, spanning by
  normal words, and the Catalan rank bound.
* `TauCeti.TemperleyLieb.threeStrandRep`, `TauCeti.TemperleyLieb.twoStrandRep_injective`,
  `TauCeti.TemperleyLieb.threeStrandRep_injective`, `TauCeti.TemperleyLieb.basisTwo`,
  `TauCeti.TemperleyLieb.basisThree`, `TauCeti.TemperleyLieb.basisOfLeThree`: faithful low-strand
  matrix representations and exact bases on up to three strands, yielding `free_of_le_three`,
  `finrank_zero`, `finrank_one`, `finrank_two`, `finrank_three`, `e_ne_zero_of_le_three`, and
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

/-! ### Generator words -/

section WordProd

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The product `e δ i₁ * ⋯ * e δ iₖ` of Temperley–Lieb generators spelled by a word
`l : List (Fin (n - 1))`. -/
def wordProd (δ : R) (l : List (Fin (n - 1))) : TemperleyLieb R δ n :=
  (l.map (e δ)).prod

/-- `wordProd δ l` is the list product `(l.map (e δ)).prod`. -/
theorem wordProd_def (δ : R) (l : List (Fin (n - 1))) :
    wordProd δ l = (l.map (e δ)).prod := (rfl)

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
    aug (wordProd (R := R) δ l) = if l = [] then 1 else 0 := by
  cases l <;> simp

/-- Products of generators span `TemperleyLieb R δ n` as an `R`-module. -/
theorem span_range_wordProd_eq_top (δ : R) :
    Submodule.span R (Set.range (wordProd (R := R) (n := n) δ)) = ⊤ := by
  have hrange : Set.range (wordProd (R := R) (n := n) δ) =
      (Submonoid.closure (Set.range (e (R := R) (n := n) δ)) : Set _) := by
    rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
    ext x
    simp [FreeMonoid.exists, FreeMonoid.lift_ofList, wordProd_def]
  rw [hrange, ← Algebra.adjoin_eq_span, adjoin_range_e, Algebra.top_toSubmodule]

/-- If every letter of `l` is at distance at least `2` from `x`, then `e δ x` commutes past
`wordProd δ l`. -/
private theorem wordProd_mul_e_comm {δ : R} {x : Fin (n - 1)} {l : List (Fin (n - 1))}
    (h : ∀ a ∈ l, (a : ℕ) + 2 ≤ x ∨ (x : ℕ) + 2 ≤ a) :
    wordProd δ l * e δ x = e δ x * wordProd δ l :=
  (Commute.list_prod_left _ _ <| List.forall_mem_map.mpr fun a ha ↦ commute_e (h a ha)).eq

end WordProd

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

/-- The default `NormalWord n` is `NormalWord.empty`. -/
@[simp]
theorem default_eq_empty : (default : NormalWord n) = empty := (rfl)

/-- The normal word consisting of a single descending run `[i, …, j]` with `j ≤ i`. -/
def run {i j : Fin (n - 1)} (h : j ≤ i) : NormalWord n :=
  ⟨[(i, j)], by simpa using h, by simp, by simp⟩

/-- The single-letter normal word `[i]`, spelling the generator `e δ i`. -/
def single (i : Fin (n - 1)) : NormalWord n := run (le_refl i)

/-- The flat list of generator indices spelled by a normal word, obtained by concatenating its
descending runs. -/
def toList (w : NormalWord n) : List (Fin (n - 1)) :=
  w.runs.flatMap fun r ↦ Fin.descendingRun r.1 r.2

/-- Explicit `List.flatMap` formula for `NormalWord.toList`. -/
theorem toList_def (w : NormalWord n) :
    w.toList = w.runs.flatMap fun r ↦ Fin.descendingRun r.1 r.2 := (rfl)

/-- The element of `TemperleyLieb R δ n` represented by a normal word `w`. -/
def eval {R : Type*} [CommSemiring R] (δ : R) (w : NormalWord n) : TemperleyLieb R δ n :=
  wordProd δ w.toList

/-- `NormalWord.eval` evaluates the underlying generator list via `wordProd`. -/
theorem eval_def {R : Type*} [CommSemiring R] (δ : R) (w : NormalWord n) :
    w.eval δ = wordProd δ w.toList := (rfl)

/-- The empty normal word has no runs. -/
@[simp]
theorem runs_empty : (empty : NormalWord n).runs = [] := (rfl)

/-- A normal word has no runs if and only if it is `NormalWord.empty`. -/
@[simp]
theorem runs_eq_nil {w : NormalWord n} : w.runs = [] ↔ w = empty := by
  rw [NormalWord.ext_iff, runs_empty]

/-- The empty normal word spells the empty generator list. -/
@[simp]
theorem toList_empty : (empty : NormalWord n).toList = [] := (rfl)

/-- A normal word spells the empty generator list if and only if it is `NormalWord.empty`. -/
@[simp]
theorem toList_eq_nil {w : NormalWord n} : w.toList = [] ↔ w = empty := by
  rw [toList_def, List.flatMap_eq_nil_iff]
  refine ⟨fun h ↦ runs_eq_nil.mp ?_, fun h ↦ by simp [h]⟩
  cases hruns : w.runs with
  | nil => rfl
  | cons r _ =>
    exact absurd (Fin.descendingRun_eq_nil.mp (h r (by simp [hruns])))
      (not_lt_of_ge (w.lower_le_upper r (by simp [hruns])))

/-- The empty normal word evaluates to `1`. -/
@[simp]
theorem eval_empty {R : Type*} [CommSemiring R] (δ : R) :
    (empty : NormalWord n).eval δ = 1 := (rfl)

/-- A single-run normal word has `[(i, j)]` as its list of runs. -/
@[simp]
theorem runs_run {i j : Fin (n - 1)} (h : j ≤ i) : (run h).runs = [(i, j)] := (rfl)

/-- A single-run normal word spells `Fin.descendingRun i j`. -/
@[simp]
theorem toList_run {i j : Fin (n - 1)} (h : j ≤ i) : (run h).toList = Fin.descendingRun i j := by
  simp [toList, run]

/-- Evaluating a single-run normal word evaluates its descending run. -/
@[simp]
theorem eval_run {R : Type*} [CommSemiring R] (δ : R) {i j : Fin (n - 1)} (h : j ≤ i) :
    (run h).eval δ = wordProd δ (Fin.descendingRun i j) := by simp [eval]

/-- A single-letter normal word has `[(i, i)]` as its list of runs. -/
@[simp]
theorem runs_single (i : Fin (n - 1)) : (single i).runs = [(i, i)] := (rfl)

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
    rw [List.map_map, List.pairwise_map]
    exact (List.pairwise_map.mp w.pairwise_upper).imp Fin.castSucc_lt_castSucc_iff.mpr
  pairwise_lower := by
    rw [List.map_map, List.pairwise_map]
    exact (List.pairwise_map.mp w.pairwise_lower).imp Fin.castSucc_lt_castSucc_iff.mpr

/-- `NormalWord.strandIncl` maps both endpoints of each run by `Fin.castSucc`. -/
@[simp]
theorem runs_strandIncl (w : NormalWord (n + 1)) :
    w.strandIncl.runs = w.runs.map (Prod.map Fin.castSucc Fin.castSucc) := (rfl)

/-- Including the empty normal word gives the empty normal word. -/
@[simp]
theorem strandIncl_empty : (empty : NormalWord (n + 1)).strandIncl = empty := by
  ext1; simp

/-- `NormalWord.strandIncl` is injective. -/
@[grind inj]
theorem strandIncl_injective : Function.Injective (strandIncl (n := n)) := by
  intro w₁ w₂ h
  ext1
  exact List.map_injective_iff.mpr
    ((Fin.castSucc_injective n).prodMap (Fin.castSucc_injective n))
    (congrArg NormalWord.runs h)

/-- Two normal words have equal `strandIncl` if and only if they are equal. -/
@[simp]
theorem strandIncl_inj {w₁ w₂ : NormalWord (n + 1)} :
    w₁.strandIncl = w₂.strandIncl ↔ w₁ = w₂ :=
  strandIncl_injective.eq_iff

/-- An included normal word is `NormalWord.empty` if and only if the original normal word is
`NormalWord.empty`. -/
@[simp]
theorem strandIncl_eq_empty {w : NormalWord (n + 1)} :
    w.strandIncl = empty ↔ w = empty := by
  rw [← strandIncl_empty, strandIncl_inj]

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

/-- Explicit `List.getLast?` formula for `NormalWord.lowerBound`. -/
theorem lowerBound_def (w : NormalWord (n + 1)) :
    w.lowerBound =
      match w.runs.getLast? with
      | none => 0
      | some r => r.2.succ := (rfl)

/-- The empty normal word has `lowerBound = 0`. -/
@[simp]
theorem lowerBound_empty : (empty : NormalWord (n + 1)).lowerBound = 0 := (rfl)

/-- A single-run normal word from `i` down to `j` has `lowerBound = j.succ`. -/
@[simp]
theorem lowerBound_run {i j : Fin n} (h : j ≤ i) :
    (run (n := n + 1) h).lowerBound = j.succ := (rfl)

/-- A single-letter normal word `[i]` has `lowerBound = i.succ`. -/
@[simp]
theorem lowerBound_single (i : Fin n) :
    (single (n := n + 1) i).lowerBound = i.succ := (rfl)

/-- Including a normal word casts its `lowerBound` via `Fin.castSucc`. -/
@[simp]
theorem lowerBound_strandIncl (w : NormalWord (n + 1)) :
    w.strandIncl.lowerBound = w.lowerBound.castSucc := by
  unfold lowerBound strandIncl
  cases h : w.runs.getLast? <;> simp [List.getLast?_map, h]

/-- `(w.lowerBound : ℕ) ≤ k` holds if and only if every run of `w` has lower endpoint strictly
below `k`. -/
theorem val_lowerBound_le_iff {w : NormalWord (n + 1)} {k : ℕ} :
    (w.lowerBound : ℕ) ≤ k ↔ ∀ r ∈ w.runs, (r.2 : ℕ) < k := by
  refine ⟨fun hk r hr ↦ ?_, fun h ↦ ?_⟩
  · have hne : w.runs ≠ [] := List.ne_nil_of_mem hr
    have hbound : ((w.runs.getLast hne).2 : ℕ) + 1 ≤ k := by
      simpa [lowerBound, List.getLast?_eq_getLast_of_ne_nil hne] using hk
    have hle : r.2 ≤ (w.runs.getLast hne).2 := by
      simpa [List.getLast_map] using
        (w.pairwise_lower.imp le_of_lt).rel_getLast (List.mem_map_of_mem hr)
    have _ := Fin.le_def.mp hle
    omega
  · rw [lowerBound_def]
    cases hget : w.runs.getLast? with
    | none => exact Nat.zero_le k
    | some r =>
      have hr : (r.2 : ℕ) < k := h r (List.mem_of_getLast? hget)
      rw [Fin.val_succ]
      omega

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
    simp only [Function.comp_apply, Prod.map_snd, Fin.lt_def, Fin.val_castSucc]
    exact val_lowerBound_le_iff.mp hw r hr

/-- `NormalWord.snocLast` appends `(Fin.last n, j)` after the cast runs of `w`. -/
@[simp]
theorem runs_snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1))
    (hw : (w.lowerBound : ℕ) ≤ j) :
    (snocLast j w hw).runs =
      w.runs.map (Prod.map (Fin.castSucc (n := n)) (Fin.castSucc (n := n))) ++
        [(Fin.last n, j)] := by
  simp [snocLast]

/-- `NormalWord.snocLast` appends `Fin.descendingRun (Fin.last n) j` to the cast generator list of
`w`. -/
@[simp]
theorem toList_snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1))
    (hw : (w.lowerBound : ℕ) ≤ j) :
    (snocLast j w hw).toList =
      w.toList.map (Fin.castSucc (n := n)) ++ Fin.descendingRun (Fin.last n) j := by
  rw [toList_def, snocLast, List.flatMap_append, List.flatMap_singleton, ← toList_def,
    toList_strandIncl]

/-- Evaluating `NormalWord.snocLast j w hw` right-multiplies `strandIncl (w.eval δ)` by the
descending run from `Fin.last n` to `j`. -/
@[simp]
theorem eval_snocLast {R : Type*} [CommSemiring R] (δ : R) (j : Fin (n + 1))
    (w : NormalWord (n + 1)) (hw : (w.lowerBound : ℕ) ≤ j) :
    (snocLast j w hw).eval δ =
      TemperleyLieb.strandIncl (w.eval δ) * wordProd δ (Fin.descendingRun (Fin.last n) j) := by
  rw [eval_def, toList_snocLast, wordProd_append, ← strandIncl_wordProd, ← eval_def]

/-- Appending `(Fin.last n, j)` sets `lowerBound` to `j.succ`. -/
@[simp]
theorem lowerBound_snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1))
    (hw : (w.lowerBound : ℕ) ≤ j) :
    (snocLast j w hw).lowerBound = j.succ := by
  simp [lowerBound, snocLast]

/-- A normal word built by `NormalWord.snocLast` is never `NormalWord.empty`. -/
@[simp]
theorem snocLast_ne_empty {j : Fin (n + 1)} {w : NormalWord (n + 1)}
    {hw : (w.lowerBound : ℕ) ≤ j} : snocLast j w hw ≠ empty :=
  ne_of_apply_ne NormalWord.runs (by simp)

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
    have h := List.pairwise_map.mp u.pairwise_upper
    rw [← List.attach_map_subtype_val u.runs, List.pairwise_map] at h
    rw [List.map_map, List.pairwise_map]
    exact h.imp fun hlt ↦ by simpa only [Function.comp_def, Fin.castPred_lt_castPred_iff] using hlt
  pairwise_lower := by
    have h := List.pairwise_map.mp u.pairwise_lower
    rw [← List.attach_map_subtype_val u.runs, List.pairwise_map] at h
    rw [List.map_map, List.pairwise_map]
    exact h.imp fun hlt ↦ by simpa only [Function.comp_def, Fin.castPred_lt_castPred_iff] using hlt

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
  have hne : u.runs ≠ [] := List.ne_nil_of_mem (List.dropLast_subset _ hr)
  have hlt : r.1 < (u.runs.getLast hne).1 := by
    simpa [List.getLast_map] using
      u.pairwise_upper.rel_dropLast_getLast (List.map_dropLast ▸ List.mem_map_of_mem hr)
  exact (hlt.trans_le (Fin.le_last _)).ne

private theorem dropLastRun_lowerBound_le (u : NormalWord (n + 2)) (hne : u.runs ≠ []) :
    ((unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)).lowerBound : ℕ) ≤
      (u.runs.getLast hne).2 := by
  have hw₀ := strandIncl_unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)
  have hbound : ((unstrandIncl (dropLastRun u) (dropLastRun_upper_ne_last u)).lowerBound : ℕ) =
      ((dropLastRun u).lowerBound : ℕ) := by
    simpa [lowerBound_strandIncl] using congrArg (fun w ↦ (w.lowerBound : ℕ)) hw₀
  rw [hbound, val_lowerBound_le_iff]
  intro r hr
  have hlt : r.2 < (u.runs.getLast hne).2 := by
    simpa [List.getLast_map] using
      u.pairwise_lower.rel_dropLast_getLast (List.map_dropLast ▸ List.mem_map_of_mem hr)
  exact Fin.lt_def.mp hlt

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
    | Sum.inr s => snocLast s.1 s.2.1 s.2.2
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
      · exact congrArg Sum.inl (strandIncl_eq_empty.mp (runs_eq_nil.mp hne)).symm
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
    · exact (runs_eq_nil.mp hne).symm
    · ext1
      simp only [snocLast, strandIncl_unstrandIncl, dropLastRun]
      have hpair : ((Fin.last n, (u.runs.getLast hne).2) :
          Fin (n + 2 - 1) × Fin (n + 2 - 1)) = u.runs.getLast hne :=
        Prod.ext hlast.symm rfl
      rw [hpair, List.dropLast_append_getLast hne]
    · exact strandIncl_unstrandIncl u _

/-- `NormalWord.stepEquiv` sends `Sum.inl w` to `w.strandIncl`. -/
@[simp]
theorem stepEquiv_inl (w : NormalWord (n + 1)) :
    stepEquiv n (Sum.inl w) = w.strandIncl := (rfl)

/-- `NormalWord.stepEquiv` sends `Sum.inr s` to `snocLast s.1 s.2.1 s.2.2`. -/
@[simp]
theorem stepEquiv_inr
    (s : Σ j : Fin (n + 1), {w : NormalWord (n + 1) // (w.lowerBound : ℕ) ≤ j}) :
    stepEquiv n (Sum.inr s) = snocLast s.1 s.2.1 s.2.2 := (rfl)

/-- `(NormalWord.stepEquiv n).symm` recovers `Sum.inl w` on `w.strandIncl`. -/
@[simp]
theorem stepEquiv_symm_strandIncl (w : NormalWord (n + 1)) :
    (stepEquiv n).symm w.strandIncl = Sum.inl w :=
  (stepEquiv n).symm_apply_apply (Sum.inl w)

/-- `(NormalWord.stepEquiv n).symm` sends `NormalWord.empty` to `Sum.inl NormalWord.empty`. -/
@[simp]
theorem stepEquiv_symm_empty :
    (stepEquiv n).symm empty = Sum.inl empty := by
  rw [← strandIncl_empty, stepEquiv_symm_strandIncl]

/-- `(NormalWord.stepEquiv n).symm` recovers `Sum.inr ⟨j, w, hw⟩` on `snocLast j w hw`. -/
@[simp]
theorem stepEquiv_symm_snocLast (j : Fin (n + 1)) (w : NormalWord (n + 1))
    (hw : (w.lowerBound : ℕ) ≤ j) :
    (stepEquiv n).symm (snocLast j w hw) = Sum.inr ⟨j, w, hw⟩ :=
  (stepEquiv n).symm_apply_apply (Sum.inr ⟨j, w, hw⟩)

/-- Every normal word on at most one strand is `NormalWord.empty`. -/
theorem eq_empty_of_le_one {n : ℕ} (h : n ≤ 1) (w : NormalWord n) : w = empty := by
  ext1
  cases hruns : w.runs with
  | nil => rfl
  | cons r _ => exact absurd r.1.isLt (by omega)

/-- On at most one strand there are no generators, so the empty word is the unique normal word. -/
@[expose, instance_reducible]
def uniqueOfLeOne (h : n ≤ 1) : Unique (NormalWord n) where
  default := empty
  uniq := eq_empty_of_le_one h

/-- On zero strands, `NormalWord.empty` is the unique normal word. -/
instance : Unique (NormalWord 0) := uniqueOfLeOne (Nat.zero_le 1)

/-- On one strand, `NormalWord.empty` is the unique normal word. -/
instance : Unique (NormalWord 1) := uniqueOfLeOne le_rfl

instance : Fintype (NormalWord n) := by
  induction n with
  | zero => exact Fintype.ofSubsingleton empty
  | succ m ih =>
    cases m with
    | zero =>
      letI := uniqueOfLeOne (n := 0 + 1) le_rfl
      exact Fintype.ofSubsingleton empty
    | succ k =>
      letI : Fintype (NormalWord (k + 1)) := ih
      exact Fintype.ofEquiv _ (stepEquiv k)

/-- Cumulative count of normal words on `m + 1` strands with `lowerBound ≤ b`. -/
private def countLe (m b : ℕ) : ℕ :=
  #{w : NormalWord (m + 1) | (w.lowerBound : ℕ) ≤ b}

private theorem countLe_zero_zero : countLe 0 0 = 1 := by
  simp [countLe, Finset.univ_unique]

private theorem countLe_succ (m b : ℕ) :
    countLe (m + 1) b =
      countLe m b +
        ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) ↦ (j : ℕ) + 1 ≤ b), countLe m j := by
  unfold countLe
  simp_rw [← Fintype.card_subtype]
  have hcongr := Fintype.card_congr <|
    Equiv.subtypeEquiv (stepEquiv m).symm
      (p := fun u ↦ (u.lowerBound : ℕ) ≤ b)
      (q := fun s ↦ ((stepEquiv m s).lowerBound : ℕ) ≤ b) fun _ ↦ by simp
  rw [hcongr]
  let eSum := (Equiv.subtypeSum (p := fun s ↦ ((stepEquiv m s).lowerBound : ℕ) ≤ b)).trans
    (Equiv.sumCongr
      (Equiv.subtypeEquivRight (q := fun w : NormalWord (m + 1) ↦ (w.lowerBound : ℕ) ≤ b)
        fun w ↦ by simp)
      ((Equiv.subtypeEquivRight fun s ↦ by simp).trans
        (Equiv.subtypeSigmaEquiv _ (fun j : Fin (m + 1) ↦ (j : ℕ) + 1 ≤ b))))
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
    · rw [countLe_eq_halfCount m (c + 1) (by omega)]
      have hlhs : halfCount (m + 1 + 1 + c) (m + 1 + 1 - c) +
          halfCount (m + 1 + (c + 1)) (m + 1 - (c + 1)) =
          halfCount (m + 2 + c) ((m - c) + 2) + halfCount (m + 2 + c) (m - c) := by
        congr 1 <;> congr 1 <;> omega
      have hrhs : halfCount (m + 1 + 1 + (c + 1)) (m + 1 + 1 - (c + 1)) =
          halfCount ((m + 2 + c) + 1) ((m - c) + 1) := by
        congr 1; omega
      rw [hlhs, hrhs, halfCount_succ_succ, add_comm]
    · have hcm : c = m := by omega
      subst hcm
      rw [countLe_of_ge c (Nat.le_succ c), ← countLe_of_ge c le_rfl,
        countLe_eq_halfCount c c le_rfl]
      have hzero : halfCount (c + 1 + c) (c + 1 - c) = halfCount (2 * c + 2) 0 := by
        have h₁ : 2 * c + 2 = (c + 1 + c) + 1 := by omega
        have h₂ : c + 1 - c = 1 := by omega
        rw [h₁, h₂, halfCount_succ_zero]
      have hlhs : halfCount (c + 1 + 1 + c) (c + 1 + 1 - c) = halfCount (2 * c + 2) 2 := by
        congr 1 <;> omega
      have hrhs : halfCount (c + 1 + 1 + (c + 1)) (c + 1 + 1 - (c + 1)) =
          halfCount ((2 * c + 2) + 1) 1 := by
        congr 1 <;> omega
      rw [hlhs, hzero, hrhs, add_comm]
      exact (halfCount_succ_succ (2 * c + 2) 0).symm

/-- **Catalan count of Jones normal words.** There are `catalan n` words in Jones normal form on
`n` strands. -/
@[simp]
theorem card_eq_catalan (n : ℕ) : Fintype.card (NormalWord n) = catalan n := by
  cases n with
  | zero =>
    rw [catalan_zero, Fintype.card_unique]
  | succ m =>
    rw [← countLe_of_ge m le_rfl, countLe_eq_halfCount m m le_rfl]
    have h₁ : halfCount (m + 1 + m) (m + 1 - m) = halfCount (2 * m + 1) 1 := by congr 1 <;> omega
    have h₂ : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [h₁, ← halfCount_succ_zero, h₂, halfCount_two_mul_zero]

end NormalWord

/-! ### Run decomposition, reduction, and the Catalan rank bound -/

section Reduction

/-- Re-parsing the flat generator list of a `NormalWord` recovers its exact list of runs. -/
@[simp]
theorem NormalWord.parseDescendingRuns_toList {n : ℕ} (w : NormalWord n) :
    w.toList.parseDescendingRuns = w.runs := by
  refine List.parseDescendingRuns_eq_iff.mpr ⟨w.lower_le_upper, ?_, w.toList_def.symm⟩
  have hchain : (w.runs.map Prod.fst).IsChain (· < ·) :=
    List.isChain_iff_pairwise.mpr w.pairwise_upper
  rw [List.isChain_map] at hchain
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain ⊢
  intro r₁ r₂ l₁ l₂ hruns
  have hr₁ : r₁.2.val ≤ r₁.1.val :=
    Fin.le_def.mp (w.lower_le_upper r₁ (by rw [hruns]; simp))
  have hlt : r₁.1.val < r₂.1.val := Fin.lt_def.mp (hchain hruns)
  omega

/-- **Distinct normal words spell distinct generator words.** -/
@[grind inj]
theorem NormalWord.toList_injective {n : ℕ} :
    Function.Injective (NormalWord.toList (n := n)) := by
  intro w₁ w₂ h
  ext1
  rw [← w₁.parseDescendingRuns_toList, ← w₂.parseDescendingRuns_toList, h]

/-- Two normal words spell the same generator list if and only if they are equal. -/
@[simp]
theorem NormalWord.toList_inj {n : ℕ} {w₁ w₂ : NormalWord n} :
    w₁.toList = w₂.toList ↔ w₁ = w₂ :=
  NormalWord.toList_injective.eq_iff

/-- The augmentation of a normal word's evaluation is `1` on `NormalWord.empty` and `0` on every
nonempty normal word. -/
@[simp]
theorem NormalWord.aug_eval {R : Type*} [CommSemiring R] {n : ℕ} (δ : R) (w : NormalWord n) :
    aug (w.eval δ) = if w = NormalWord.empty then 1 else 0 := by
  simp [NormalWord.eval_def]

section AlgebraicSteps

variable {R : Type*} [CommSemiring R] {δ : R} {n : ℕ}

/-- Distant commutation step: when `(i₂ : ℕ) + 2 ≤ j₁ ≤ i₁`, the leading generator `i₂` of the
second run commutes left past the first run, preserving word length and placing `i₂ < i₁` first. -/
private theorem reduce_distant {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (h₂ : j₂ ≤ i₂) (hdist : (i₂ : ℕ) + 2 ≤ j₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) = wordProd δ mid ∧
      ∀ post, List.Shortlex (· < ·) (mid ++ post)
        ((Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) ++ post) := by
  obtain ⟨t₁, ht₁⟩ := Fin.exists_cons_descendingRun h₁
  obtain ⟨t₂, ht₂⟩ := Fin.exists_cons_descendingRun h₂
  refine ⟨i₂ :: (Fin.descendingRun i₁ j₁ ++ t₂), ?_, fun post ↦ ?_⟩
  · have hcomm := wordProd_mul_e_comm (δ := δ) (x := i₂) (l := Fin.descendingRun i₁ j₁)
      fun a ha ↦ Or.inr (hdist.trans (Fin.le_def.mp (Fin.mem_descendingRun.mp ha).1))
    simp [ht₂, ← mul_assoc, hcomm]
  · have hlt : i₂ < i₁ := by
      have _ : j₁.val ≤ i₁.val := Fin.le_def.mp h₁
      rw [Fin.lt_def]; omega
    rw [ht₁, List.cons_append, List.cons_append, List.cons_append]
    exact List.Shortlex.of_lex
      (by simp only [ht₂, List.length_cons, List.length_append]; omega)
      (List.Lex.rel hlt)

/-- Core left zig-zag step: for `j₁ < x`, `Fin.descendingRun x j₁` times `e δ x` reduces in
length. -/
private theorem reduce_left_zigzag_core {x j₁ : Fin (n - 1)} (h : j₁ < x) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (Fin.descendingRun x j₁) * e δ x = wordProd δ mid ∧
      mid.length < (Fin.descendingRun x j₁).length + 1 := by
  have _ : j₁.val < x.val := Fin.lt_def.mp h
  let x₁ : Fin (n - 1) := ⟨x.val - 1, by have := x.isLt; omega⟩
  have hx₁_eq : (⟨x.val - 1, by have := x.isLt; omega⟩ : Fin (n - 1)) = x₁ := rfl
  have hx₁ : (x₁ : ℕ) + 1 = x := by dsimp only [x₁]; omega
  have hj₁x₁ : j₁ ≤ x₁ := by rw [Fin.le_def]; dsimp only [x₁]; omega
  rcases eq_or_lt_of_le hj₁x₁ with hEq | hlt
  · refine ⟨[x], ?_, by simp only [List.length_singleton, Fin.length_descendingRun]; omega⟩
    rw [Fin.descendingRun_cons h, hx₁_eq, hEq]
    simp [e_mul_e_mul_e (Or.inr hx₁)]
  · let x₂ : Fin (n - 1) := ⟨x.val - 2, by have := x.isLt; omega⟩
    have hx₂ : (⟨x₁.val - 1, by have := x₁.isLt; omega⟩ : Fin (n - 1)) = x₂ := by
      ext; dsimp only [x₁, x₂]; omega
    refine ⟨x :: Fin.descendingRun x₂ j₁, ?_, ?_⟩
    · have hcomm := wordProd_mul_e_comm (δ := δ) (x := x) (l := Fin.descendingRun x₂ j₁)
        fun a ha ↦ Or.inl <| by
          have ha_le : a.val ≤ x₂.val := Fin.le_def.mp (Fin.mem_descendingRun.mp ha).2
          dsimp only [x₂] at ha_le; omega
      calc
        wordProd δ (Fin.descendingRun x j₁) * e δ x
            = e δ x * (e δ x₁ * (wordProd δ (Fin.descendingRun x₂ j₁) * e δ x)) := by
              rw [Fin.descendingRun_cons h, hx₁_eq, Fin.descendingRun_cons hlt, hx₂]
              simp only [wordProd_cons, mul_assoc]
        _ = (e δ x * e δ x₁ * e δ x) * wordProd δ (Fin.descendingRun x₂ j₁) := by
              rw [hcomm]; simp only [mul_assoc]
        _ = wordProd δ (x :: Fin.descendingRun x₂ j₁) := by
              rw [e_mul_e_mul_e (Or.inr hx₁), wordProd_cons]
    · simp only [List.length_cons, Fin.length_descendingRun]
      have hltv : j₁.val < x₁.val := Fin.lt_def.mp hlt
      dsimp only [x₁, x₂] at hltv ⊢; omega

/-- Core right zig-zag step: for `j₁ < i₂`, `e δ j₁` times `Fin.descendingRun i₂ j₁` reduces in
length. -/
private theorem reduce_right_zigzag_core {i₂ j₁ : Fin (n - 1)} (h : j₁ < i₂) :
    ∃ mid : List (Fin (n - 1)),
      e δ j₁ * wordProd δ (Fin.descendingRun i₂ j₁) = wordProd δ mid ∧
      mid.length < (Fin.descendingRun i₂ j₁).length + 1 := by
  have _ : j₁.val < i₂.val := Fin.lt_def.mp h
  let j' : Fin (n - 1) := ⟨j₁.val + 1, by have := i₂.isLt; omega⟩
  have hj'_eq : (⟨j₁.val + 1, by have := i₂.isLt; omega⟩ : Fin (n - 1)) = j' := rfl
  have hj' : (j₁ : ℕ) + 1 = j' := by simp [j']
  have hj'i₂ : j' ≤ i₂ := by rw [Fin.le_def]; exact Fin.lt_def.mp h
  rcases eq_or_lt_of_le hj'i₂ with hEq | hlt
  · refine ⟨[j₁], ?_, by simp only [List.length_singleton, Fin.length_descendingRun]; omega⟩
    rw [Fin.descendingRun_concat h, hj'_eq, ← hEq]
    simp [← mul_assoc, e_mul_e_mul_e (Or.inl hj')]
  · let j'' : Fin (n - 1) := ⟨j₁.val + 2, by have := i₂.isLt; omega⟩
    have hj'' : (⟨j'.val + 1, by have := i₂.isLt; omega⟩ : Fin (n - 1)) = j'' := by
      ext; simp [j', j'']
    refine ⟨Fin.descendingRun i₂ j'' ++ [j₁], ?_, ?_⟩
    · have hcomm := (wordProd_mul_e_comm (δ := δ) (x := j₁) (l := Fin.descendingRun i₂ j'')
        fun a ha ↦ Or.inr <| by
          have ha_ge : j''.val ≤ a.val := Fin.le_def.mp (Fin.mem_descendingRun.mp ha).1
          dsimp only [j''] at ha_ge; omega).symm
      calc
        e δ j₁ * wordProd δ (Fin.descendingRun i₂ j₁)
            = (e δ j₁ * wordProd δ (Fin.descendingRun i₂ j'')) * e δ j' * e δ j₁ := by
              rw [Fin.descendingRun_concat h, hj'_eq, Fin.descendingRun_concat hlt, hj'']
              simp only [wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_assoc]
        _ = wordProd δ (Fin.descendingRun i₂ j'') * (e δ j₁ * e δ j' * e δ j₁) := by
              rw [hcomm]; simp only [mul_assoc]
        _ = wordProd δ (Fin.descendingRun i₂ j'' ++ [j₁]) := by
              rw [e_mul_e_mul_e (Or.inl hj')]
              simp only [wordProd_append, wordProd_cons, wordProd_nil, mul_one]
    · simp only [List.length_append, List.length_singleton, Fin.length_descendingRun]
      have hltv : j'.val < i₂.val := Fin.lt_def.mp hlt
      dsimp only [j', j''] at hltv ⊢; omega

/-- Left zig-zag reduction on two adjacent runs when `j₁ < i₂ ≤ i₁`. -/
private theorem reduce_left_zigzag {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₂ : j₂ ≤ i₂) (hj₁ : j₁ < i₂) (hi₂ : i₂ ≤ i₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) = wordProd δ mid ∧
      mid.length < (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂).length := by
  obtain ⟨tail₂, htail₂⟩ := Fin.exists_cons_descendingRun h₂
  obtain ⟨pre₁, hpre₁⟩ : ∃ pre₁, Fin.descendingRun i₁ j₁ = pre₁ ++ Fin.descendingRun i₂ j₁ := by
    rcases eq_or_lt_of_le hi₂ with rfl | hlt
    · exact ⟨[], rfl⟩
    · let k : Fin (n - 1) := ⟨i₂.val + 1, by have := i₁.isLt; omega⟩
      have hki₁ : k ≤ i₁ := by rw [Fin.le_def]; exact Fin.lt_def.mp hlt
      have hjk : j₁ < k := by
        have _ := Fin.lt_def.mp hj₁
        rw [Fin.lt_def]; dsimp only [k]; omega
      have hkpred : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin (n - 1)) = i₂ := by
        ext; dsimp only [k]; omega
      exact ⟨Fin.descendingRun i₁ k, hkpred ▸ Fin.descendingRun_split hki₁ hjk⟩
  obtain ⟨mid₀, hmid₀, hlen₀⟩ := reduce_left_zigzag_core (δ := δ) hj₁
  refine ⟨pre₁ ++ mid₀ ++ tail₂, ?_, ?_⟩
  · simp [hpre₁, htail₂, ← hmid₀, mul_assoc]
  · simp only [hpre₁, htail₂, List.length_append, List.length_cons]
    omega

/-- Right zig-zag reduction on two adjacent runs when `j₂ ≤ j₁ < i₂`. -/
private theorem reduce_right_zigzag {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (hj₁ : j₁ < i₂) (hj₂ : j₂ ≤ j₁) :
    ∃ mid : List (Fin (n - 1)),
      wordProd δ (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) = wordProd δ mid ∧
      mid.length < (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂).length := by
  obtain ⟨init₁, hinit₁⟩ := Fin.exists_concat_descendingRun h₁
  obtain ⟨post₂, hpost₂⟩ : ∃ post₂, Fin.descendingRun i₂ j₂ = Fin.descendingRun i₂ j₁ ++ post₂ :=
    (eq_or_lt_of_le hj₂).elim (fun h ↦ ⟨[], by simp [h]⟩)
      fun h ↦ ⟨_, Fin.descendingRun_split hj₁.le h⟩
  obtain ⟨mid₀, hmid₀, hlen₀⟩ := reduce_right_zigzag_core (δ := δ) hj₁
  refine ⟨init₁ ++ mid₀ ++ post₂, ?_, ?_⟩
  · simp [hinit₁, hpost₂, ← hmid₀, mul_assoc]
  · simp only [hinit₁, hpost₂, List.length_append, List.length_singleton]
    omega

/-- Any adjacent pair of runs `(i₁, j₁), (i₂, j₂)` from `List.parseDescendingRuns` violating
`i₁ < i₂ ∧ j₁ < j₂` reduces to a `δ`-power multiple of a word strictly smaller in `List.Shortlex`
before any suffix `post`. -/
private theorem reduce_bad_pair {i₁ j₁ i₂ j₂ : Fin (n - 1)}
    (h₁ : j₁ ≤ i₁) (h₂ : j₂ ≤ i₂) (hsep : (i₂ : ℕ) + 1 ≠ j₁) (hbad : ¬ (i₁ < i₂ ∧ j₁ < j₂)) :
    ∃ (k : ℕ) (mid : List (Fin (n - 1))),
      wordProd δ (Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) = δ ^ k • wordProd δ mid ∧
      ∀ post, List.Shortlex (· < ·) (mid ++ post)
        ((Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) ++ post) := by
  by_cases hdist : (i₂ : ℕ) + 2 ≤ j₁
  · obtain ⟨mid, hmid, hshort⟩ := reduce_distant (δ := δ) h₁ h₂ hdist
    exact ⟨0, mid, by simpa using hmid, hshort⟩
  · by_cases heq : i₂ = j₁
    · subst heq
      obtain ⟨init₁, hinit₁⟩ := Fin.exists_concat_descendingRun h₁
      obtain ⟨tail₂, htail₂⟩ := Fin.exists_cons_descendingRun h₂
      refine ⟨1, init₁ ++ i₂ :: tail₂, ?_, fun post ↦ List.Shortlex.of_length_lt ?_⟩
      · have hsq : e δ i₂ * (e δ i₂ * wordProd δ tail₂) = δ • (e δ i₂ * wordProd δ tail₂) := by
          rw [← mul_assoc, e_mul_self, smul_mul_assoc]
        simp [hinit₁, htail₂, hsq]
      · simp [hinit₁, htail₂]
    · have hj₁_lt_i₂ : j₁ < i₂ := by
        have _ : i₂.val ≠ j₁.val := Fin.val_ne_of_ne heq
        rw [Fin.lt_def]; omega
      by_cases hi₂_le_i₁ : i₂ ≤ i₁
      · obtain ⟨mid, hmid, hlen⟩ := reduce_left_zigzag (δ := δ) h₂ hj₁_lt_i₂ hi₂_le_i₁
        exact ⟨0, mid, by simpa using hmid, fun post ↦
          List.Shortlex.of_length_lt (by simp only [List.length_append] at hlen ⊢; omega)⟩
      · rw [not_and_or, not_lt, not_lt] at hbad
        obtain ⟨mid, hmid, hlen⟩ := reduce_right_zigzag (δ := δ) h₁ hj₁_lt_i₂
          (hbad.resolve_left hi₂_le_i₁)
        exact ⟨0, mid, by simpa using hmid, fun post ↦
          List.Shortlex.of_length_lt (by simp only [List.length_append] at hlen ⊢; omega)⟩

/-- A word `l` whose runs are not strictly increasing in both endpoints reduces globally in
`List.Shortlex` up to a power of `δ`. -/
private theorem reduce_not_isChain (δ : R) {l : List (Fin (n - 1))}
    (hgood : ¬ l.parseDescendingRuns.IsChain fun r₁ r₂ ↦ r₁.1 < r₂.1 ∧ r₁.2 < r₂.2) :
    ∃ (k : ℕ) (l' : List (Fin (n - 1))),
      wordProd δ l = δ ^ k • wordProd δ l' ∧ List.Shortlex (· < ·) l' l := by
  obtain ⟨⟨i₁, j₁⟩, ⟨i₂, j₂⟩, rsPre, rsPost, hrs_eq, hbad⟩ := by
    simpa only [List.isChain_iff_forall_rel_of_append_cons_cons, Classical.not_forall, not_imp]
      using hgood
  have h₁ : j₁ ≤ i₁ :=
    List.snd_le_fst_of_mem_parseDescendingRuns (r := (i₁, j₁)) (by rw [hrs_eq]; simp)
  have h₂ : j₂ ≤ i₂ :=
    List.snd_le_fst_of_mem_parseDescendingRuns (r := (i₂, j₂)) (by rw [hrs_eq]; simp)
  have hsep : (i₂ : ℕ) + 1 ≠ j₁ :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp (List.isChain_parseDescendingRuns l) hrs_eq
  let pre := rsPre.flatMap fun r ↦ Fin.descendingRun r.1 r.2
  let post := rsPost.flatMap fun r ↦ Fin.descendingRun r.1 r.2
  have hl_eq : l = pre ++ ((Fin.descendingRun i₁ j₁ ++ Fin.descendingRun i₂ j₂) ++ post) := by
    have hf := List.flatMap_parseDescendingRuns l
    rw [hrs_eq, List.flatMap_append, List.flatMap_cons, List.flatMap_cons] at hf
    simpa [pre, post, List.append_assoc] using hf.symm
  obtain ⟨k, mid, hmid_eq, hshort⟩ := reduce_bad_pair (δ := δ) h₁ h₂ hsep hbad
  refine ⟨k, pre ++ (mid ++ post), ?_, ?_⟩
  · rw [hl_eq, wordProd_append, wordProd_append, hmid_eq]
    simp
  · rw [hl_eq]
    exact (hshort post).append_left pre

/-- **Jones normal form monomial reduction.** Over every commutative semiring `R` and for every loop
parameter `δ : R`, every generator word `wordProd δ l` equals `δ ^ k • w.eval δ` for some loop count
`k : ℕ` and some normal word `w : NormalWord n`. -/
theorem exists_wordProd_eq_pow_smul_eval (δ : R) (l : List (Fin (n - 1))) :
    ∃ (k : ℕ) (w : NormalWord n), wordProd δ l = δ ^ k • w.eval δ := by
  refine (List.Shortlex.wf (r := ((· < ·) : Fin (n - 1) → Fin (n - 1) → Prop))
    wellFounded_lt).induction
    (C := fun l ↦ ∃ (k : ℕ) (w : NormalWord n), wordProd δ l = δ ^ k • w.eval δ) l fun l ih ↦ ?_
  by_cases hgood : l.parseDescendingRuns.IsChain fun r₁ r₂ ↦ r₁.1 < r₂.1 ∧ r₁.2 < r₂.2
  · have hup : (l.parseDescendingRuns.map Prod.fst).Pairwise (· < ·) :=
      List.isChain_iff_pairwise.mp (List.isChain_map _ |>.mpr (hgood.imp fun _ _ h ↦ h.1))
    have hlow : (l.parseDescendingRuns.map Prod.snd).Pairwise (· < ·) :=
      List.isChain_iff_pairwise.mp (List.isChain_map _ |>.mpr (hgood.imp fun _ _ h ↦ h.2))
    let w : NormalWord n :=
      ⟨l.parseDescendingRuns, fun _ ↦ List.snd_le_fst_of_mem_parseDescendingRuns, hup, hlow⟩
    have hw : w.eval δ = wordProd δ l := by
      simp [NormalWord.eval, NormalWord.toList, w]
    exact ⟨0, w, by simp [hw]⟩
  · obtain ⟨k₁, l', hprod, hlt⟩ := reduce_not_isChain δ hgood
    obtain ⟨k₂, w, ihw⟩ := ih l' hlt
    exact ⟨k₁ + k₂, w, by rw [hprod, ihw, smul_smul, ← pow_add]⟩

/-- Every generator word lies in the `R`-span of the evaluations of `NormalWord n`. -/
theorem wordProd_mem_span_range_eval (δ : R) :
    ∀ l : List (Fin (n - 1)),
      wordProd δ l ∈ Submodule.span R (Set.range (NormalWord.eval (R := R) (n := n) δ)) := by
  intro l
  obtain ⟨k, w, h⟩ := exists_wordProd_eq_pow_smul_eval δ l
  exact h ▸ Submodule.smul_mem _ (δ ^ k) (Submodule.subset_span ⟨w, rfl⟩)

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

/-- **Catalan rank bound** (cardinal form): over every commutative semiring `R`, the `R`-rank of
`TemperleyLieb R δ n` is at most `catalan n`. -/
theorem rank_le_catalan (δ : R) (n : ℕ) :
    Module.rank R (TemperleyLieb R δ n) ≤ catalan n := by
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [rank_subsingleton]
    exact_mod_cast (NormalWord.card_eq_catalan n ▸ Fintype.card_pos : 1 ≤ catalan n)
  · rw [← rank_top, ← span_range_eval_eq_top (R := R) δ n]
    have hcard : Cardinal.mk (Set.range (NormalWord.eval (R := R) (n := n) δ)) ≤ catalan n := by
      simpa [NormalWord.card_eq_catalan] using
        Cardinal.mk_range_le_lift (f := NormalWord.eval (R := R) (n := n) δ)
    exact (rank_span_le _).trans hcard

/-- **Catalan dimension bound.** Over every commutative semiring `R`, the `finrank` of
`TemperleyLieb R δ n` is at most `catalan n`. -/
theorem finrank_le_catalan (δ : R) (n : ℕ) :
    Module.finrank R (TemperleyLieb R δ n) ≤ catalan n :=
  Module.finrank_le_of_rank_le (rank_le_catalan δ n)

end AlgebraicSteps

end Reduction

/-! ### Exact normal-word bases on up to three strands -/

section SmallBases

variable {R : Type*} [CommSemiring R]

/-- On at most one strand, `NormalWord n` forms an `R`-basis of `TemperleyLieb R δ n`. -/
private noncomputable def basisOfLeOne (δ : R) {n : ℕ} (hn : n ≤ 1) :
    Module.Basis (NormalWord n) R (TemperleyLieb R δ n) :=
  letI := NormalWord.uniqueOfLeOne hn
  (Module.Basis.singleton (NormalWord n) R).map (algEquivOfLeOne δ hn).symm.toLinearEquiv

private theorem coe_basisOfLeOne (δ : R) {n : ℕ} (hn : n ≤ 1) :
    ⇑(basisOfLeOne (R := R) δ hn) = NormalWord.eval δ := by
  let _ := NormalWord.uniqueOfLeOne hn
  ext w
  rw [NormalWord.eq_empty_of_le_one hn w]
  simp [basisOfLeOne]

/-- First-column coordinate map of a matrix representation `rep` indexed by
`idx : NormalWord n → Fin k`. -/
private def firstColCoord {δ : R} {n k : ℕ} [NeZero k]
    (rep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin k) (Fin k) R)
    (idx : NormalWord n → Fin k) :
    TemperleyLieb R δ n →ₗ[R] (NormalWord n → R) where
  toFun x w := rep x (idx w) 0
  map_add' x y := by ext w; simp
  map_smul' r x := by ext w; simp

private theorem firstColCoord_eval {δ : R} {n k : ℕ} [NeZero k] (hk : k = catalan n)
    (rep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin k) (Fin k) R)
    (word : Fin k → NormalWord n) (idx : NormalWord n → Fin k)
    (hidx : Function.LeftInverse idx word)
    (hcol : ∀ i j, rep ((word i).eval δ) j 0 = if j = i then 1 else 0)
    (w : NormalWord n) :
    firstColCoord rep idx (w.eval δ) = Pi.single w 1 := by
  have hsurj : Function.Surjective word := by
    refine ((Fintype.bijective_iff_injective_and_card word).mpr ⟨hidx.injective, ?_⟩).2
    rw [Fintype.card_fin, NormalWord.card_eq_catalan, hk]
  ext u
  dsimp only [firstColCoord, LinearMap.coe_mk, AddHom.coe_mk]
  obtain ⟨i, rfl⟩ := hsurj w
  obtain ⟨j, rfl⟩ := hsurj u
  rw [hidx j, hcol i j, Pi.single_apply]
  simp only [hidx.injective.eq_iff]

/-- Construct the `NormalWord n` basis of `TemperleyLieb R δ n` from a `k × k` matrix
representation whose first column separates the `k = catalan n` normal words. -/
private noncomputable def basisOfFirstCol {δ : R} {n k : ℕ} [NeZero k] (hk : k = catalan n)
    (rep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin k) (Fin k) R)
    (word : Fin k → NormalWord n) (idx : NormalWord n → Fin k)
    (hidx : Function.LeftInverse idx word)
    (hcol : ∀ i j, rep ((word i).eval δ) j 0 = if j = i then 1 else 0) :
    Module.Basis (NormalWord n) R (TemperleyLieb R δ n) :=
  Module.Basis.mk
    (LinearIndependent.of_comp (firstColCoord rep idx) <| by
      simpa only [Function.comp_def, firstColCoord_eval hk rep word idx hidx hcol] using
        Pi.linearIndependent_single_one (NormalWord n) R)
    (span_range_eval_eq_top δ n).ge

private theorem coe_basisOfFirstCol {δ : R} {n k : ℕ} [NeZero k] (hk : k = catalan n)
    (rep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin k) (Fin k) R)
    (word : Fin k → NormalWord n) (idx : NormalWord n → Fin k)
    (hidx : Function.LeftInverse idx word)
    (hcol : ∀ i j, rep ((word i).eval δ) j 0 = if j = i then 1 else 0) :
    ⇑(basisOfFirstCol hk rep word idx hidx hcol) = NormalWord.eval δ :=
  Module.Basis.coe_mk _ _

private theorem injective_of_firstCol {δ : R} {n k : ℕ} [NeZero k] (hk : k = catalan n)
    (rep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin k) (Fin k) R)
    (word : Fin k → NormalWord n) (idx : NormalWord n → Fin k)
    (hidx : Function.LeftInverse idx word)
    (hcol : ∀ i j, rep ((word i).eval δ) j 0 = if j = i then 1 else 0) :
    Function.Injective rep := by
  let b := basisOfFirstCol hk rep word idx hidx hcol
  have hb : ⇑b = NormalWord.eval δ := coe_basisOfFirstCol hk rep word idx hidx hcol
  have hcoord : ∀ x w, firstColCoord rep idx x w = b.repr x w := fun x w ↦ by
    conv_lhs => rw [← b.sum_repr x]
    simp [map_sum, map_smul, hb, firstColCoord_eval hk rep word idx hidx hcol, Pi.single_apply]
  intro x y hxy
  apply b.repr.injective
  ext w
  rw [← hcoord, ← hcoord]
  exact congrArg (fun M ↦ M (idx w) 0) hxy

/-- Enumeration `(1, e 0)` of the two normal words on two strands. -/
private def twoStrandWord : Fin 2 → NormalWord 2
  | 0 => NormalWord.empty
  | 1 => NormalWord.single 0

/-- Computable index of a normal word on two strands: `0` for `1`, `1` for `e 0`. -/
private def twoStrandIdx (w : NormalWord 2) : Fin 2 :=
  if w.runs.isEmpty then 0 else 1

private theorem twoStrandIdx_twoStrandWord (k : Fin 2) : twoStrandIdx (twoStrandWord k) = k := by
  fin_cases k <;> rfl

private theorem twoStrandRep_eval_col_zero (δ : R) (i j : Fin 2) :
    twoStrandRep δ ((twoStrandWord i).eval δ) j 0 = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [twoStrandWord]

/-- On two strands, the normal words `(1, e δ 0)` form an `R`-basis of `TemperleyLieb R δ 2` over
every commutative semiring `R`. -/
noncomputable def basisTwo (δ : R) : Module.Basis (NormalWord 2) R (TemperleyLieb R δ 2) :=
  basisOfFirstCol catalan_two.symm (twoStrandRep δ) twoStrandWord twoStrandIdx
    twoStrandIdx_twoStrandWord (twoStrandRep_eval_col_zero δ)

/-- `basisTwo` evaluates each normal word via `NormalWord.eval`. -/
@[simp]
theorem coe_basisTwo (δ : R) : ⇑(basisTwo (R := R) δ) = NormalWord.eval δ :=
  coe_basisOfFirstCol catalan_two.symm (twoStrandRep δ) twoStrandWord twoStrandIdx
    twoStrandIdx_twoStrandWord (twoStrandRep_eval_col_zero δ)

/-- The two-dimensional representation `twoStrandRep` is faithful over every commutative semiring
`R` and at every loop value `δ`. -/
theorem twoStrandRep_injective (δ : R) :
    Function.Injective (twoStrandRep (R := R) δ) :=
  injective_of_firstCol catalan_two.symm (twoStrandRep δ) twoStrandWord twoStrandIdx
    twoStrandIdx_twoStrandWord (twoStrandRep_eval_col_zero δ)

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

private theorem threeStrandRep_eval_col_zero (δ : R) (i j : Fin 5) :
    threeStrandRep δ ((threeStrandWord i).eval δ) j 0 = if j = i then 1 else 0 := by
  have hdr : Fin.descendingRun (1 : Fin (3 - 1)) 0 = [1, 0] := by
    rw [Fin.descendingRun_cons (by decide)]; simp
  fin_cases i <;> fin_cases j <;>
    simp [threeStrandWord, NormalWord.eval, NormalWord.toList, wordProd, hdr]

/-- On three strands, the five normal words `(1, e 0, e 1, e 0 * e 1, e 1 * e 0)` form an `R`-basis
of `TemperleyLieb R δ 3` over every commutative semiring `R` and at every loop value `δ`. -/
noncomputable def basisThree (δ : R) : Module.Basis (NormalWord 3) R (TemperleyLieb R δ 3) :=
  basisOfFirstCol catalan_three.symm (threeStrandRep δ) threeStrandWord threeStrandIdx
    threeStrandIdx_threeStrandWord (threeStrandRep_eval_col_zero δ)

/-- `basisThree` evaluates each normal word via `NormalWord.eval`. -/
@[simp]
theorem coe_basisThree (δ : R) : ⇑(basisThree (R := R) δ) = NormalWord.eval δ :=
  coe_basisOfFirstCol catalan_three.symm (threeStrandRep δ) threeStrandWord threeStrandIdx
    threeStrandIdx_threeStrandWord (threeStrandRep_eval_col_zero δ)

/-- The five-dimensional left-regular representation `threeStrandRep` is faithful over every
commutative semiring `R` and at every loop value `δ`. -/
theorem threeStrandRep_injective (δ : R) :
    Function.Injective (threeStrandRep (R := R) δ) :=
  injective_of_firstCol catalan_three.symm (threeStrandRep δ) threeStrandWord threeStrandIdx
    threeStrandIdx_threeStrandWord (threeStrandRep_eval_col_zero δ)

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
  · exact coe_basisOfLeOne δ (Nat.zero_le 1)
  · exact coe_basisOfLeOne δ le_rfl
  · exact coe_basisTwo δ
  · exact coe_basisThree δ
  · omega

/-- On at most three strands, `TemperleyLieb R δ n` is a free `R`-module for every commutative
semiring `R` and loop value `δ`. -/
theorem free_of_le_three (δ : R) {n : ℕ} (hn : n ≤ 3) : Module.Free R (TemperleyLieb R δ n) :=
  Module.Free.of_basis (basisOfLeThree δ hn)

/-- The zero-strand Temperley–Lieb algebra is a free `R`-module. -/
instance (δ : R) : Module.Free R (TemperleyLieb R δ 0) := free_of_le_three δ (by decide)

/-- The one-strand Temperley–Lieb algebra is a free `R`-module. -/
instance (δ : R) : Module.Free R (TemperleyLieb R δ 1) := free_of_le_three δ (by decide)

/-- The two-strand Temperley–Lieb algebra is a free `R`-module. -/
instance (δ : R) : Module.Free R (TemperleyLieb R δ 2) := free_of_le_three δ (by decide)

/-- The three-strand Temperley–Lieb algebra is a free `R`-module. -/
instance (δ : R) : Module.Free R (TemperleyLieb R δ 3) := free_of_le_three δ (by decide)

/-- On at most three strands, `TemperleyLieb R δ n` has `finrank` equal to `catalan n` over every
nontrivial commutative semiring `R`. -/
theorem finrank_eq_catalan_of_le_three [Nontrivial R] (δ : R) {n : ℕ} (hn : n ≤ 3) :
    Module.finrank R (TemperleyLieb R δ n) = catalan n := by
  rw [Module.finrank_eq_card_basis (basisOfLeThree (R := R) δ hn), NormalWord.card_eq_catalan]

/-- The zero-strand Temperley–Lieb algebra has dimension `1` over every commutative semiring `R` and
at every loop parameter `δ`. -/
@[simp]
theorem finrank_zero (δ : R) :
    Module.finrank R (TemperleyLieb R δ 0) = 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Module.finrank_subsingleton
  · rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_zero]

/-- The one-strand Temperley–Lieb algebra has dimension `1` over every commutative semiring `R` and
at every loop parameter `δ`. -/
@[simp]
theorem finrank_one (δ : R) :
    Module.finrank R (TemperleyLieb R δ 1) = 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Module.finrank_subsingleton
  · rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_one]

/-- The two-strand Temperley–Lieb algebra has dimension `2` over every nontrivial commutative
semiring `R` and at every loop parameter `δ`. -/
@[simp]
theorem finrank_two [Nontrivial R] (δ : R) :
    Module.finrank R (TemperleyLieb R δ 2) = 2 := by
  rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_two]

/-- The three-strand Temperley–Lieb algebra has dimension `5` over every nontrivial commutative
semiring `R` and at every loop parameter `δ`. -/
@[simp]
theorem finrank_three [Nontrivial R] (δ : R) :
    Module.finrank R (TemperleyLieb R δ 3) = 5 := by
  rw [finrank_eq_catalan_of_le_three δ (by decide), catalan_three]

/-- Every generator of `TemperleyLieb R δ n` for `n ≤ 3` is nonzero over any nontrivial
commutative semiring `R`. -/
theorem e_ne_zero_of_le_three [Nontrivial R] {δ : R} {n : ℕ} (hn : n ≤ 3) (i : Fin (n - 1)) :
    e δ i ≠ 0 := by
  simpa using (basisOfLeThree (R := R) δ hn).ne_zero (NormalWord.single i)

/-- Adding a straight strand is injective from `1` to `2` strands and from `2` to `3` strands, over
every commutative semiring `R` and at every loop value `δ`. -/
theorem strandIncl_injective_of_le_one (δ : R) {n : ℕ} (hn : n ≤ 1) :
    Function.Injective (strandIncl (R := R) (δ := δ) (n := n)) := by
  let b₁ := basisOfLeThree (R := R) δ (n := n + 1) (by omega)
  let b₂ := basisOfLeThree (R := R) δ (n := n + 2) (by omega)
  have heq : b₁.constr R (b₂ ∘ NormalWord.strandIncl) =
      (strandIncl (R := R) (δ := δ) (n := n)).toLinearMap :=
    b₁.constr_eq R fun u ↦ by simp [b₁, b₂]
  simpa only [heq, AlgHom.coe_toLinearMap] using
    b₁.injective_constr_of_linearIndependent (R₂ := R)
      (b₂.linearIndependent.comp _ NormalWord.strandIncl_injective)

end SmallBases

end TauCeti.TemperleyLieb
