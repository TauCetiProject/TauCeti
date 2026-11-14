/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import TauCeti.Algebra.TemperleyLieb.Basic
import Mathlib.Data.List.Intervals
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Supplies `CommSemiring.strongRankCondition_of_nontrivial` for `rank_span_le` and `finrank`.
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import TauCeti.Combinatorics.PlanarMatching.HalfDiagram

/-!
# Jones normal form and the Catalan rank bound for Temperley–Lieb algebras

Every element of the Temperley–Lieb algebra `TemperleyLieb R δ n` over a commutative semiring `R`
is an `R`-linear combination of **Jones reduced words**: products
`(e i₁ * e (i₁ - 1) * ⋯ * e j₁) * ⋯ * (e iᵣ * e (iᵣ - 1) * ⋯ * e jᵣ)`
of decreasing generator blocks whose starting indices `i₁ < ⋯ < iᵣ` and ending indices
`j₁ < ⋯ < jᵣ` are both strictly increasing, with `jₛ ≤ iₛ` in every block.

This file develops Jones reduced words directly from the three defining relations of
`TemperleyLieb R δ n` — without diagram bases, cell modules or Gram determinants — and establishes
that there are `catalan n` reduced words on `n` strands, that `TemperleyLieb R δ n` is finitely
generated as an `R`-module, and that its `R`-rank and `finrank` (as well as those of any `R`-linear
quotient) are at most `catalan n`.

Two immediate structural consequences accompany the upper bound:

* Over any field, `TemperleyLieb R δ n` and all of its quotients by `R`-submodules (in particular
  quotients by left, right, or two-sided ideals such as trace radicals) are finite-dimensional of
  dimension at most `catalan n`.
* Over any commutative semiring satisfying `OrzechProperty` (including every commutative ring and
  every field), any `R`-linear map out of `TemperleyLieb R δ n` whose image has `finrank` at least
  `catalan n` is automatically injective and promotes the reduced-word evaluations to a free
  `R`-basis of rank `catalan n`. On two strands, combining `linearIndependent_two` with
  reduced-word spanning furnishes the explicit free `R`-basis `basisTwo` of rank `2 = catalan 2`.

## Main definitions

* `TauCeti.TemperleyLieb.descBlockList`: the decreasing list of generator indices from `i` to `j`.
* `TauCeti.TemperleyLieb.descBlock`: the decreasing generator product `e δ i * ⋯ * e δ j`.
* `TauCeti.TemperleyLieb.JonesWord`: Jones reduced words on `n` strands.
* `TauCeti.TemperleyLieb.JonesWord.eval`: evaluation of a reduced word in `TemperleyLieb R δ n`.
* `TauCeti.TemperleyLieb.JonesWord.wordLength`: total number of generators in a reduced word.
* `TauCeti.TemperleyLieb.JonesWord.castSucc`: inclusion of reduced words along `strandIncl`.
* `TauCeti.TemperleyLieb.JonesWord.equivFinsetPair`: equivalence between `JonesWord n` and pairs of
  equal-sized subsets of `Fin (n - 1)` satisfying `jₛ ≤ iₛ` on sorted elements.
* `TauCeti.TemperleyLieb.basisJonesWordOfCatalanLeFinrankRange`: free `R`-basis of reduced words
  witnessed by a linear map whose image has `finrank` at least `catalan n`.
* `TauCeti.TemperleyLieb.basisTwo`: explicit free `R`-basis `![1, e δ 0]` on two strands.

## Main results

* `TauCeti.TemperleyLieb.exists_jonesWord_of_list`: every generator product reduces to
  `δ ^ m • w.eval δ` with `w.wordLength ≤ l.length`.
* `TauCeti.TemperleyLieb.span_range_jonesWord_eval`,
  `TauCeti.TemperleyLieb.span_range_comp_jonesWord_eval_of_surjective`: reduced words span
  `TemperleyLieb R δ n` and any surjective `R`-linear image of it.
* `TauCeti.TemperleyLieb.card_jonesWord`: `Fintype.card (JonesWord n) = catalan n`.
* `TauCeti.TemperleyLieb.rank_le_catalan`, `TauCeti.TemperleyLieb.finrank_le_catalan`,
  `TauCeti.TemperleyLieb.rank_le_catalan_of_surjective`,
  `TauCeti.TemperleyLieb.finrank_le_catalan_of_surjective`,
  `TauCeti.TemperleyLieb.rank_quotient_le_catalan`,
  `TauCeti.TemperleyLieb.finrank_quotient_le_catalan`: the `R`-rank and `finrank` of
  `TemperleyLieb R δ n`, of any surjective `R`-linear image, and of any submodule quotient are at
  most `catalan n`.
* `TauCeti.TemperleyLieb.injective_of_catalan_le_finrank_range`: a linear map out of
  `TemperleyLieb R δ n` whose range has `finrank` at least `catalan n` is injective.
* `TauCeti.TemperleyLieb.finrank_two`: exact `finrank` equal to `2` on two strands.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Exercises 4.1.2–4.1.3.
-/

public section

namespace TauCeti.TemperleyLieb

section DescBlock

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Decreasing list of generator indices in `Fin (n - 1)` over the half-open natural-number
interval `[lo, hi)`, given `hi ≤ n - 1`. -/
private def descIco (lo hi : ℕ) (hhi : hi ≤ n - 1) : List (Fin (n - 1)) :=
  (List.Ico lo hi).reverse.pmap Fin.mk fun _ hm ↦
    (List.Ico.mem.1 (List.mem_reverse.1 hm)).2.trans_le hhi

private theorem length_descIco (lo hi : ℕ) (hhi : hi ≤ n - 1) :
    (descIco lo hi hhi).length = hi - lo := by
  simp [descIco]

private theorem mem_descIco {lo hi : ℕ} {hhi : hi ≤ n - 1} {x : Fin (n - 1)} :
    x ∈ descIco lo hi hhi ↔ lo ≤ x.val ∧ x.val < hi := by
  simp only [descIco, List.mem_pmap, List.mem_reverse, List.Ico.mem]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨x.val, hx, Fin.ext rfl⟩

private theorem descIco_of_le {lo hi : ℕ} (hhi : hi ≤ n - 1) (h : hi ≤ lo) :
    descIco lo hi hhi = [] := by
  simp [descIco, List.Ico.eq_nil_of_le h]

private theorem descIco_singleton (i : Fin (n - 1)) :
    descIco i.val (i.val + 1) i.isLt = [i] := by
  simp [descIco]

private theorem descIco_split {lo mid hi : ℕ} (hhi : hi ≤ n - 1) (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    descIco lo hi hhi = descIco mid hi hhi ++ descIco lo mid (h₂.trans hhi) := by
  apply List.map_injective_iff.2 Fin.val_injective
  simp [descIco, List.map_pmap, List.Ico.append_consecutive h₁ h₂]

private theorem commute_prod_descIco_e (δ : R) {lo hi : ℕ} (hhi : hi ≤ n - 1) {k : Fin (n - 1)}
    (h : k.val + 2 ≤ lo ∨ hi + 1 ≤ k.val) :
    Commute (((descIco lo hi hhi).map (e δ)).prod) (e δ k) := by
  refine Commute.list_prod_left _ _ fun x hx ↦ ?_
  obtain ⟨i, hi', rfl⟩ := List.mem_map.1 hx
  rw [mem_descIco] at hi'
  exact commute_e (by omega)

/-- The decreasing list of generator indices `[i, i - 1, …, j]` in `Fin (n - 1)`, which is empty
when `i < j`. -/
def descBlockList (i j : Fin (n - 1)) : List (Fin (n - 1)) :=
  descIco j.val (i.val + 1) i.isLt

/-- A single-index decreasing block list consists of that generator index alone. -/
@[simp]
theorem descBlockList_self (i : Fin (n - 1)) : descBlockList i i = [i] :=
  descIco_singleton i

/-- When `i < j`, the decreasing block list from `i` down to `j` is empty. -/
theorem descBlockList_of_lt {i j : Fin (n - 1)} (h : i < j) : descBlockList i j = [] :=
  descIco_of_le i.isLt (by omega)

/-- Length of `descBlockList i j`. -/
@[simp]
theorem length_descBlockList (i j : Fin (n - 1)) :
    (descBlockList i j).length = i.val + 1 - j.val :=
  length_descIco j.val (i.val + 1) i.isLt

/-- `descBlockList i j` is empty if and only if `i < j`. -/
@[simp]
theorem descBlockList_eq_nil_iff {i j : Fin (n - 1)} : descBlockList i j = [] ↔ i < j := by
  rw [← List.length_eq_zero_iff, length_descBlockList]
  omega

/-- Membership in `descBlockList i j`: the indices `x` with `j ≤ x ≤ i`. -/
@[simp]
theorem mem_descBlockList {i j x : Fin (n - 1)} :
    x ∈ descBlockList i j ↔ j ≤ x ∧ x ≤ i := by
  rw [descBlockList, mem_descIco]
  exact ⟨fun h ↦ ⟨h.1, Nat.lt_succ_iff.1 h.2⟩, fun h ↦ ⟨h.1, Nat.lt_succ_iff.2 h.2⟩⟩

/-- Extending a nonempty decreasing block list on the left by the successor of `i`. -/
theorem descBlockList_cons {k i j : Fin (n - 1)} (hji : j ≤ i) (hik : i.val + 1 = k.val) :
    k :: descBlockList i j = descBlockList k j := by
  apply List.map_injective_iff.2 Fin.val_injective
  suffices (i.val + 1) :: (List.Ico j.val (i.val + 1)).reverse =
      (List.Ico j.val (i.val + 1 + 1)).reverse by
    simpa [descBlockList, descIco, List.map_pmap, ← hik]
  rw [← List.Ico.append_consecutive (Nat.le_succ_of_le hji) (Nat.le_succ (i.val + 1))]
  simp

/-- Extending a nonempty decreasing block list on the right by the predecessor of `j`. -/
theorem descBlockList_concat {i j k : Fin (n - 1)} (hji : j ≤ i) (hkj : k.val + 1 = j.val) :
    descBlockList i j ++ [k] = descBlockList i k := by
  rw [descBlockList, descBlockList, ← descIco_singleton k, ← hkj]
  exact (descIco_split i.isLt (by omega) (by omega)).symm

private theorem descBlockList_eq_descIco_append_singleton {i j : Fin (n - 1)} (hji : j ≤ i) :
    descBlockList i j = descIco (j.val + 1) (i.val + 1) i.isLt ++ [j] := by
  rw [descBlockList, ← descIco_singleton j]
  exact descIco_split i.isLt (Nat.le_succ j.val) (Nat.succ_le_succ hji)

/-- Mapping `descBlockList` along `Fin.castSucc` produces `descBlockList` at the next strand
level. -/
@[simp]
theorem map_castSucc_descBlockList {m : ℕ} (i j : Fin m) :
    (descBlockList (n := m + 1) i j).map Fin.castSucc =
      descBlockList (n := m + 2) i.castSucc j.castSucc := by
  simp only [descBlockList, descIco, List.map_pmap, Fin.val_castSucc]
  exact List.pmap_congr_left _ fun _ _ _ _ ↦ rfl

/-- The decreasing generator block `e δ i * e δ (i - 1) * ⋯ * e δ j` in `TemperleyLieb R δ n`,
equal to `1` when `i < j`. -/
def descBlock (δ : R) (i j : Fin (n - 1)) : TemperleyLieb R δ n :=
  ((descBlockList i j).map (e δ)).prod

/-- `descBlock δ i j` is the product of `e δ` along `descBlockList i j`. -/
theorem descBlock_def (δ : R) (i j : Fin (n - 1)) :
    descBlock δ i j = ((descBlockList i j).map (e δ)).prod := (rfl)

/-- A decreasing block of length one is a single generator. -/
@[simp]
theorem descBlock_self (δ : R) (i : Fin (n - 1)) : descBlock δ i i = e δ i := by
  simp [descBlock_def]

/-- When `i < j`, `descBlock δ i j = 1`. -/
theorem descBlock_of_lt (δ : R) {i j : Fin (n - 1)} (h : i < j) : descBlock δ i j = 1 := by
  simp [descBlock_def, descBlockList_of_lt h]

/-- Left multiplication by `e δ k` extends `descBlock δ i j` when `j ≤ i` and `i + 1 = k`. -/
theorem e_mul_descBlock_of_succ_eq (δ : R) {k i j : Fin (n - 1)} (hji : j ≤ i)
    (hik : i.val + 1 = k.val) :
    e δ k * descBlock δ i j = descBlock δ k j := by
  rw [descBlock_def, descBlock_def, ← descBlockList_cons hji hik, List.map_cons, List.prod_cons]

/-- Right multiplication by `e δ k` extends `descBlock δ i j` when `j ≤ i` and `k + 1 = j`. -/
theorem descBlock_mul_e_of_succ_eq (δ : R) {i j k : Fin (n - 1)} (hji : j ≤ i)
    (hkj : k.val + 1 = j.val) :
    descBlock δ i j * e δ k = descBlock δ i k := by
  rw [descBlock_def, descBlock_def, ← descBlockList_concat hji hkj, List.map_append,
    List.prod_append]
  simp

/-- A generator `e δ k` commutes with `descBlock δ i j` when `k` is at distance at least `2` from
every index in `[j, i]`. -/
theorem commute_descBlock_e (δ : R) {i j k : Fin (n - 1)}
    (h : k.val + 2 ≤ j.val ∨ i.val + 2 ≤ k.val) :
    Commute (descBlock δ i j) (e δ k) :=
  commute_prod_descIco_e δ i.isLt (by omega)

/-- Right multiplication of `descBlock δ i j` (`j ≤ i`) by its bottom generator `e δ j` absorbs via
`e j * e j = δ • e j`. -/
theorem descBlock_mul_e_self (δ : R) {i j : Fin (n - 1)} (hji : j ≤ i) :
    descBlock δ i j * e δ j = δ • descBlock δ i j := by
  rw [descBlock_def, descBlockList_eq_descIco_append_singleton hji, List.map_append,
    List.prod_append]
  simp [mul_assoc, e_mul_self]

/-- The augmentation kills every nonempty decreasing generator block (`j ≤ i`). -/
@[simp]
theorem aug_descBlock_of_le (δ : R) {i j : Fin (n - 1)} (hji : j ≤ i) :
    aug (descBlock δ i j) = 0 := by
  rw [descBlock_def, descBlockList_eq_descIco_append_singleton hji, List.map_append,
    List.prod_append]
  simp

/-- Strand inclusion sends a decreasing block to the decreasing block with `castSucc` endpoints. -/
@[simp]
theorem strandIncl_descBlock {m : ℕ} (δ : R) (i j : Fin m) :
    strandIncl (descBlock (R := R) (n := m + 1) δ i j) =
      descBlock (R := R) (n := m + 2) δ i.castSucc j.castSucc := by
  rw [descBlock_def, descBlock_def, ← map_castSucc_descBlockList, map_list_prod, List.map_map,
    List.map_map]
  congr 1
  exact List.map_congr_left fun x _ ↦ strandIncl_e x

/-- Internal zigzag absorption: when `j < k ≤ i`, multiplying `descBlock δ i j` on the right by
`e δ k` commutes `e δ k` past `e (k - 2) * ⋯ * e j` and straightens `e k * e (k - 1) * e k = e k`,
yielding a generator product with two fewer generators. -/
private theorem exists_list_descBlock_mul_e_of_lt_of_le (δ : R) {i j k : Fin (n - 1)}
    (hjk : j < k) (hki : k ≤ i) :
    ∃ t : List (Fin (n - 1)),
      t.length + 1 ≤ (descBlockList i j).length ∧
        (t.map (e δ)).prod = descBlock δ i j * e δ k := by
  have hk1 : k.val - 1 < n - 1 := by omega
  let km1 : Fin (n - 1) := ⟨k.val - 1, hk1⟩
  refine ⟨descBlockList i k ++ descIco j.val (k.val - 1) (by omega), ?_, ?_⟩
  · rw [List.length_append, length_descBlockList, length_descIco, length_descBlockList]
    omega
  · have hsplit₁ : descBlockList i j =
        descIco (k.val + 1) (i.val + 1) i.isLt ++ [k] ++ [km1] ++
          descIco j.val (k.val - 1) (by omega) := by
      rw [descBlockList, descIco_split i.isLt (mid := k.val - 1) (by omega) (by omega),
        descIco_split i.isLt (mid := k.val) (by omega) (by omega),
        descIco_split i.isLt (mid := k.val + 1) (by omega) (by omega)]
      have hk_eq : k.val - 1 + 1 = k.val := by omega
      have hkm1 : descIco (k.val - 1) k.val (by omega) = [km1] := by
        simpa [km1, hk_eq] using descIco_singleton km1
      rw [descIco_singleton k, hkm1, List.append_assoc, List.append_assoc]
    have hcomm := (commute_prod_descIco_e (R := R) δ (lo := j.val) (hi := k.val - 1)
      (by omega) (k := k) (Or.inr (by omega))).eq
    have hadj : e (R := R) δ k * e δ km1 * e δ k = e δ k :=
      e_mul_e_mul_e (Or.inr (by simp [km1]; omega))
    rw [descBlock_def, hsplit₁, descBlockList_eq_descIco_append_singleton hki]
    simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    calc ((descIco (k.val + 1) (i.val + 1) i.isLt).map (e δ)).prod * e δ k *
            ((descIco j.val (k.val - 1) _).map (e δ)).prod
        = ((descIco (k.val + 1) (i.val + 1) i.isLt).map (e δ)).prod *
            (e δ k * e δ km1 * e δ k) *
            ((descIco j.val (k.val - 1) _).map (e δ)).prod := by rw [hadj]
      _ = _ := by
          simp only [mul_assoc]
          rw [← mul_assoc (e δ k), hcomm]
          simp only [mul_assoc]

/-- Boundary zigzag absorption across two consecutive blocks: when the first block ends at `k` and
the second ends at `j₂ = k + 1`, right multiplication by `e δ k` commutes the first block's bottom
`e δ k` across `e i₂ * ⋯ * e (k + 2)` and straightens `e k * e (k + 1) * e k = e k`, dropping two
generators. -/
private theorem exists_list_descBlock_mul_descBlock_mul_e (δ : R) {i₁ i₂ j₂ k : Fin (n - 1)}
    (hk₁ : k ≤ i₁) (hkj : k.val + 1 = j₂.val) (hj₂ : j₂ ≤ i₂) :
    ∃ t : List (Fin (n - 1)),
      t.length + 1 ≤ (descBlockList i₁ k).length + (descBlockList i₂ j₂).length ∧
        (t.map (e δ)).prod = descBlock δ i₁ k * descBlock δ i₂ j₂ * e δ k := by
  refine ⟨descIco (k.val + 1) (i₁.val + 1) i₁.isLt ++
      descIco (j₂.val + 1) (i₂.val + 1) i₂.isLt ++ [k], ?_, ?_⟩
  · rw [List.length_append, List.length_append, List.length_singleton, length_descIco,
      length_descIco, length_descBlockList, length_descBlockList]
    omega
  · have hcomm := (commute_prod_descIco_e (R := R) δ (lo := j₂.val + 1) (hi := i₂.val + 1)
      i₂.isLt (k := k) (Or.inl (by omega))).eq
    have hadj : e (R := R) δ k * e δ j₂ * e δ k = e δ k :=
      e_mul_e_mul_e (Or.inl hkj)
    let P₁ := ((descIco (k.val + 1) (i₁.val + 1) i₁.isLt).map (e δ)).prod
    let P₂ := ((descIco (j₂.val + 1) (i₂.val + 1) i₂.isLt).map (e δ)).prod
    rw [descBlock_def, descBlock_def, descBlockList_eq_descIco_append_singleton hk₁,
      descBlockList_eq_descIco_append_singleton hj₂]
    simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    calc P₁ * P₂ * e δ k
        = P₁ * P₂ * (e δ k * e δ j₂ * e δ k) := by rw [hadj]
      _ = P₁ * (P₂ * e δ k) * (e δ j₂ * e δ k) := by simp only [mul_assoc]
      _ = P₁ * (e δ k * P₂) * (e δ j₂ * e δ k) := by rw [hcomm]
      _ = (P₁ * e δ k) * (P₂ * e δ j₂) * e δ k := by simp only [mul_assoc]

end DescBlock

/-! ### Jones reduced words -/

/-- A **Jones reduced word** on `n` strands, encoding a normal-form monomial
`(e i₁ * ⋯ * e j₁) * ⋯ * (e iᵣ * ⋯ * e jᵣ)` by the list of `(start, finish)` index pairs of its
decreasing generator blocks: each block has `jₛ ≤ iₛ`, and both the starting indices `iₛ` and the
ending indices `jₛ` are strictly increasing. -/
@[ext]
structure JonesWord (n : ℕ) where
  /-- The `(start, finish)` generator-index pairs of the decreasing blocks. -/
  blocks : List (Fin (n - 1) × Fin (n - 1))
  /-- In every block `(i, j)`, the ending index `j` does not exceed the starting index `i`. -/
  snd_le_fst : ∀ p ∈ blocks, p.2 ≤ p.1
  /-- The starting indices of consecutive blocks are strictly increasing. -/
  pairwise_fst_lt : blocks.Pairwise fun p q ↦ p.1 < q.1
  /-- The ending indices of consecutive blocks are strictly increasing. -/
  pairwise_snd_lt : blocks.Pairwise fun p q ↦ p.2 < q.2
  deriving DecidableEq

namespace JonesWord

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The empty Jones reduced word, whose evaluation in `TemperleyLieb R δ n` is `1`. -/
def empty : JonesWord n where
  blocks := []
  snd_le_fst := by simp
  pairwise_fst_lt := .nil
  pairwise_snd_lt := .nil

instance : Inhabited (JonesWord n) := ⟨empty⟩

/-- The empty reduced word has no blocks. -/
@[simp]
theorem blocks_empty : (empty : JonesWord n).blocks = [] := (rfl)

/-- The single-generator Jones reduced word `[(i, i)]`. -/
def singleton (i : Fin (n - 1)) : JonesWord n where
  blocks := [(i, i)]
  snd_le_fst := by simp
  pairwise_fst_lt := List.pairwise_singleton _ _
  pairwise_snd_lt := List.pairwise_singleton _ _

/-- Blocks of `singleton i`. -/
@[simp]
theorem blocks_singleton (i : Fin (n - 1)) : (singleton i).blocks = [(i, i)] := (rfl)

/-- Append a final decreasing block `(i, j)` with `j ≤ i` whose start and end strictly exceed those
of every block in `w`. -/
def snoc (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) : JonesWord n where
  blocks := w.blocks ++ [(i, j)]
  snd_le_fst p hp := by
    rcases List.mem_append.1 hp with hp | hp
    · exact w.snd_le_fst p hp
    · obtain rfl := List.mem_singleton.1 hp
      exact hji
  pairwise_fst_lt := List.pairwise_append.2
    ⟨w.pairwise_fst_lt, List.pairwise_singleton _ _, fun p hp q hq ↦ by
      obtain rfl := List.mem_singleton.1 hq; exact hi p hp⟩
  pairwise_snd_lt := List.pairwise_append.2
    ⟨w.pairwise_snd_lt, List.pairwise_singleton _ _, fun p hp q hq ↦ by
      obtain rfl := List.mem_singleton.1 hq; exact hj p hp⟩

/-- Blocks of `w.snoc i j hji hi hj`. -/
@[simp]
theorem blocks_snoc (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    (w.snoc i j hji hi hj).blocks = w.blocks ++ [(i, j)] := (rfl)

/-- Appending a decreasing block yields a nonempty Jones reduced word. -/
@[simp]
theorem snoc_ne_empty (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    w.snoc i j hji hi hj ≠ empty := fun h ↦ by
  simpa using congrArg (List.length ∘ blocks) h

/-- Drop the last decreasing block of a Jones reduced word (leaving `empty` untouched). -/
def dropLast (w : JonesWord n) : JonesWord n where
  blocks := w.blocks.dropLast
  snd_le_fst p hp := w.snd_le_fst p (List.dropLast_subset _ hp)
  pairwise_fst_lt := w.pairwise_fst_lt.sublist (List.dropLast_sublist _)
  pairwise_snd_lt := w.pairwise_snd_lt.sublist (List.dropLast_sublist _)

/-- Blocks of `w.dropLast`. -/
@[simp]
theorem blocks_dropLast (w : JonesWord n) : w.dropLast.blocks = w.blocks.dropLast := (rfl)

/-- Dropping the last block of `empty` yields `empty`. -/
@[simp]
theorem dropLast_empty : (empty : JonesWord n).dropLast = empty := by
  ext1
  simp

/-- Dropping the last block of `w.snoc i j …` recovers `w`. -/
@[simp]
theorem dropLast_snoc (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    (w.snoc i j hji hi hj).dropLast = w := by
  ext1
  simp

/-- Structural induction on `JonesWord n` by appending decreasing blocks from the right (`snoc`). -/
@[elab_as_elim]
theorem snoc_induction_on {motive : JonesWord n → Prop} (w : JonesWord n) (empty : motive empty)
    (snoc : ∀ (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
      (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j),
      motive w → motive (w.snoc i j hji hi hj)) : motive w := by
  obtain ⟨blocks, hle, hfst, hsnd⟩ := w
  induction blocks using List.reverseRecOn with
  | nil => exact empty
  | append_singleton l p ih =>
    obtain ⟨hfst_l, -, hfst_last⟩ := List.pairwise_append.1 hfst
    obtain ⟨hsnd_l, -, hsnd_last⟩ := List.pairwise_append.1 hsnd
    let w₀ : JonesWord n :=
      ⟨l, fun q hq ↦ hle q (List.mem_append_left _ hq), hfst_l, hsnd_l⟩
    exact snoc w₀ p.1 p.2 (hle p (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun q hq ↦ hfst_last q hq p (List.mem_singleton_self _))
      (fun q hq ↦ hsnd_last q hq p (List.mem_singleton_self _))
      (ih w₀.snd_le_fst hfst_l hsnd_l)

/-- Underlying generator-index list of a Jones reduced word, obtained by concatenating the
decreasing index lists of its blocks. -/
def toList (w : JonesWord n) : List (Fin (n - 1)) :=
  w.blocks.flatMap fun p ↦ descBlockList p.1 p.2

/-- `w.toList` is the concatenation of `descBlockList p.1 p.2` across `p ∈ w.blocks`. -/
theorem toList_def (w : JonesWord n) :
    w.toList = w.blocks.flatMap fun p ↦ descBlockList p.1 p.2 := (rfl)

/-- `empty.toList` is empty. -/
@[simp]
theorem toList_empty : (empty : JonesWord n).toList = [] := (rfl)

/-- `(singleton i).toList` is `[i]`. -/
@[simp]
theorem toList_singleton (i : Fin (n - 1)) : (singleton i).toList = [i] := by
  simp [toList_def]

/-- `toList` on `snoc` appends `descBlockList i j`. -/
@[simp]
theorem toList_snoc (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    (w.snoc i j hji hi hj).toList = w.toList ++ descBlockList i j := by
  simp [toList_def, blocks_snoc]

/-- Total number of generators in a Jones reduced word, equal to `∑ (iₛ - jₛ + 1)`. -/
def wordLength (w : JonesWord n) : ℕ :=
  (w.blocks.map fun p ↦ p.1.val + 1 - p.2.val).sum

/-- `w.wordLength` is the sum of `p.1 + 1 - p.2` over `p ∈ w.blocks`. -/
theorem wordLength_def (w : JonesWord n) :
    w.wordLength = (w.blocks.map fun p ↦ p.1.val + 1 - p.2.val).sum := (rfl)

/-- The empty reduced word has word length `0`. -/
@[simp]
theorem wordLength_empty : (empty : JonesWord n).wordLength = 0 := (rfl)

/-- Word length of `singleton i` is `1`. -/
@[simp]
theorem wordLength_singleton (i : Fin (n - 1)) : (singleton i).wordLength = 1 := by
  simp [wordLength_def]

/-- Word length of `snoc` adds the length `i - j + 1` of the new block. -/
@[simp]
theorem wordLength_snoc (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    (w.snoc i j hji hi hj).wordLength = w.wordLength + (i.val + 1 - j.val) := by
  simp [wordLength_def, blocks_snoc]

/-- `w.toList` has length `w.wordLength`. -/
@[simp]
theorem length_toList (w : JonesWord n) : w.toList.length = w.wordLength := by
  simp [toList_def, wordLength_def, List.length_flatMap]

/-- A Jones reduced word has word length `0` if and only if it is `empty`. -/
@[simp]
theorem wordLength_eq_zero_iff {w : JonesWord n} : w.wordLength = 0 ↔ w = empty := by
  induction w using snoc_induction_on with
  | empty => simp
  | snoc w i j hji hi hj _ =>
    simp only [wordLength_snoc, snoc_ne_empty, iff_false]
    omega

/-- Evaluate a Jones reduced word in `TemperleyLieb R δ n` as the product of its decreasing
generator blocks. -/
def eval (δ : R) (w : JonesWord n) : TemperleyLieb R δ n :=
  (w.blocks.map fun p ↦ descBlock δ p.1 p.2).prod

/-- `w.eval δ` is the product of `descBlock δ p.1 p.2` over `p ∈ w.blocks`. -/
theorem eval_def (δ : R) (w : JonesWord n) :
    w.eval δ = (w.blocks.map fun p ↦ descBlock δ p.1 p.2).prod := (rfl)

/-- Evaluating the empty reduced word yields `1`. -/
@[simp]
theorem eval_empty (δ : R) : (empty : JonesWord n).eval δ = 1 := (rfl)

/-- Evaluating `singleton i` yields the generator `e δ i`. -/
@[simp]
theorem eval_singleton (δ : R) (i : Fin (n - 1)) : (singleton i).eval δ = e δ i := by
  simp [eval_def]

/-- Evaluating `w.snoc i j …` multiplies `w.eval δ` on the right by `descBlock δ i j`. -/
@[simp]
theorem eval_snoc (δ : R) (w : JonesWord n) (i j : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w.blocks, p.1 < i) (hj : ∀ p ∈ w.blocks, p.2 < j) :
    (w.snoc i j hji hi hj).eval δ = w.eval δ * descBlock δ i j := by
  simp [eval_def, blocks_snoc]

/-- Evaluating a reduced word agrees with multiplying the generators along `w.toList`. -/
theorem prod_map_toList (δ : R) (w : JonesWord n) :
    (w.toList.map (e δ)).prod = w.eval δ := by
  induction w using snoc_induction_on with
  | empty => simp
  | snoc w i j hji hi hj ih =>
    rw [toList_snoc, List.map_append, List.prod_append, ih, eval_snoc, descBlock_def]

/-- The augmentation maps `empty.eval δ` to `1` and kills the evaluation of every nonempty reduced
word. -/
@[simp]
theorem aug_eval (δ : R) (w : JonesWord n) :
    aug (w.eval δ) = if w = empty then 1 else 0 := by
  induction w using snoc_induction_on with
  | empty => simp
  | snoc w i j hji hi hj _ => simp [aug_descBlock_of_le δ hji]

/-- Embedding of Jones reduced words on `m + 1` strands into those on `m + 2` strands by mapping
each generator index along `Fin.castSucc`. -/
def castSucc {m : ℕ} : JonesWord (m + 1) ↪ JonesWord (m + 2) where
  toFun w :=
    { blocks := w.blocks.map (Prod.map (Fin.castSucc (n := m)) (Fin.castSucc (n := m)))
      snd_le_fst := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact Fin.castSucc_le_castSucc_iff.2 (w.snd_le_fst p hp)
      pairwise_fst_lt := by
        rw [List.pairwise_map]
        exact w.pairwise_fst_lt.imp fun h ↦ Fin.castSucc_lt_castSucc_iff.2 h
      pairwise_snd_lt := by
        rw [List.pairwise_map]
        exact w.pairwise_snd_lt.imp fun h ↦ Fin.castSucc_lt_castSucc_iff.2 h }
  inj' w₁ w₂ h := by
    have hmap : Function.Injective
        (Prod.map (Fin.castSucc (n := m)) (Fin.castSucc (n := m))) :=
      fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab ↦ Prod.ext
        (Fin.castSucc_injective m (congrArg Prod.fst hab))
        (Fin.castSucc_injective m (congrArg Prod.snd hab))
    ext1
    exact List.map_injective_iff.2 hmap (congrArg blocks h)

/-- Blocks of `w.castSucc`. -/
@[simp]
theorem blocks_castSucc {m : ℕ} (w : JonesWord (m + 1)) :
    (w.castSucc).blocks =
      w.blocks.map (Prod.map (Fin.castSucc (n := m)) (Fin.castSucc (n := m))) := (rfl)

/-- `castSucc` preserves `empty`. -/
@[simp]
theorem castSucc_empty {m : ℕ} : (empty : JonesWord (m + 1)).castSucc = empty := by
  ext1
  simp

/-- `castSucc` sends `singleton i` to `singleton i.castSucc`. -/
@[simp]
theorem castSucc_singleton {m : ℕ} (i : Fin m) :
    (singleton (n := m + 1) i).castSucc = singleton (n := m + 2) i.castSucc := by
  ext1
  simp

/-- `castSucc` preserves `wordLength`. -/
@[simp]
theorem wordLength_castSucc {m : ℕ} (w : JonesWord (m + 1)) :
    (w.castSucc).wordLength = w.wordLength := by
  simp [wordLength_def, Function.comp_def]

/-- `toList` of `w.castSucc` maps `w.toList` along `Fin.castSucc`. -/
@[simp]
theorem toList_castSucc {m : ℕ} (w : JonesWord (m + 1)) :
    (w.castSucc).toList = w.toList.map Fin.castSucc := by
  simp only [toList_def, blocks_castSucc, List.flatMap_map, List.map_flatMap]
  congr 1
  funext p
  exact (map_castSucc_descBlockList p.1 p.2).symm

/-- Strand inclusion intertwines evaluation of Jones reduced words with `castSucc`. -/
@[simp]
theorem strandIncl_eval {m : ℕ} (δ : R) (w : JonesWord (m + 1)) :
    strandIncl (w.eval δ) = (w.castSucc).eval δ := by
  simp only [eval_def, blocks_castSucc, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ ↦ strandIncl_descBlock δ p.1 p.2

/-- Set of starting block indices of a Jones reduced word. -/
def startFinset (w : JonesWord n) : Finset (Fin (n - 1)) :=
  (w.blocks.map Prod.fst).toFinset

/-- Set of ending block indices of a Jones reduced word. -/
def endFinset (w : JonesWord n) : Finset (Fin (n - 1)) :=
  (w.blocks.map Prod.snd).toFinset

/-- `w.startFinset` is the finset of first coordinates of `w.blocks`. -/
theorem startFinset_def (w : JonesWord n) :
    w.startFinset = (w.blocks.map Prod.fst).toFinset := (rfl)

/-- `w.endFinset` is the finset of second coordinates of `w.blocks`. -/
theorem endFinset_def (w : JonesWord n) :
    w.endFinset = (w.blocks.map Prod.snd).toFinset := (rfl)

/-- Membership in `w.startFinset`. -/
@[simp]
theorem mem_startFinset {w : JonesWord n} {i : Fin (n - 1)} :
    i ∈ w.startFinset ↔ ∃ j, (i, j) ∈ w.blocks := by
  simp [startFinset_def]

/-- Membership in `w.endFinset`. -/
@[simp]
theorem mem_endFinset {w : JonesWord n} {j : Fin (n - 1)} :
    j ∈ w.endFinset ↔ ∃ i, (i, j) ∈ w.blocks := by
  simp [endFinset_def]

/-- Sorting `w.startFinset` in increasing order recovers `w.blocks.map Prod.fst`. -/
theorem sort_startFinset (w : JonesWord n) :
    w.startFinset.sort (· ≤ ·) = w.blocks.map Prod.fst := by
  have hlt : (w.blocks.map Prod.fst).Pairwise (· < ·) := List.pairwise_map.2 w.pairwise_fst_lt
  exact (List.toFinset_sort (· ≤ ·) (hlt.imp ne_of_lt)).2 (hlt.imp le_of_lt)

/-- Sorting `w.endFinset` in increasing order recovers `w.blocks.map Prod.snd`. -/
theorem sort_endFinset (w : JonesWord n) :
    w.endFinset.sort (· ≤ ·) = w.blocks.map Prod.snd := by
  have hlt : (w.blocks.map Prod.snd).Pairwise (· < ·) := List.pairwise_map.2 w.pairwise_snd_lt
  exact (List.toFinset_sort (· ≤ ·) (hlt.imp ne_of_lt)).2 (hlt.imp le_of_lt)

/-- Cardinality of `w.startFinset` equals the number of blocks in `w`. -/
@[simp]
theorem card_startFinset (w : JonesWord n) : w.startFinset.card = w.blocks.length := by
  rw [← Finset.length_sort (· ≤ ·), w.sort_startFinset, List.length_map]

/-- Cardinality of `w.endFinset` equals the number of blocks in `w`. -/
@[simp]
theorem card_endFinset (w : JonesWord n) : w.endFinset.card = w.blocks.length := by
  rw [← Finset.length_sort (· ≤ ·), w.sort_endFinset, List.length_map]

/-- A Jones reduced word is uniquely determined by `(w.startFinset, w.endFinset)`. -/
theorem blocks_eq_zip_sort (w : JonesWord n) :
    List.zip (w.startFinset.sort (· ≤ ·)) (w.endFinset.sort (· ≤ ·)) = w.blocks := by
  rw [w.sort_startFinset, w.sort_endFinset]
  induction w.blocks with
  | nil => rfl
  | cons p l ih => exact congrArg (p :: ·) ih

/-- Equivalence between `JonesWord n` and pairs `(I, J)` of equal-sized subsets of `Fin (n - 1)`
whose sorted elements satisfy `jₛ ≤ iₛ` in each position. -/
def equivFinsetPair :
    JonesWord n ≃
      {s : Finset (Fin (n - 1)) × Finset (Fin (n - 1)) //
        s.1.card = s.2.card ∧
          ∀ p ∈ List.zip (s.1.sort (· ≤ ·)) (s.2.sort (· ≤ ·)), p.2 ≤ p.1} where
  toFun w := ⟨(w.startFinset, w.endFinset), by
    rw [w.card_startFinset, w.card_endFinset]
    exact ⟨rfl, w.blocks_eq_zip_sort.symm ▸ w.snd_le_fst⟩⟩
  invFun s :=
    { blocks := List.zip (s.1.1.sort (· ≤ ·)) (s.1.2.sort (· ≤ ·))
      snd_le_fst := s.2.2
      pairwise_fst_lt := by
        have hlen : (s.1.1.sort (· ≤ ·)).length = (s.1.2.sort (· ≤ ·)).length := by simp [s.2.1]
        rw [← List.pairwise_map, List.map_fst_zip (le_of_eq hlen)]
        exact ((s.1.1.pairwise_sort (· ≤ ·)).sortedLE.sortedLT_of_nodup
          (s.1.1.sort_nodup (· ≤ ·))).pairwise
      pairwise_snd_lt := by
        have hlen : (s.1.1.sort (· ≤ ·)).length = (s.1.2.sort (· ≤ ·)).length := by simp [s.2.1]
        rw [← List.pairwise_map, List.map_snd_zip (ge_of_eq hlen)]
        exact ((s.1.2.pairwise_sort (· ≤ ·)).sortedLE.sortedLT_of_nodup
          (s.1.2.sort_nodup (· ≤ ·))).pairwise }
  left_inv w := by
    ext1
    exact w.blocks_eq_zip_sort
  right_inv s := by
    have hlen : (s.1.1.sort (· ≤ ·)).length = (s.1.2.sort (· ≤ ·)).length := by simp [s.2.1]
    ext x <;>
      simp [startFinset_def, endFinset_def, List.map_fst_zip (le_of_eq hlen),
        List.map_snd_zip (ge_of_eq hlen)]

/-- Underlying subset pair of `equivFinsetPair w`. -/
@[simp]
theorem coe_equivFinsetPair (w : JonesWord n) :
    (equivFinsetPair w).val = (w.startFinset, w.endFinset) := (rfl)

/-- Blocks of `equivFinsetPair.symm s`. -/
@[simp]
theorem blocks_equivFinsetPair_symm
    (s : {s : Finset (Fin (n - 1)) × Finset (Fin (n - 1)) //
      s.1.card = s.2.card ∧
        ∀ p ∈ List.zip (s.1.sort (· ≤ ·)) (s.2.sort (· ≤ ·)), p.2 ≤ p.1}) :
    (equivFinsetPair.symm s).blocks = List.zip (s.1.1.sort (· ≤ ·)) (s.1.2.sort (· ≤ ·)) := (rfl)

instance : Fintype (JonesWord n) :=
  Fintype.ofEquiv _ equivFinsetPair.symm

/-- On at most one strand there are no generators, so `empty` is the unique Jones reduced word. -/
@[instance_reducible]
def uniqueOfLeOne (hn : n ≤ 1) : Unique (JonesWord n) where
  default := empty
  uniq w := by
    ext1
    cases h : w.blocks with
    | nil => rfl
    | cons p _ => exact absurd p.1.isLt (by omega)

instance : Unique (JonesWord 0) := uniqueOfLeOne (Nat.zero_le 1)

instance : Unique (JonesWord 1) := uniqueOfLeOne le_rfl

end JonesWord

/-! ### Reduction of arbitrary generator words to Jones normal form -/

section NormalForm

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Outcome of multiplying a Jones reduced word `w` on the right by `e δ k`: either an extended
reduced word of length `w.wordLength + 1` whose block coordinates come from `w` or `k`, or `δ ^ b`
times a generator product of length at most `w.wordLength`. -/
private abbrev StepRightOutcome (δ : R) (w : JonesWord n) (k : Fin (n - 1)) : Prop :=
  (∃ w' : JonesWord n,
      w'.wordLength = w.wordLength + 1 ∧
      w'.eval δ = w.eval δ * e δ k ∧
      (∀ q ∈ w'.blocks,
        (∃ p ∈ w.blocks, q.1 = p.1 ∧ (q.2 = p.2 ∨ q.2 = k)) ∨ q = (k, k))) ∨
    ∃ (b : ℕ) (l : List (Fin (n - 1))),
      l.length ≤ w.wordLength ∧ w.eval δ * e δ k = δ ^ b • (l.map (e δ)).prod

/-- Adjacent case `k + 1 = j` when multiplying `w₀.snoc i j …` on the right by `e δ k`. -/
private theorem stepRight_adj (δ : R) (w₀ : JonesWord n) (i j k : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w₀.blocks, p.1 < i) (hj : ∀ p ∈ w₀.blocks, p.2 < j)
    (hki : k ≤ i) (hsucc : k.val + 1 = j.val) :
    StepRightOutcome δ (w₀.snoc i j hji hi hj) k := by
  induction w₀ using JonesWord.snoc_induction_on with
  | empty =>
    refine Or.inl ⟨JonesWord.empty.snoc i k hki (by simp) (by simp), ?_, ?_, ?_⟩
    · simp only [JonesWord.wordLength_snoc, JonesWord.wordLength_empty]
      omega
    · simp [descBlock_mul_e_of_succ_eq δ hji hsucc]
    · intro q hq
      obtain rfl := List.mem_singleton.1 (by simpa using hq)
      exact Or.inl ⟨(i, j), by simp, rfl, Or.inr rfl⟩
  | snoc w₁ i₁ j₁ hj₁i₁ hi₁ hj₁ _ =>
    have hj₁j : j₁.val < j.val :=
      hj (i₁, j₁) (List.mem_append_right _ (List.mem_singleton_self _))
    have hj₁k : j₁ ≤ k := Fin.le_def.2 (by omega)
    rcases lt_or_eq_of_le hj₁k with hj₁_lt | rfl
    · -- `j₁ < k`: extending `(i, j)` to `(i, k)` preserves strict monotonicity of block ends.
      have hj' : ∀ p ∈ (w₁.snoc i₁ j₁ hj₁i₁ hi₁ hj₁).blocks, p.2 < k := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact (hj₁ p hp).trans hj₁_lt
        · obtain rfl := List.mem_singleton.1 hp; exact hj₁_lt
      refine Or.inl ⟨(w₁.snoc i₁ j₁ hj₁i₁ hi₁ hj₁).snoc i k hki hi hj', ?_, ?_, ?_⟩
      · simp only [JonesWord.wordLength_snoc]
        omega
      · simp [mul_assoc, descBlock_mul_e_of_succ_eq δ hji hsucc]
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact Or.inl ⟨q, List.mem_append_left _ hq, rfl, Or.inl rfl⟩
        · obtain rfl := List.mem_singleton.1 hq
          exact Or.inl ⟨(i, j), List.mem_append_right _ (List.mem_singleton_self _),
            rfl, Or.inr rfl⟩
    · -- `j₁ = k`: boundary zigzag across `(i₁, k)` and `(i, j)`.
      obtain ⟨t, hlen, hprod⟩ := exists_list_descBlock_mul_descBlock_mul_e δ hj₁i₁ hsucc hji
      refine Or.inr ⟨0, w₁.toList ++ t, ?_, ?_⟩
      · rw [List.length_append, w₁.length_toList, JonesWord.wordLength_snoc,
          JonesWord.wordLength_snoc]
        rw [length_descBlockList, length_descBlockList] at hlen
        omega
      · rw [pow_zero, one_smul, List.map_append, List.prod_append, w₁.prod_map_toList, hprod,
          JonesWord.eval_snoc, JonesWord.eval_snoc]
        simp only [mul_assoc]

/-- Distant case `k + 2 ≤ j` when multiplying `w₀.snoc i j …` on the right by `e δ k`: commute
`e δ k` left past `descBlock δ i j` and transport the recursive outcome from `w₀`. -/
private theorem stepRight_comm (δ : R) (w₀ : JonesWord n) (i j k : Fin (n - 1)) (hji : j ≤ i)
    (hi : ∀ p ∈ w₀.blocks, p.1 < i) (hj : ∀ p ∈ w₀.blocks, p.2 < j)
    (hdist : k.val + 2 ≤ j.val) (ih : StepRightOutcome δ w₀ k) :
    StepRightOutcome δ (w₀.snoc i j hji hi hj) k := by
  have hkj_lt : k < j := by omega
  have hcomm : descBlock (R := R) δ i j * e δ k = e δ k * descBlock δ i j :=
    (commute_descBlock_e δ (Or.inl hdist)).eq
  rcases ih with ⟨u₀, hu_len, hu_eval, hu_mem⟩ | ⟨b, l₀, hl_len, hl_eval⟩
  · have hi_u : ∀ q ∈ u₀.blocks, q.1 < i := by
      intro q hq
      rcases hu_mem q hq with ⟨p, hp, hq1, -⟩ | rfl
      · exact hq1 ▸ hi p hp
      · exact lt_of_lt_of_le hkj_lt hji
    have hj_u : ∀ q ∈ u₀.blocks, q.2 < j := by
      intro q hq
      rcases hu_mem q hq with ⟨p, hp, -, hq2 | hq2⟩ | rfl
      · exact hq2 ▸ hj p hp
      · exact hq2 ▸ hkj_lt
      · exact hkj_lt
    refine Or.inl ⟨u₀.snoc i j hji hi_u hj_u, ?_, ?_, ?_⟩
    · rw [JonesWord.wordLength_snoc, JonesWord.wordLength_snoc, hu_len]
      omega
    · rw [JonesWord.eval_snoc, JonesWord.eval_snoc, mul_assoc, hcomm, ← mul_assoc, hu_eval]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · rcases hu_mem q hq with ⟨p, hp, h1, h2⟩ | hqk
        · exact Or.inl ⟨p, List.mem_append_left _ hp, h1, h2⟩
        · exact Or.inr hqk
      · obtain rfl := List.mem_singleton.1 hq
        exact Or.inl ⟨(i, j), List.mem_append_right _ (List.mem_singleton_self _),
          rfl, Or.inl rfl⟩
  · refine Or.inr ⟨b, l₀ ++ descBlockList i j, ?_, ?_⟩
    · rw [List.length_append, length_descBlockList, JonesWord.wordLength_snoc]
      omega
    · rw [JonesWord.eval_snoc, mul_assoc, hcomm, ← mul_assoc, hl_eval, smul_mul_assoc,
        List.map_append, List.prod_append, ← descBlock_def]

private theorem stepRight (δ : R) (w : JonesWord n) (k : Fin (n - 1)) :
    StepRightOutcome δ w k := by
  induction w using JonesWord.snoc_induction_on with
  | empty =>
    refine Or.inl ⟨JonesWord.singleton k, by simp, by simp, fun q hq ↦ ?_⟩
    exact Or.inr (List.mem_singleton.1 hq)
  | snoc w₀ i j hji hi hj ih =>
    by_cases hik : i < k
    · -- `k` strictly exceeds the last block's start (hence also its end): append `(k, k)`.
      have hjk : j < k := lt_of_le_of_lt hji hik
      have hi' : ∀ p ∈ (w₀.snoc i j hji hi hj).blocks, p.1 < k := fun p hp ↦ by
        rcases List.mem_append.1 hp with hp | hp
        · exact (hi p hp).trans hik
        · obtain rfl := List.mem_singleton.1 hp; exact hik
      have hj' : ∀ p ∈ (w₀.snoc i j hji hi hj).blocks, p.2 < k := fun p hp ↦ by
        rcases List.mem_append.1 hp with hp | hp
        · exact (hj p hp).trans hjk
        · obtain rfl := List.mem_singleton.1 hp; exact hjk
      refine Or.inl ⟨(w₀.snoc i j hji hi hj).snoc k k le_rfl hi' hj', by simp, by simp, ?_⟩
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact Or.inl ⟨q, hq, rfl, Or.inl rfl⟩
      · exact Or.inr (List.mem_singleton.1 hq)
    · have hki : k ≤ i := not_lt.1 hik
      by_cases hjk : j < k
      · -- `j < k ≤ i`: internal zigzag absorption inside the last block.
        obtain ⟨t, hlen, hprod⟩ := exists_list_descBlock_mul_e_of_lt_of_le δ hjk hki
        refine Or.inr ⟨0, w₀.toList ++ t, ?_, ?_⟩
        · rw [List.length_append, w₀.length_toList, JonesWord.wordLength_snoc]
          rw [length_descBlockList] at hlen
          omega
        · rw [pow_zero, one_smul, List.map_append, List.prod_append, w₀.prod_map_toList, hprod,
            JonesWord.eval_snoc, mul_assoc]
      · rcases eq_or_lt_of_le (not_lt.1 hjk) with rfl | hkj_lt
        · -- `k = j`: quadratic absorption `descBlock δ i k * e δ k = δ • descBlock δ i k`.
          refine Or.inr ⟨1, (w₀.snoc i k hki hi hj).toList, ?_, ?_⟩
          · rw [JonesWord.length_toList]
          · rw [pow_one, JonesWord.prod_map_toList, JonesWord.eval_snoc, mul_assoc,
              descBlock_mul_e_self δ hki, mul_smul_comm]
        · by_cases hsucc : k.val + 1 = j.val
          · exact stepRight_adj δ w₀ i j k hji hi hj hki hsucc
          · exact stepRight_comm δ w₀ i j k hji hi hj (by omega) ih

/-- **Jones word reduction.** Every product of generators `(l.map (e δ)).prod` in
`TemperleyLieb R δ n` reduces to `δ ^ m • w.eval δ` for some `m : ℕ` and some Jones reduced word
`w` of word length at most `l.length`. -/
theorem exists_jonesWord_of_list (δ : R) (l : List (Fin (n - 1))) :
    ∃ (m : ℕ) (w : JonesWord n),
      w.wordLength ≤ l.length ∧ (l.map (e δ)).prod = δ ^ m • w.eval δ := by
  suffices ∀ N : ℕ, ∀ l : List (Fin (n - 1)), l.length = N →
      ∃ (m : ℕ) (w : JonesWord n),
        w.wordLength ≤ l.length ∧ (l.map (e δ)).prod = δ ^ m • w.eval δ from
    this l.length l rfl
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro l hl
    rcases l.eq_nil_or_concat with rfl | ⟨l₀, k, rfl⟩
    · exact ⟨0, JonesWord.empty, by simp, by simp⟩
    · rw [List.concat_eq_append] at hl ⊢
      have hl₀ : l₀.length < N := by rw [← hl, List.length_append, List.length_singleton]; omega
      obtain ⟨m₀, w₀, hw₀_len, hw₀_eq⟩ := ih l₀.length hl₀ l₀ rfl
      rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, hw₀_eq,
        smul_mul_assoc]
      rcases stepRight δ w₀ k with ⟨w', hw'_len, hw'_eq, -⟩ | ⟨b, l', hl'_len, hl'_eq⟩
      · refine ⟨m₀, w', ?_, by rw [hw'_eq]⟩
        rw [List.length_append, List.length_singleton, hw'_len]
        exact Nat.succ_le_succ hw₀_len
      · have hl'_lt : l'.length < N := lt_of_le_of_lt (hl'_len.trans hw₀_len) hl₀
        obtain ⟨m₁, w₁, hw₁_len, hw₁_eq⟩ := ih l'.length hl'_lt l' rfl
        refine ⟨m₀ + b + m₁, w₁, ?_, ?_⟩
        · rw [List.length_append, List.length_singleton]
          exact hw₁_len.trans (hl'_len.trans (hw₀_len.trans (Nat.le_succ _)))
        · rw [hl'_eq, hw₁_eq, smul_smul, smul_smul, ← pow_add, ← pow_add, add_assoc]

/-- **The Jones reduced words span the Temperley–Lieb algebra.** Over any commutative semiring `R`,
`TemperleyLieb R δ n` is spanned as an `R`-module by the evaluations of `JonesWord n`. -/
theorem span_range_jonesWord_eval (δ : R) (n : ℕ) :
    Submodule.span R (Set.range (JonesWord.eval (R := R) δ (n := n))) = ⊤ := by
  rw [eq_top_iff, ← Algebra.top_toSubmodule, ← adjoin_range_e (R := R) (δ := δ) (n := n),
    Algebra.adjoin_eq_span, Submodule.span_le]
  intro x hx
  obtain ⟨L, hL, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
  obtain ⟨l, rfl⟩ : L ∈ Set.range (List.map (e δ)) := (Set.range_list_map (e δ)).symm ▸ hL
  obtain ⟨m, w, -, hw⟩ := exists_jonesWord_of_list δ l
  rw [hw]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

end NormalForm

/-! ### Catalan enumeration of Jones reduced words -/

section CatalanCount

open Finset

/-- Reduced words on `n` strands whose block start indices are `< m` and end indices are `< b`. -/
private def jonesWordsBounded (n m b : ℕ) : Finset (JonesWord n) :=
  {w : JonesWord n | ∀ p ∈ w.blocks, p.1.val < m ∧ p.2.val < b}

private theorem mem_jonesWordsBounded {n m b : ℕ} {w : JonesWord n} :
    w ∈ jonesWordsBounded n m b ↔ ∀ p ∈ w.blocks, p.1.val < m ∧ p.2.val < b :=
  Finset.mem_filter_univ w

private theorem jonesWordsBounded_top (n : ℕ) :
    jonesWordsBounded n (n - 1) (n - 1) = Finset.univ := by
  ext w
  simp [mem_jonesWordsBounded, Fin.is_lt]

private theorem jonesWordsBounded_zero_right (n m : ℕ) :
    jonesWordsBounded n m 0 = {JonesWord.empty} := by
  ext w
  rw [mem_jonesWordsBounded, Finset.mem_singleton]
  constructor
  · intro hw
    ext1
    cases h : w.blocks with
    | nil => rfl
    | cons p _ => exact absurd (hw p (h ▸ List.mem_cons_self)).2 (Nat.not_lt_zero _)
  · rintro rfl
    simp

private theorem jonesWordsBounded_zero_left (n b : ℕ) :
    jonesWordsBounded n 0 b = {JonesWord.empty} := by
  ext w
  rw [mem_jonesWordsBounded, Finset.mem_singleton]
  constructor
  · intro hw
    ext1
    cases h : w.blocks with
    | nil => rfl
    | cons p _ => exact absurd (hw p (h ▸ List.mem_cons_self)).1 (Nat.not_lt_zero _)
  · rintro rfl
    simp

private theorem jonesWordsBounded_eq_self_of_le {n m b : ℕ} (h : m ≤ b) :
    jonesWordsBounded n m b = jonesWordsBounded n m m := by
  ext w
  simp only [mem_jonesWordsBounded]
  refine forall₂_congr fun p hp ↦ ?_
  have hle : p.2.val ≤ p.1.val := w.snd_le_fst p hp
  exact ⟨fun hp' ↦ ⟨hp'.1, lt_of_le_of_lt hle hp'.1⟩,
    fun hp' ↦ ⟨hp'.1, lt_of_lt_of_le hp'.2 h⟩⟩

/-- Forward map of the ballot bijection: send `u ∈ jonesWordsBounded n m (b + 1)` either to
`u.snoc m b` (when all block ends in `u` are `< b`) or to `u` itself (when `u` already has a block
ending at `b`). -/
private def ballotForward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m) (u : JonesWord n) :
    JonesWord n :=
  if h : (∀ p ∈ u.blocks, p.1.val < m) ∧ (∀ p ∈ u.blocks, p.2.val < b) then
    u.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm h.1 h.2
  else
    u

/-- Inverse map of the ballot bijection: keep `w` if all block starts are `< m`, otherwise drop its
final block `(m, b)`. -/
private def ballotBackward {n : ℕ} (m : ℕ) (w : JonesWord n) : JonesWord n :=
  if ∀ p ∈ w.blocks, p.1.val < m then w else w.dropLast

private theorem ballotBackward_ballotForward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {u : JonesWord n} (hu : u ∈ jonesWordsBounded n m (b + 1)) :
    ballotBackward m (ballotForward hm hbm u) = u := by
  rw [mem_jonesWordsBounded] at hu
  have hu₁ : ∀ p ∈ u.blocks, p.1.val < m := fun p hp ↦ (hu p hp).1
  by_cases hu₂ : ∀ p ∈ u.blocks, p.2.val < b
  · have hnot : ¬ ∀ p ∈ (u.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm hu₁ hu₂).blocks,
        p.1.val < m :=
      fun hall ↦ (lt_irrefl m) (hall (⟨m, hm⟩, ⟨b, lt_of_le_of_lt hbm hm⟩) (by simp))
    rw [ballotForward, dite_eq_left ⟨hu₁, hu₂⟩, ballotBackward, ite_eq_right hnot]
    ext1
    simp
  · rw [ballotForward, dite_eq_right fun h ↦ hu₂ h.2, ballotBackward, ite_eq_left hu₁]

/-- If `w ∈ jonesWordsBounded n (m + 1) (b + 1)` has a block start `≥ m` and a block end `≥ b`,
strict monotonicity of both coordinates forces its last block to be `(m, b)`. -/
private theorem eq_snoc_of_mem_jonesWordsBounded {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {w : JonesWord n} (hw : w ∈ jonesWordsBounded n (m + 1) (b + 1))
    (hw₁ : ¬ ∀ p ∈ w.blocks, p.1.val < m) (hnot : ¬ ∀ p ∈ w.blocks, p.2.val < b) :
    ∃ (w₀ : JonesWord n) (hi : ∀ p ∈ w₀.blocks, p.1 < ⟨m, hm⟩)
      (hj : ∀ p ∈ w₀.blocks, p.2 < ⟨b, lt_of_le_of_lt hbm hm⟩),
      w = w₀.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm hi hj := by
  rw [mem_jonesWordsBounded] at hw
  induction w using JonesWord.snoc_induction_on with
  | empty => exact absurd (by simp) hw₁
  | snoc w₀ i j hji hi hj _ =>
    have him : i.val = m := by
      by_contra hne
      have hilt : i.val < m :=
        lt_of_le_of_ne (Nat.lt_succ_iff.1 (hw (i, j) (by simp)).1) hne
      exact hw₁ fun p hp ↦ by
        rcases List.mem_append.1 hp with hp | hp
        · exact Nat.lt_trans (hi p hp) hilt
        · obtain rfl := List.mem_singleton.1 hp; exact hilt
    have hjb : j.val = b := by
      by_contra hne
      have hjlt : j.val < b :=
        lt_of_le_of_ne (Nat.lt_succ_iff.1 (hw (i, j) (by simp)).2) hne
      exact hnot fun p hp ↦ by
        rcases List.mem_append.1 hp with hp | hp
        · exact Nat.lt_trans (hj p hp) hjlt
        · obtain rfl := List.mem_singleton.1 hp; exact hjlt
    have hi_eq : i = ⟨m, hm⟩ := Fin.ext him
    have hj_eq : j = ⟨b, lt_of_le_of_lt hbm hm⟩ := Fin.ext hjb
    subst hi_eq hj_eq
    exact ⟨w₀, hi, hj, rfl⟩

private theorem ballotForward_ballotBackward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {w : JonesWord n} (hw : w ∈ jonesWordsBounded n (m + 1) (b + 1))
    (hnot : ¬ ∀ p ∈ w.blocks, p.2.val < b) :
    ballotBackward m w ∈ jonesWordsBounded n m (b + 1) ∧
      ballotForward hm hbm (ballotBackward m w) = w := by
  by_cases hw₁ : ∀ p ∈ w.blocks, p.1.val < m
  · rw [mem_jonesWordsBounded] at hw
    have hmem : w ∈ jonesWordsBounded n m (b + 1) :=
      mem_jonesWordsBounded.2 fun p hp ↦ ⟨hw₁ p hp, (hw p hp).2⟩
    rw [ballotBackward, ite_eq_left hw₁]
    exact ⟨hmem, by rw [ballotForward, dite_eq_right fun h ↦ hnot h.2]⟩
  · obtain ⟨w₀, hi, hj, rfl⟩ := eq_snoc_of_mem_jonesWordsBounded hm hbm hw hw₁ hnot
    rw [ballotBackward, ite_eq_right hw₁, JonesWord.dropLast_snoc]
    exact ⟨mem_jonesWordsBounded.2 fun p hp ↦
      ⟨hi p hp, Nat.lt_trans (hj p hp) (Nat.lt_succ_self b)⟩,
      by rw [ballotForward, dite_eq_left ⟨hi, hj⟩]⟩

/-- The ballot recurrence on `jonesWordsBounded`. -/
private theorem card_jonesWordsBounded_succ_succ {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m) :
    #(jonesWordsBounded n (m + 1) (b + 1)) =
      #(jonesWordsBounded n (m + 1) b) + #(jonesWordsBounded n m (b + 1)) := by
  let S := jonesWordsBounded n (m + 1) (b + 1)
  let P : JonesWord n → Prop := fun w ↦ ∀ p ∈ w.blocks, p.2.val < b
  rw [← Finset.card_filter_add_card_filter_not P (s := S)]
  congr 1
  · congr 1
    ext w
    simp only [S, P, Finset.mem_filter, mem_jonesWordsBounded]
    exact ⟨fun ⟨h1, h2⟩ p hp ↦ ⟨(h1 p hp).1, h2 p hp⟩,
      fun h ↦ ⟨fun p hp ↦ ⟨(h p hp).1, (h p hp).2.trans (Nat.lt_succ_self b)⟩,
        fun p hp ↦ (h p hp).2⟩⟩
  · refine Finset.card_bij' (fun w _ ↦ ballotBackward m w) (fun u _ ↦ ballotForward hm hbm u)
      ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact (ballotForward_ballotBackward hm hbm hw.1 hw.2).1
    · intro u hu
      rw [Finset.mem_filter]
      rw [mem_jonesWordsBounded] at hu
      have hu₁ : ∀ p ∈ u.blocks, p.1.val < m := fun p hp ↦ (hu p hp).1
      dsimp only [ballotForward]
      split_ifs with h
      · refine ⟨mem_jonesWordsBounded.2 fun p hp ↦ ?_, fun hall ↦ ?_⟩
        · rcases List.mem_append.1 hp with hp | hp
          · exact ⟨(hu₁ p hp).trans (Nat.lt_succ_self m), (h.2 p hp).trans (Nat.lt_succ_self b)⟩
          · obtain rfl := List.mem_singleton.1 hp
            exact ⟨Nat.lt_succ_self m, Nat.lt_succ_self b⟩
        · exact (lt_irrefl b) (hall (⟨m, hm⟩, ⟨b, lt_of_le_of_lt hbm hm⟩) (by simp))
      · exact ⟨mem_jonesWordsBounded.2 fun p hp ↦
          ⟨(hu₁ p hp).trans (Nat.lt_succ_self m), (hu p hp).2⟩, fun hu₂ ↦ h ⟨hu₁, hu₂⟩⟩
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact (ballotForward_ballotBackward hm hbm hw.1 hw.2).2
    · intro u hu
      exact ballotBackward_ballotForward hm hbm hu

/-- Closed count of `jonesWordsBounded n m b` in terms of `TauCeti.halfCount`. -/
private theorem card_jonesWordsBounded_eq_halfCount {n m b : ℕ} (hm : m ≤ n - 1)
    (hbm : b ≤ m + 1) :
    #(jonesWordsBounded n m b) = halfCount (m + 1 + b) (m + 1 - b) := by
  induction m generalizing b with
  | zero =>
    rw [jonesWordsBounded_zero_left, Finset.card_singleton]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbm with rfl | rfl
    · simp [halfCount_self]
    · simpa using (halfCount_two_mul_zero 1).symm
  | succ m ihm =>
    induction b with
    | zero =>
      rw [jonesWordsBounded_zero_right, Finset.card_singleton]
      simp [halfCount_self]
    | succ b ihb =>
      rcases le_or_gt b m with hbm' | hmb
      · rw [card_jonesWordsBounded_succ_succ (by omega) hbm', ihb (by omega),
          ihm (by omega) (Nat.succ_le_succ hbm'), add_comm]
        convert (halfCount_succ_succ (m + b + 2) (m - b)).symm using 2 <;>
          first | omega | (congr 1 <;> omega)
      · have hbeq : b = m + 1 := by omega
        subst hbeq
        rw [jonesWordsBounded_eq_self_of_le (Nat.le_succ (m + 1)), ihb (Nat.le_succ (m + 1))]
        convert (halfCount_succ_zero (2 * m + 3)).symm using 2 <;> omega

/-- **The Catalan count of Jones reduced words.** On `n` strands there are `catalan n` Jones
reduced words. -/
@[simp]
theorem card_jonesWord (n : ℕ) : Fintype.card (JonesWord n) = catalan n := by
  rw [← Finset.card_univ, ← jonesWordsBounded_top n]
  cases n with
  | zero =>
    rw [Nat.zero_sub, jonesWordsBounded_zero_left, Finset.card_singleton, catalan_zero]
  | succ k =>
    rw [Nat.succ_sub_one,
      card_jonesWordsBounded_eq_halfCount (n := k + 1) (m := k) (b := k) le_rfl (Nat.le_succ k),
      ← halfCount_two_mul_zero]
    convert (halfCount_succ_zero (2 * k + 1)).symm using 2 <;> omega

end CatalanCount

/-! ### Module finiteness, rank bounds, and bases -/

section Dimension

variable {R : Type*} [CommSemiring R]

/-- Over any commutative semiring `R`, the Temperley–Lieb algebra `TemperleyLieb R δ n` is finitely
generated as an `R`-module. In particular, over any field it is finite-dimensional, and so is every
quotient of it by an `R`-submodule (including any left, right, or two-sided ideal). -/
instance (δ : R) (n : ℕ) : Module.Finite R (TemperleyLieb R δ n) := by
  have : Module.Finite R (JonesWord n →₀ R) := Module.Finite.of_basis Finsupp.basisSingleOne
  refine Module.Finite.of_surjective (Finsupp.linearCombination R (JonesWord.eval δ)) ?_
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, span_range_jonesWord_eval]

/-- Under any surjective `R`-linear map out of `TemperleyLieb R δ n`, the images of the
reduced-word evaluations span the target module. -/
theorem span_range_comp_jonesWord_eval_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Submodule.span R (Set.range (f ∘ JonesWord.eval δ)) = ⊤ := by
  rw [Set.range_comp, ← Submodule.map_span, span_range_jonesWord_eval, Submodule.map_top,
    LinearMap.range_eq_top.2 hf]

/-- Any `R`-module admitting a surjective `R`-linear map from `TemperleyLieb R δ n` has `R`-rank
at most `(catalan n : Cardinal)`. -/
theorem rank_le_catalan_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Module.rank R M ≤ catalan n := by
  by_cases hR : Nontrivial R
  · rw [← (Submodule.topEquiv (R := R) (M := M)).rank_eq,
      ← span_range_comp_jonesWord_eval_of_surjective f hf]
    refine (rank_span_le _).trans ?_
    simpa [card_jonesWord] using Cardinal.mk_range_le_lift (f := f ∘ JonesWord.eval δ)
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.1 hR
    rw [rank_subsingleton, ← card_jonesWord n]
    exact_mod_cast Nat.succ_le_of_lt Fintype.card_pos

/-- **Catalan rank bound.** Over any commutative semiring `R`, the `R`-rank of
`TemperleyLieb R δ n` is at most `(catalan n : Cardinal)`. -/
theorem rank_le_catalan (δ : R) (n : ℕ) :
    Module.rank R (TemperleyLieb R δ n) ≤ catalan n :=
  rank_le_catalan_of_surjective LinearMap.id Function.surjective_id

/-- Any `R`-module admitting a surjective `R`-linear map from `TemperleyLieb R δ n` has `finrank`
at most `catalan n`. When `R` is a commutative ring, this applies in particular to every quotient of
`TemperleyLieb R δ n` by an `R`-submodule (including any left, right, or two-sided ideal). -/
theorem finrank_le_catalan_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Module.finrank R M ≤ catalan n :=
  Module.finrank_le_of_rank_le (rank_le_catalan_of_surjective f hf)

/-- **Catalan `finrank` bound.** Over any commutative semiring `R`, the `finrank` of
`TemperleyLieb R δ n` is at most `catalan n`. -/
theorem finrank_le_catalan (δ : R) (n : ℕ) :
    Module.finrank R (TemperleyLieb R δ n) ≤ catalan n :=
  finrank_le_catalan_of_surjective LinearMap.id Function.surjective_id

/-- Any quotient of `TemperleyLieb S δ n` by an `S`-submodule (in particular by any left, right, or
two-sided ideal) has `S`-rank at most `(catalan n : Cardinal)`. -/
theorem rank_quotient_le_catalan {S : Type*} [CommRing S] {δ : S} {n : ℕ}
    (p : Submodule S (TemperleyLieb S δ n)) :
    Module.rank S (TemperleyLieb S δ n ⧸ p) ≤ catalan n :=
  rank_le_catalan_of_surjective p.mkQ p.mkQ_surjective

/-- Any quotient of `TemperleyLieb S δ n` by an `S`-submodule (in particular by any left, right, or
two-sided ideal) has `finrank` at most `catalan n`. -/
theorem finrank_quotient_le_catalan {S : Type*} [CommRing S] {δ : S} {n : ℕ}
    (p : Submodule S (TemperleyLieb S δ n)) :
    Module.finrank S (TemperleyLieb S δ n ⧸ p) ≤ catalan n :=
  finrank_le_catalan_of_surjective p.mkQ p.mkQ_surjective

section Orzech

variable [OrzechProperty R] {M : Type*} [AddCommMonoid M] [Module R M] {δ : R} {n : ℕ}

private theorem linearIndependent_rangeRestrict_of_catalan_le_finrank_range
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    LinearIndependent R (f.rangeRestrict ∘ JonesWord.eval (R := R) δ (n := n)) :=
  linearIndependent_of_top_le_span_of_card_le_finrank
    (span_range_comp_jonesWord_eval_of_surjective f.rangeRestrict f.surjective_rangeRestrict).ge
    ((card_jonesWord n).trans_le hf)

/-- Over a commutative semiring satisfying the Orzech property (in particular over any commutative
ring or field), if a linear map `f : TemperleyLieb R δ n →ₗ[R] M` has range of `finrank` at least
`catalan n`, then the evaluations `JonesWord.eval δ` are `R`-linearly independent. -/
theorem linearIndependent_jonesWord_eval_of_catalan_le_finrank_range
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    LinearIndependent R (JonesWord.eval (R := R) δ (n := n)) :=
  (linearIndependent_rangeRestrict_of_catalan_le_finrank_range f hf).of_comp f.rangeRestrict

/-- Free `R`-basis of `TemperleyLieb R δ n` indexed by `JonesWord n`, obtained whenever some
`R`-linear map out of `TemperleyLieb R δ n` has range of `finrank` at least `catalan n`. -/
noncomputable def basisJonesWordOfCatalanLeFinrankRange
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    Module.Basis (JonesWord n) R (TemperleyLieb R δ n) :=
  Module.Basis.mk (linearIndependent_jonesWord_eval_of_catalan_le_finrank_range f hf)
    (span_range_jonesWord_eval δ n).ge

/-- Basis vector of `basisJonesWordOfCatalanLeFinrankRange` at `w` is `w.eval δ`. -/
@[simp]
theorem basisJonesWordOfCatalanLeFinrankRange_apply
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f))
    (w : JonesWord n) :
    basisJonesWordOfCatalanLeFinrankRange f hf w = w.eval δ :=
  Module.Basis.mk_apply _ _ w

/-- **Representation faithfulness criterion.** Over a commutative semiring with the Orzech property
(including every commutative ring and field), any `R`-linear map out of `TemperleyLieb R δ n` whose
range has `finrank` at least `catalan n` is injective. -/
theorem injective_of_catalan_le_finrank_range
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    Function.Injective f := by
  let B := basisJonesWordOfCatalanLeFinrankRange f hf
  have h : B.constr ℕ (f.rangeRestrict ∘ JonesWord.eval δ) = f.rangeRestrict :=
    B.constr_eq ℕ fun w ↦ by simp [B]
  exact f.injective_rangeRestrict_iff.1 <|
    h ▸ B.injective_constr_of_linearIndependent (R₂ := ℕ)
      (linearIndependent_rangeRestrict_of_catalan_le_finrank_range f hf)

/-- When an `R`-linear map out of `TemperleyLieb R δ n` has range of `finrank` at least
`catalan n`, the `finrank` of `TemperleyLieb R δ n` equals `catalan n`. -/
theorem finrank_eq_catalan_of_catalan_le_finrank_range
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    Module.finrank R (TemperleyLieb R δ n) = catalan n :=
  le_antisymm (finrank_le_catalan δ n)
    (hf.trans_eq (LinearEquiv.ofInjective f
      (injective_of_catalan_le_finrank_range f hf)).symm.finrank_eq)

end Orzech

section SmallCases

/-- On two strands, `![1, e δ 0]` is a free `R`-basis of `TemperleyLieb R δ 2` over every
commutative semiring `R`. -/
noncomputable def basisTwo (δ : R) : Module.Basis (Fin 2) R (TemperleyLieb R δ 2) :=
  Module.Basis.mk (linearIndependent_two δ) <| by
    rw [← span_range_jonesWord_eval (R := R) δ 2]
    refine Submodule.span_mono ?_
    rintro _ ⟨⟨blocks, -, hfst, -⟩, rfl⟩
    rcases blocks with _ | ⟨⟨i, j⟩, _ | ⟨⟨i', j'⟩, _⟩⟩
    · exact ⟨0, by simp [JonesWord.eval_def]⟩
    · fin_cases i
      fin_cases j
      exact ⟨1, by simp [JonesWord.eval_def]⟩
    · exfalso
      have hlt : i < i' := (List.pairwise_cons.1 hfst).1 (i', j') List.mem_cons_self
      omega

/-- The `0`-th vector of `basisTwo` is `1`. -/
@[simp]
theorem basisTwo_zero (δ : R) : basisTwo (R := R) δ 0 = 1 := by
  simp [basisTwo]

/-- The `1`-st vector of `basisTwo` is `e δ 0`. -/
@[simp]
theorem basisTwo_one (δ : R) : basisTwo (R := R) δ 1 = e δ 0 := by
  simp [basisTwo]

/-- On two strands over a nontrivial commutative semiring `R`, `TemperleyLieb R δ 2` has `finrank`
equal to `2 = catalan 2`. Nontriviality is required because `Module.finrank_subsingleton` equals
`1` over a trivial semiring. -/
theorem finrank_two [Nontrivial R] (δ : R) :
    Module.finrank R (TemperleyLieb R δ 2) = 2 := by
  rw [Module.finrank_eq_card_basis (basisTwo δ), Fintype.card_fin]

end SmallCases

end Dimension

end TauCeti.TemperleyLieb
