/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.Algebra.TemperleyLieb.Basic
import Mathlib.Data.List.Intervals

/-!
# Jones normal form for Temperley–Lieb algebras

Every element of the Temperley–Lieb algebra `TemperleyLieb R δ n` over a commutative semiring `R`
is an `R`-linear combination of **Jones reduced words**: products
`(e i₁ * e (i₁ - 1) * ⋯ * e j₁) * ⋯ * (e iᵣ * e (iᵣ - 1) * ⋯ * e jᵣ)`
of decreasing generator blocks whose starting indices `i₁ < ⋯ < iᵣ` and ending indices
`j₁ < ⋯ < jᵣ` are both strictly increasing, with `jₛ ≤ iₛ` in every block.

This file develops decreasing generator blocks (`descBlockList`, `descBlock`) and Jones reduced
words (`JonesWord`) directly from the three defining relations of `TemperleyLieb R δ n` — without
diagram bases, cell modules, or Gram determinants — and proves that every product of generators
reduces to a scalar multiple of a reduced word of no greater length, so the reduced words span
`TemperleyLieb R δ n` as an `R`-module. Catalan enumeration of `JonesWord n`, module finiteness,
the Catalan rank/`finrank` upper bounds, and the Orzech faithfulness criterion are developed on top
of this file in `TauCeti.Algebra.TemperleyLieb.Dimension`.

## Main definitions

* `TauCeti.TemperleyLieb.descBlockList`: the decreasing list of indices from `i` to `j` in `Fin m`.
* `TauCeti.TemperleyLieb.descBlock`: the decreasing generator product `e δ i * ⋯ * e δ j`.
* `TauCeti.TemperleyLieb.JonesWord`: Jones reduced words on `n` strands.
* `TauCeti.TemperleyLieb.JonesWord.eval`: evaluation of a reduced word in `TemperleyLieb R δ n`.
* `TauCeti.TemperleyLieb.JonesWord.wordLength`: total number of generators in a reduced word.
* `TauCeti.TemperleyLieb.JonesWord.castSucc`: inclusion of reduced words along `strandIncl`.
* `TauCeti.TemperleyLieb.JonesWord.equivFinsetPair`: equivalence between `JonesWord n` and pairs of
  equal-sized subsets of `Fin (n - 1)` satisfying `jₛ ≤ iₛ` on sorted elements.

## Main results

* `TauCeti.TemperleyLieb.exists_prod_map_e_eq_pow_smul_eval`: every generator product reduces to
  `δ ^ m • w.eval δ` with `w.wordLength ≤ l.length`.
* `TauCeti.TemperleyLieb.span_range_jonesWord_eval`: reduced words span `TemperleyLieb R δ n`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Exercises 4.1.2–4.1.3.
-/

public section

namespace TauCeti.TemperleyLieb

section DescBlock

section List

variable {m : ℕ}

/-- The decreasing list of indices `[i, i - 1, …, j]` in `Fin m`, which is empty when `i < j`. -/
def descBlockList (i j : Fin m) : List (Fin m) :=
  (List.Ico j.val (i.val + 1)).reverse.pmap Fin.mk fun _ hm ↦
    (List.Ico.mem.1 (List.mem_reverse.1 hm)).2.trans_le i.isLt

/-- A single-index decreasing block list consists of that index alone. -/
@[simp]
theorem descBlockList_self (i : Fin m) : descBlockList i i = [i] := by
  simp [descBlockList]

/-- When `i < j`, the decreasing block list from `i` down to `j` is empty. -/
theorem descBlockList_of_lt {i j : Fin m} (h : i < j) : descBlockList i j = [] := by
  simp [descBlockList, List.Ico.eq_nil_of_le (show i.val + 1 ≤ j.val by omega)]

/-- Length of `descBlockList i j`. -/
@[simp]
theorem length_descBlockList (i j : Fin m) :
    (descBlockList i j).length = i.val + 1 - j.val := by
  simp [descBlockList]

/-- `descBlockList i j` is empty if and only if `i < j`. -/
@[simp]
theorem descBlockList_eq_nil_iff {i j : Fin m} : descBlockList i j = [] ↔ i < j := by
  rw [← List.length_eq_zero_iff, length_descBlockList]
  omega

/-- Membership in `descBlockList i j`: the indices `x` with `j ≤ x ≤ i`. -/
@[simp]
theorem mem_descBlockList {i j x : Fin m} :
    x ∈ descBlockList i j ↔ j ≤ x ∧ x ≤ i := by
  simp only [descBlockList, List.mem_pmap, List.mem_reverse, List.Ico.mem]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1, Nat.lt_succ_iff.1 ha.2⟩
  · intro hx
    exact ⟨x.val, ⟨hx.1, Nat.lt_succ_iff.2 hx.2⟩, Fin.ext rfl⟩

/-- Concatenating adjacent decreasing block lists merges them into one block list. -/
theorem descBlockList_append_descBlockList_of_succ_eq {i a b j : Fin m}
    (hbi : b ≤ i) (hab : b.val + 1 = a.val) (hja : j ≤ a) :
    descBlockList i a ++ descBlockList b j = descBlockList i j := by
  apply List.map_injective_iff.2 Fin.val_injective
  have h : List.Ico j.val (i.val + 1) =
      List.Ico j.val (b.val + 1) ++ List.Ico a.val (i.val + 1) := by
    rw [← hab, List.Ico.append_consecutive (by omega) (by omega)]
  simp [descBlockList, List.map_pmap, h]

/-- Extending a nonempty decreasing block list on the left by the successor of `i`. -/
theorem cons_descBlockList_of_succ_eq {k i j : Fin m} (hji : j ≤ i) (hik : i.val + 1 = k.val) :
    k :: descBlockList i j = descBlockList k j := by
  simpa using descBlockList_append_descBlockList_of_succ_eq (i := k) (j := j) (hab := hik)
    (Fin.le_def.2 (by omega)) (Fin.le_def.2 (by omega))

/-- Extending a nonempty decreasing block list on the right by the predecessor of `j`. -/
theorem descBlockList_append_singleton_of_succ_eq {i j k : Fin m} (hji : j ≤ i)
    (hkj : k.val + 1 = j.val) :
    descBlockList i j ++ [k] = descBlockList i k := by
  simpa using descBlockList_append_descBlockList_of_succ_eq (i := i) (j := k) (hab := hkj)
    (Fin.le_def.2 (by omega)) (Fin.le_def.2 (by omega))

/-- The last index of a nonempty decreasing block list `descBlockList i j` (`j ≤ i`) is `j`. -/
@[simp]
theorem getLast_descBlockList {i j : Fin m} (h : descBlockList i j ≠ []) :
    (descBlockList i j).getLast h = j := by
  have hji : j ≤ i := not_lt.1 (descBlockList_eq_nil_iff.not.1 h)
  rcases eq_or_lt_of_le hji with rfl | hlt
  · simp
  · let jp1 : Fin m := ⟨j.val + 1, by omega⟩
    have hsplit : descBlockList i jp1 ++ [j] = descBlockList i j :=
      descBlockList_append_singleton_of_succ_eq (Nat.succ_le_of_lt hlt) rfl
    simp [← hsplit]

/-- Mapping `descBlockList` along `Fin.castSucc` produces `descBlockList` on `Fin (m + 1)`. -/
@[simp]
theorem map_castSucc_descBlockList (i j : Fin m) :
    (descBlockList i j).map Fin.castSucc = descBlockList i.castSucc j.castSucc := by
  simp only [descBlockList, List.map_pmap, Fin.val_castSucc]
  exact List.pmap_congr_left _ fun _ _ _ _ ↦ rfl

end List

variable {R : Type*} [CommSemiring R] {n : ℕ}

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
  rw [descBlock_def, descBlock_def, ← cons_descBlockList_of_succ_eq hji hik, List.map_cons,
    List.prod_cons]

/-- Right multiplication by `e δ k` extends `descBlock δ i j` when `j ≤ i` and `k + 1 = j`. -/
theorem descBlock_mul_e_of_succ_eq (δ : R) {i j k : Fin (n - 1)} (hji : j ≤ i)
    (hkj : k.val + 1 = j.val) :
    descBlock δ i j * e δ k = descBlock δ i k := by
  rw [descBlock_def, descBlock_def, ← descBlockList_append_singleton_of_succ_eq hji hkj,
    List.map_append, List.prod_append]
  simp

/-- A generator `e δ k` commutes with `descBlock δ i j` when `k` is at distance at least `2` from
every index in `[j, i]`. -/
theorem commute_descBlock_e (δ : R) {i j k : Fin (n - 1)}
    (h : k.val + 2 ≤ j.val ∨ i.val + 2 ≤ k.val) :
    Commute (descBlock δ i j) (e δ k) := by
  refine Commute.list_prod_left _ _ fun x hx ↦ ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  rw [mem_descBlockList] at hr
  exact commute_e (by omega)

private theorem descBlock_eq_prod_dropLast_mul_e (δ : R) {i j : Fin (n - 1)} (hji : j ≤ i) :
    descBlock δ i j = (((descBlockList i j).dropLast).map (e δ)).prod * e δ j := by
  have hne : descBlockList i j ≠ [] := by simp [not_lt.2 hji]
  rw [descBlock_def, ← List.dropLast_append_getLast hne, getLast_descBlockList hne]
  simp

/-- Right multiplication of `descBlock δ i j` (`j ≤ i`) by its bottom generator `e δ j` absorbs via
`e j * e j = δ • e j`. -/
theorem descBlock_mul_e_self (δ : R) {i j : Fin (n - 1)} (hji : j ≤ i) :
    descBlock δ i j * e δ j = δ • descBlock δ i j := by
  rw [descBlock_eq_prod_dropLast_mul_e δ hji, mul_assoc, e_mul_self, mul_smul_comm]

/-- The augmentation kills every nonempty decreasing generator block (`j ≤ i`). -/
@[simp]
theorem aug_descBlock_of_le (δ : R) {i j : Fin (n - 1)} (hji : j ≤ i) :
    aug (descBlock δ i j) = 0 := by
  rw [descBlock_eq_prod_dropLast_mul_e δ hji]
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
  let km1 : Fin (n - 1) := ⟨k.val - 1, by omega⟩
  have hkm1 : km1.val + 1 = k.val := by simp [km1]; omega
  have hstraight : descBlock (R := R) δ i k * e δ km1 * e δ k = descBlock δ i k := by
    rw [descBlock_eq_prod_dropLast_mul_e δ hki]
    simp only [mul_assoc]
    rw [← mul_assoc (e δ k), e_mul_e_mul_e (Or.inr hkm1)]
  rcases eq_or_lt_of_le (show j ≤ km1 from Nat.le_sub_one_of_lt hjk) with heq | hlt
  · refine ⟨descBlockList i k, ?_, ?_⟩
    · rw [heq, length_descBlockList, length_descBlockList]; simp [km1]; omega
    · rw [heq, ← descBlock_def, ← descBlock_mul_e_of_succ_eq δ hki hkm1, hstraight]
  · let km2 : Fin (n - 1) := ⟨k.val - 2, by omega⟩
    have hkm2 : km2.val + 1 = km1.val := by simp [km2, km1]; omega
    refine ⟨descBlockList i k ++ descBlockList km2 j, ?_, ?_⟩
    · rw [List.length_append, length_descBlockList, length_descBlockList, length_descBlockList]
      simp [km2]; omega
    · have hblock : descBlock δ i j = descBlock δ i k * e δ km1 * descBlock δ km2 j := by
        have hsplit : descBlockList i j =
            descBlockList i k ++ [km1] ++ descBlockList km2 j := by
          rw [descBlockList_append_singleton_of_succ_eq hki hkm1,
            descBlockList_append_descBlockList_of_succ_eq (Fin.le_def.2 (by simp [km2]; omega))
              hkm2 hlt.le]
        simp [descBlock_def, hsplit, mul_assoc]
      have hcomm := (commute_descBlock_e (R := R) δ (i := km2) (j := j) (k := k)
        (Or.inr (by simp [km2]; omega))).eq
      rw [List.map_append, List.prod_append, ← descBlock_def, ← descBlock_def, hblock,
        mul_assoc, hcomm, ← mul_assoc, hstraight]

/-- Boundary zigzag absorption across two consecutive blocks: when the first block ends at `k` and
the second ends at `j₂ = k + 1`, right multiplication by `e δ k` commutes the first block's bottom
`e δ k` across `e i₂ * ⋯ * e (k + 2)` and straightens `e k * e (k + 1) * e k = e k`, dropping two
generators. -/
private theorem exists_list_descBlock_mul_descBlock_mul_e (δ : R) {i₁ i₂ j₂ k : Fin (n - 1)}
    (hk₁ : k ≤ i₁) (hkj : k.val + 1 = j₂.val) (hj₂ : j₂ ≤ i₂) :
    ∃ t : List (Fin (n - 1)),
      t.length + 1 ≤ (descBlockList i₁ k).length + (descBlockList i₂ j₂).length ∧
        (t.map (e δ)).prod = descBlock δ i₁ k * descBlock δ i₂ j₂ * e δ k := by
  refine ⟨(descBlockList i₁ k).dropLast ++ (descBlockList i₂ j₂).dropLast ++ [k], ?_, ?_⟩
  · rw [List.length_append, List.length_append, List.length_singleton, List.length_dropLast,
      List.length_dropLast, length_descBlockList, length_descBlockList]
    omega
  · have hcomm : Commute (((descBlockList i₂ j₂).dropLast.map (e δ)).prod) (e δ k) := by
      rcases eq_or_lt_of_le hj₂ with rfl | hlt
      · simp
      · let j₂' : Fin (n - 1) := ⟨j₂.val + 1, by omega⟩
        have hdl : (descBlockList i₂ j₂).dropLast = descBlockList i₂ j₂' := by
          rw [← descBlockList_append_singleton_of_succ_eq (i := i₂) (j := j₂') (k := j₂)
            (Nat.succ_le_of_lt hlt) rfl, List.dropLast_concat]
        rw [hdl]
        exact commute_descBlock_e δ (Or.inl (by simp [j₂']; omega))
    have hadj : e (R := R) δ k * e δ j₂ * e δ k = e δ k :=
      e_mul_e_mul_e (Or.inl hkj)
    let P₁ := (((descBlockList i₁ k).dropLast).map (e δ)).prod
    let P₂ := (((descBlockList i₂ j₂).dropLast).map (e δ)).prod
    rw [descBlock_eq_prod_dropLast_mul_e δ hk₁, descBlock_eq_prod_dropLast_mul_e δ hj₂]
    simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    calc P₁ * P₂ * e δ k
        = P₁ * P₂ * (e δ k * e δ j₂ * e δ k) := by rw [hadj]
      _ = P₁ * (P₂ * e δ k) * (e δ j₂ * e δ k) := by simp only [mul_assoc]
      _ = P₁ * (e δ k * P₂) * (e δ j₂ * e δ k) := by rw [hcomm.eq]
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

/-- The default Jones reduced word is `empty`. -/
@[simp]
theorem default_eq_empty : (default : JonesWord n) = empty := (rfl)

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

/-- Every block in `w.snoc i j …` has starting index at most `i`. -/
theorem fst_le_of_mem_blocks_snoc {w : JonesWord n} {i j : Fin (n - 1)} {hji : j ≤ i}
    {hi : ∀ p ∈ w.blocks, p.1 < i} {hj : ∀ p ∈ w.blocks, p.2 < j}
    {p : Fin (n - 1) × Fin (n - 1)} (hp : p ∈ (w.snoc i j hji hi hj).blocks) :
    p.1 ≤ i := by
  rcases List.mem_append.1 hp with hp | hp
  · exact (hi p hp).le
  · obtain rfl := List.mem_singleton.1 hp
    exact le_rfl

/-- Every block in `w.snoc i j …` has ending index at most `j`. -/
theorem snd_le_of_mem_blocks_snoc {w : JonesWord n} {i j : Fin (n - 1)} {hji : j ≤ i}
    {hi : ∀ p ∈ w.blocks, p.1 < i} {hj : ∀ p ∈ w.blocks, p.2 < j}
    {p : Fin (n - 1) × Fin (n - 1)} (hp : p ∈ (w.snoc i j hji hi hj).blocks) :
    p.2 ≤ j := by
  rcases List.mem_append.1 hp with hp | hp
  · exact (hj p hp).le
  · obtain rfl := List.mem_singleton.1 hp
    exact le_rfl

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
    ext1
    exact List.map_injective_iff.2
      ((Fin.castSucc_injective m).prodMap (Fin.castSucc_injective m)) (congrArg blocks h)

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

/-- Zipping the sorted starting and ending finsets of a Jones reduced word recovers `w.blocks`. -/
theorem zip_sort_startFinset_endFinset (w : JonesWord n) :
    List.zip (w.startFinset.sort (· ≤ ·)) (w.endFinset.sort (· ≤ ·)) = w.blocks := by
  rw [w.sort_startFinset, w.sort_endFinset, ← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]

/-- Equivalence between `JonesWord n` and pairs `(I, J)` of equal-sized subsets of `Fin (n - 1)`
whose sorted elements satisfy `jₛ ≤ iₛ` in each position. -/
def equivFinsetPair :
    JonesWord n ≃
      {s : Finset (Fin (n - 1)) × Finset (Fin (n - 1)) //
        s.1.card = s.2.card ∧
          ∀ p ∈ List.zip (s.1.sort (· ≤ ·)) (s.2.sort (· ≤ ·)), p.2 ≤ p.1} where
  toFun w := ⟨(w.startFinset, w.endFinset), by
    rw [w.card_startFinset, w.card_endFinset]
    exact ⟨rfl, w.zip_sort_startFinset_endFinset.symm ▸ w.snd_le_fst⟩⟩
  invFun s :=
    { blocks := List.zip (s.val.1.sort (· ≤ ·)) (s.val.2.sort (· ≤ ·))
      snd_le_fst := s.property.2
      pairwise_fst_lt := by
        have hlen : (s.val.1.sort (· ≤ ·)).length = (s.val.2.sort (· ≤ ·)).length
            := by simp [s.property.1]
        rw [← List.pairwise_map, List.map_fst_zip (le_of_eq hlen)]
        exact s.val.1.sortedLT_sort.pairwise
      pairwise_snd_lt := by
        have hlen : (s.val.1.sort (· ≤ ·)).length = (s.val.2.sort (· ≤ ·)).length
            := by simp [s.property.1]
        rw [← List.pairwise_map, List.map_snd_zip (ge_of_eq hlen)]
        exact s.val.2.sortedLT_sort.pairwise }
  left_inv w := by
    ext1
    exact w.zip_sort_startFinset_endFinset
  right_inv s := by
    have hlen : (s.val.1.sort (· ≤ ·)).length = (s.val.2.sort (· ≤ ·)).length
        := by simp [s.property.1]
    ext x <;>
      simp [startFinset_def, endFinset_def, List.map_fst_zip (le_of_eq hlen),
        List.map_snd_zip (ge_of_eq hlen)]

/-- Underlying subset pair of `equivFinsetPair w`. -/
@[simp]
theorem val_equivFinsetPair (w : JonesWord n) :
    (equivFinsetPair w).val = (w.startFinset, w.endFinset) := (rfl)

/-- Blocks of `equivFinsetPair.symm s`. -/
@[simp]
theorem blocks_equivFinsetPair_symm
    (s : {s : Finset (Fin (n - 1)) × Finset (Fin (n - 1)) //
      s.1.card = s.2.card ∧
        ∀ p ∈ List.zip (s.1.sort (· ≤ ·)) (s.2.sort (· ≤ ·)), p.2 ≤ p.1}) :
    (equivFinsetPair.symm s).blocks = List.zip (s.val.1.sort (· ≤ ·)) (s.val.2.sort (· ≤ ·)) :=
        (rfl)

instance : Fintype (JonesWord n) :=
  Fintype.ofEquiv _ equivFinsetPair.symm

/-- On at most one strand there are no generators, so every Jones reduced word is `empty`. -/
theorem eq_empty_of_le_one (hn : n ≤ 1) (w : JonesWord n) : w = empty := by
  ext1
  cases h : w.blocks with
  | nil => rfl
  | cons p _ => exact absurd p.1.isLt (by omega)

/-- On at most one strand there are no generators, so `empty` is the unique Jones reduced word. -/
@[expose, instance_reducible]
def uniqueOfLeOne (hn : n ≤ 1) : Unique (JonesWord n) where
  uniq := eq_empty_of_le_one hn

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
    (hsucc : k.val + 1 = j.val) :
    StepRightOutcome δ (w₀.snoc i j hji hi hj) k := by
  have hki : k ≤ i := Fin.le_def.2 (by omega)
  by_cases hj' : ∀ p ∈ w₀.blocks, p.2 < k
  · -- All earlier blocks end strictly below `k`: extend `(i, j)` to `(i, k)`.
    refine Or.inl ⟨w₀.snoc i k hki hi hj', ?_, ?_, ?_⟩
    · simp only [JonesWord.wordLength_snoc]
      omega
    · simp [mul_assoc, descBlock_mul_e_of_succ_eq δ hji hsucc]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact Or.inl ⟨q, List.mem_append_left _ hq, rfl, Or.inl rfl⟩
      · obtain rfl := List.mem_singleton.1 hq
        exact Or.inl ⟨(i, j), List.mem_append_right _ (List.mem_singleton_self _),
          rfl, Or.inr rfl⟩
  · -- Otherwise the last block of `w₀` must end at `k`: boundary zigzag across `(i₁, k)` and
    -- `(i, j)`.
    induction w₀ using JonesWord.snoc_induction_on with
    | empty => exact absurd (by simp) hj'
    | snoc w₁ i₁ j₁ hj₁i₁ hi₁ hj₁ _ =>
      have hj₁j : j₁.val < j.val :=
        hj (i₁, j₁) (List.mem_append_right _ (List.mem_singleton_self _))
      have hj₁k : j₁ ≤ k := Fin.le_def.2 (by omega)
      rcases lt_or_eq_of_le hj₁k with hj₁_lt | rfl
      · exact absurd (fun _ hp ↦ lt_of_le_of_lt (JonesWord.snd_le_of_mem_blocks_snoc hp) hj₁_lt) hj'
      · obtain ⟨t, hlen, hprod⟩ := exists_list_descBlock_mul_descBlock_mul_e δ hj₁i₁ hsucc hji
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
      have hi' : ∀ p ∈ (w₀.snoc i j hji hi hj).blocks, p.1 < k :=
        fun _ hp ↦ lt_of_le_of_lt (JonesWord.fst_le_of_mem_blocks_snoc hp) hik
      have hj' : ∀ p ∈ (w₀.snoc i j hji hi hj).blocks, p.2 < k :=
        fun _ hp ↦ lt_of_le_of_lt (JonesWord.snd_le_of_mem_blocks_snoc hp) hjk
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
          · exact stepRight_adj δ w₀ i j k hji hi hj hsucc
          · exact stepRight_comm δ w₀ i j k hji hi hj (by omega) ih

/-- **Jones word reduction.** Every product of generators `(l.map (e δ)).prod` in
`TemperleyLieb R δ n` reduces to `δ ^ m • w.eval δ` for some `m : ℕ` and some Jones reduced word
`w` of word length at most `l.length`. -/
theorem exists_prod_map_e_eq_pow_smul_eval (δ : R) (l : List (Fin (n - 1))) :
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
  obtain ⟨m, w, -, hw⟩ := exists_prod_map_e_eq_pow_smul_eval δ l
  rw [hw]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

end NormalForm

end TauCeti.TemperleyLieb
