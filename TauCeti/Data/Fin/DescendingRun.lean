/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Chain
import Mathlib.Order.Fin.Basic

/-!
# Descending step-one runs in `Fin m` and maximal run factorization

For `i, j : Fin m`, `Fin.descendingRun i j` lists the indices `[i, i - 1, …, j]` descending by one
at each step (and is empty when `i < j`). Every word `l : List (Fin m)` factors uniquely as a
concatenation of nonempty descending runs `(i₁, j₁), …, (iₚ, jₚ)` whose adjacent runs cannot be
merged into a longer step-one run, meaning `(iₖ₊₁ : ℕ) + 1 ≠ jₖ`. `Fin.parseRuns l` computes this
canonical maximal descending-run factorization, and `Fin.parseRuns_eq_iff` characterizes it by
validity (`jₖ ≤ iₖ`), maximality (`List.IsChain`), and concatenation (`List.flatMap`).

This run factorization underlies normal-form arguments for words in indexed generators (such as
Jones normal form in Temperley–Lieb and Hecke algebras), where generator words are grouped into
maximal descending runs before comparing endpoints of adjacent runs.

## Main definitions and results

* `Fin.descendingRun`: the descending step-one run `[i, i - 1, …, j]` in `Fin m`.
* `Fin.mem_descendingRun`, `Fin.descendingRun_split`, `Fin.descendingRun_cons`,
  `Fin.descendingRun_concat`: membership and endpoint-splitting lemmas for `Fin.descendingRun`.
* `Fin.parseRuns`: decomposition of `l : List (Fin m)` into maximal descending-by-one runs.
* `Fin.lower_le_upper_parseRuns`, `Fin.flatMap_parseRuns`, `Fin.isChain_parseRuns`: every run
  returned by `Fin.parseRuns` is nonempty (`r.2 ≤ r.1`), their concatenation recovers `l`, and
  adjacent runs satisfy `(r₂.1 : ℕ) + 1 ≠ r₁.2`.
* `Fin.parseRuns_eq_iff`: uniqueness characterization of the maximal descending-run factorization.
-/

public section

namespace Fin

variable {m : ℕ}

/-- The descending run `[i, i - 1, …, j]` in `Fin m`, with `i.val + 1 - j.val` entries (nonempty
when `j ≤ i`, and `[]` when `i < j`). -/
def descendingRun (i j : Fin m) : List (Fin m) :=
  (List.range (i.val + 1 - j.val)).map fun k ↦
    ⟨i.val - k, (Nat.sub_le i.val k).trans_lt i.isLt⟩

/-- Explicit `List.range` formula for `Fin.descendingRun`. -/
theorem descendingRun_def (i j : Fin m) :
    descendingRun i j =
      (List.range (i.val + 1 - j.val)).map fun k ↦
        ⟨i.val - k, (Nat.sub_le i.val k).trans_lt i.isLt⟩ := (rfl)

/-- The length of `Fin.descendingRun i j` is `i.val + 1 - j.val`. -/
@[simp]
theorem length_descendingRun (i j : Fin m) : (descendingRun i j).length = i.val + 1 - j.val := by
  simp [descendingRun]

/-- The `k`-th entry of `Fin.descendingRun i j` is `i - k`. -/
@[simp]
theorem getElem_descendingRun (i j : Fin m) (k : ℕ) (hk : k < (descendingRun i j).length) :
    (descendingRun i j)[k] = ⟨i.val - k, (Nat.sub_le i.val k).trans_lt i.isLt⟩ := by
  simp [descendingRun]

/-- `Fin.descendingRun i j` is empty if and only if `i < j`. -/
@[simp]
theorem descendingRun_eq_nil {i j : Fin m} : descendingRun i j = [] ↔ i < j := by
  rw [← List.length_eq_zero_iff, length_descendingRun, Fin.lt_def]
  omega

/-- A descending run from `i` to `i` is the singleton `[i]`. -/
@[simp]
theorem descendingRun_self (i : Fin m) : descendingRun i i = [i] := by
  have h : i.val + 1 - i.val = 1 := by omega
  rw [descendingRun, h, List.range_one]
  simp

/-- An index `a` belongs to `Fin.descendingRun i j` if and only if `j ≤ a ∧ a ≤ i`. -/
@[simp, grind =]
theorem mem_descendingRun {i j a : Fin m} :
    a ∈ descendingRun i j ↔ j ≤ a ∧ a ≤ i := by
  simp only [descendingRun, List.mem_map, List.mem_range, Fin.ext_iff, Fin.le_def]
  exact ⟨fun ⟨k, _, _⟩ ↦ by omega, fun ⟨_, _⟩ ↦ ⟨i.val - a.val, by omega, by omega⟩⟩

/-- Splitting a descending run `[i, …, j]` at an intermediate cut `k` with `j < k ≤ i`. -/
theorem descendingRun_split {i k j : Fin m} (hik : k ≤ i) (hjk : j < k) :
    descendingRun i j =
      descendingRun i k ++ descendingRun ⟨k.val - 1, by have := k.isLt; omega⟩ j := by
  have _ : k.val ≤ i.val := Fin.le_def.mp hik
  have _ : j.val < k.val := Fin.lt_def.mp hjk
  apply List.ext_getElem
  · simp only [List.length_append, length_descendingRun]; omega
  · intro t ht₁ ht₂
    rw [List.getElem_append]
    simp only [length_descendingRun, getElem_descendingRun]
    split_ifs with hlt
    · rfl
    · ext; dsimp only; omega

/-- Peeling the first entry `i` off `Fin.descendingRun i j` when `j < i`. -/
theorem descendingRun_cons {i j : Fin m} (h : j < i) :
    descendingRun i j = i :: descendingRun ⟨i.val - 1, by have := i.isLt; omega⟩ j := by
  simpa using descendingRun_split le_rfl h

/-- Peeling the last entry `j` off `Fin.descendingRun i j` when `j < i`. -/
theorem descendingRun_concat {i j : Fin m} (h : j < i) :
    descendingRun i j = descendingRun i ⟨j.val + 1, by have := i.isLt; omega⟩ ++ [j] := by
  have hk : (⟨j.val + 1, by have := i.isLt; omega⟩ : Fin m) ≤ i := by
    rw [Fin.le_def]; exact Fin.lt_def.mp h
  have hjk : j < (⟨j.val + 1, by have := i.isLt; omega⟩ : Fin m) := by
    rw [Fin.lt_def]; exact Nat.lt_succ_self j.val
  simpa using descendingRun_split hk hjk

/-- Any valid descending run `Fin.descendingRun i j` (`j ≤ i`) starts with `i`. -/
theorem exists_cons_descendingRun {i j : Fin m} (h : j ≤ i) :
    ∃ t, descendingRun i j = i :: t :=
  (eq_or_lt_of_le h).elim (fun hEq ↦ ⟨[], hEq ▸ descendingRun_self i⟩)
    fun hlt ↦ ⟨_, descendingRun_cons hlt⟩

/-- Any valid descending run `Fin.descendingRun i j` (`j ≤ i`) ends with `j`. -/
theorem exists_concat_descendingRun {i j : Fin m} (h : j ≤ i) :
    ∃ init, descendingRun i j = init ++ [j] :=
  (eq_or_lt_of_le h).elim (fun hEq ↦ ⟨[], by simp [hEq]⟩)
    fun hlt ↦ ⟨_, descendingRun_concat hlt⟩

/-- Mapping `Fin.castSucc` across a descending run gives the descending run of cast endpoints. -/
@[simp]
theorem map_castSucc_descendingRun (i j : Fin m) :
    (descendingRun i j).map Fin.castSucc = descendingRun i.castSucc j.castSucc := by
  simp [descendingRun, List.map_map, Function.comp_def]

/-- Decompose a word in `Fin m` into maximal descending-by-one runs `(i, j)`. -/
def parseRuns : List (Fin m) → List (Fin m × Fin m)
  | [] => []
  | [x] => [(x, x)]
  | x :: y :: rest =>
    match parseRuns (y :: rest) with
    | [] => [(x, x)]
    | (i, j) :: rs =>
      if (y : ℕ) + 1 = x then (x, j) :: rs else (x, x) :: (i, j) :: rs

/-- The empty word has no runs. -/
@[simp]
theorem parseRuns_nil : parseRuns ([] : List (Fin m)) = [] := (rfl)

/-- A single-letter word `[x]` has the single run `[(x, x)]`. -/
@[simp]
theorem parseRuns_singleton (x : Fin m) : parseRuns [x] = [(x, x)] := (rfl)

/-- Recursive step of `Fin.parseRuns` on a list of length at least two. -/
theorem parseRuns_cons_cons (x y : Fin m) (rest : List (Fin m)) :
    parseRuns (x :: y :: rest) =
      match parseRuns (y :: rest) with
      | [] => [(x, x)]
      | (i, j) :: rs =>
        if (y : ℕ) + 1 = x then (x, j) :: rs else (x, x) :: (i, j) :: rs := (rfl)

/-- On any nonempty list `y :: rest`, the first run returned by `Fin.parseRuns` has upper endpoint
`y`. -/
theorem parseRuns_cons_nonempty (y : Fin m) (rest : List (Fin m)) :
    ∃ j rs, parseRuns (y :: rest) = (y, j) :: rs := by
  induction rest generalizing y with
  | nil => exact ⟨y, [], rfl⟩
  | cons z rest ih =>
    obtain ⟨j, rs, h⟩ := ih z
    simp only [parseRuns, h]
    split_ifs <;> exact ⟨_, _, rfl⟩

/-- `Fin.parseRuns l` is empty if and only if `l` is empty. -/
@[simp]
theorem parseRuns_eq_nil {l : List (Fin m)} : parseRuns l = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons y rest =>
    obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y rest
    simp [h]

/-- Every run `(i, j)` in `Fin.parseRuns l` satisfies `j ≤ i`. -/
theorem lower_le_upper_parseRuns (l : List (Fin m)) :
    ∀ r ∈ parseRuns l, r.2 ≤ r.1 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    cases rest with
    | nil => simp
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      have hj : j ≤ y := ih (y, j) (by simp [h])
      have hrs : ∀ r ∈ rs, r.2 ≤ r.1 := fun r hr ↦ ih r (by simp [h, hr])
      simp only [parseRuns, h]
      split_ifs with hyx
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · have _ : j.val ≤ y.val := Fin.le_def.mp hj
          rw [Fin.le_def]; dsimp only; omega
        · exact hrs r hr
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | hr
        · exact le_rfl
        · exact hj
        · exact hrs r hr

/-- Concatenating the descending runs produced by `Fin.parseRuns l` recovers `l`. -/
@[simp]
theorem flatMap_parseRuns (l : List (Fin m)) :
    (parseRuns l).flatMap (fun r ↦ descendingRun r.1 r.2) = l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => simp
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      have hj : j ≤ y := lower_le_upper_parseRuns (y :: tl) (y, j) (by simp [h])
      simp only [parseRuns_cons_cons, h, List.flatMap_cons] at ih ⊢
      split_ifs with hyx
      · have hlt : j < x := by
          have _ : j.val ≤ y.val := Fin.le_def.mp hj
          rw [Fin.lt_def]; omega
        have hpred : (⟨x.val - 1, by have := x.isLt; omega⟩ : Fin m) = y := by
          ext; dsimp only; omega
        rw [List.flatMap_cons, descendingRun_cons hlt, hpred, List.cons_append, ih]
      · simpa [List.flatMap_cons] using ih

/-- Adjacent runs `(i₁, j₁), (i₂, j₂)` produced by `Fin.parseRuns` never satisfy
`(i₂ : ℕ) + 1 = j₁`. -/
theorem isChain_parseRuns (l : List (Fin m)) :
    (parseRuns l).IsChain fun r₁ r₂ ↦ (r₂.1 : ℕ) + 1 ≠ r₁.2 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    cases rest with
    | nil => simp
    | cons y tl =>
      obtain ⟨j, rs, h⟩ := parseRuns_cons_nonempty y tl
      rw [h] at ih
      simp only [parseRuns_cons_cons, h]
      split_ifs with hyx
      · cases rs with
        | nil => simp
        | cons _ _ =>
          rw [List.isChain_cons_cons] at ih ⊢
          exact ih
      · exact List.isChain_cons_cons.mpr ⟨hyx, ih⟩

/-- Prepending a descending run `[i, …, j]` before `rest` prepends `(i, j)` to `Fin.parseRuns`
whenever the first letter of `rest` does not continue the run as `j - 1`. -/
theorem parseRuns_descendingRun_append {i j : Fin m} (hji : j ≤ i) {rest : List (Fin m)}
    (hsep : ∀ y rest', rest = y :: rest' → (y : ℕ) + 1 ≠ j) :
    parseRuns (descendingRun i j ++ rest) = (i, j) :: parseRuns rest := by
  obtain ⟨d, hd⟩ : ∃ d, i.val - j.val = d := ⟨_, rfl⟩
  induction d generalizing i with
  | zero =>
    have hij : i = j := by
      have _ : j.val ≤ i.val := Fin.le_def.mp hji
      ext; omega
    subst hij
    rw [descendingRun_self, List.singleton_append]
    cases rest with
    | nil => rfl
    | cons y rest' =>
      obtain ⟨j₂, rs, h⟩ := parseRuns_cons_nonempty y rest'
      simp [parseRuns_cons_cons, h, hsep y rest' rfl]
  | succ d ih =>
    have hlt : j < i := by rw [Fin.lt_def]; omega
    let i' : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hi'_eq : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin m) = i' := rfl
    have hji' : j ≤ i' := by rw [Fin.le_def]; dsimp only [i']; omega
    rw [descendingRun_cons hlt, hi'_eq, List.cons_append]
    have hrec := ih hji' (by dsimp only [i']; omega)
    obtain ⟨zs, hdl⟩ := exists_cons_descendingRun hji'
    rw [hdl, List.cons_append] at hrec ⊢
    have hyi : (i' : ℕ) + 1 = i := by dsimp only [i']; omega
    simp [parseRuns_cons_cons, hrec, hyi]

/-- Uniqueness characterization of `Fin.parseRuns`: `parseRuns l = rs` holds if and only if every
run in `rs` is valid (`r.2 ≤ r.1`), adjacent runs cannot merge (`(r₂.1 : ℕ) + 1 ≠ r₁.2`), and the
concatenation of the runs is `l`. -/
theorem parseRuns_eq_iff {l : List (Fin m)} {rs : List (Fin m × Fin m)} :
    parseRuns l = rs ↔
      (∀ r ∈ rs, r.2 ≤ r.1) ∧
      (rs.IsChain fun r₁ r₂ ↦ (r₂.1 : ℕ) + 1 ≠ r₁.2) ∧
      rs.flatMap (fun r ↦ descendingRun r.1 r.2) = l := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨lower_le_upper_parseRuns l, isChain_parseRuns l, flatMap_parseRuns l⟩
  · rintro ⟨hle, hchain, rfl⟩
    induction rs with
    | nil => simp
    | cons r rs ih =>
      have hr : r.2 ≤ r.1 := hle r List.mem_cons_self
      have hrs_le : ∀ x ∈ rs, x.2 ≤ x.1 := fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)
      rw [List.flatMap_cons, parseRuns_descendingRun_append hr, ih hrs_le hchain.tail]
      intro y rest' hrest
      cases rs with
      | nil => simp at hrest
      | cons r₂ rs' =>
        obtain ⟨t, ht⟩ := exists_cons_descendingRun (hrs_le r₂ List.mem_cons_self)
        rw [List.flatMap_cons, ht, List.cons_append, List.cons.injEq] at hrest
        rw [← hrest.1]
        exact (List.isChain_cons_cons.mp hchain).1

end Fin
