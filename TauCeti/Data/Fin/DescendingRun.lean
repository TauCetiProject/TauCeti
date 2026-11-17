/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Chain
import Mathlib.Data.List.SplitBy
import Mathlib.Order.Fin.Basic

/-!
# Descending step-one runs in `Fin m` and maximal run factorization

For `i, j : Fin m`, `Fin.descendingRun i j` lists the indices `[i, i - 1, …, j]` descending by one
at each step (and is empty when `i < j`). Every word `l : List (Fin m)` factors uniquely as a
concatenation of nonempty descending runs `(i₁, j₁), …, (iₚ, jₚ)` whose adjacent runs cannot be
merged into a longer step-one run, meaning `(iₖ₊₁ : ℕ) + 1 ≠ jₖ`. `List.parseDescendingRuns l`
computes this canonical maximal descending-run factorization via `List.splitBy`, and
`List.parseDescendingRuns_eq_iff` characterizes it by validity (`jₖ ≤ iₖ`), maximality
(`List.IsChain`), and concatenation (`List.flatMap`).

This run factorization underlies normal-form arguments for words in indexed generators (such as
Jones normal form in Temperley–Lieb and Hecke algebras), where generator words are grouped into
maximal descending runs before comparing endpoints of adjacent runs.

## Main definitions and results

* `Fin.descendingRun`: the descending step-one run `[i, i - 1, …, j]` in `Fin m`.
* `Fin.mem_descendingRun`, `Fin.descendingRun_split`, `Fin.descendingRun_cons`,
  `Fin.descendingRun_concat`, `Fin.head_descendingRun`, `Fin.getLast_descendingRun`,
  `Fin.isChain_descendingRun`: membership, endpoint, splitting, and step-one chain lemmas for
  `Fin.descendingRun`.
* `List.getLast_le_head_and_eq_descendingRun_of_isChain`: converse characterization identifying any
  nonempty step-one descending chain in `Fin m` with `Fin.descendingRun`.
* `List.parseDescendingRuns`: decomposition of `l : List (Fin m)` into maximal descending-by-one
  runs.
* `List.snd_le_fst_of_mem_parseDescendingRuns`, `List.flatMap_parseDescendingRuns`,
  `List.isChain_parseDescendingRuns`: every run returned by `List.parseDescendingRuns` is nonempty
  (`r.2 ≤ r.1`), their concatenation recovers `l`, and adjacent runs satisfy
  `(r₂.1 : ℕ) + 1 ≠ r₁.2`.
* `List.parseDescendingRuns_eq_iff`: uniqueness characterization of the maximal descending-run
  factorization.
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

/-- The first entry of a nonempty descending run `Fin.descendingRun i j` is `i`. -/
@[simp]
theorem head_descendingRun {i j : Fin m} (hne : descendingRun i j ≠ []) :
    (descendingRun i j).head hne = i := by
  have h : j ≤ i := le_of_not_gt (descendingRun_eq_nil.not.mp hne)
  obtain ⟨t, ht⟩ := exists_cons_descendingRun h
  simp [ht]

/-- The last entry of a nonempty descending run `Fin.descendingRun i j` is `j`. -/
@[simp]
theorem getLast_descendingRun {i j : Fin m} (hne : descendingRun i j ≠ []) :
    (descendingRun i j).getLast hne = j := by
  have h : j ≤ i := le_of_not_gt (descendingRun_eq_nil.not.mp hne)
  obtain ⟨init, hinit⟩ := exists_concat_descendingRun h
  simp [hinit]

/-- Adjacent entries of `Fin.descendingRun i j` decrease by one at each step. -/
theorem isChain_descendingRun (i j : Fin m) :
    (descendingRun i j).IsChain fun x y : Fin m ↦ (y : ℕ) + 1 = x := by
  rw [List.isChain_iff_getElem]
  intro k hk
  simp only [length_descendingRun, getElem_descendingRun] at hk ⊢
  omega

end Fin

namespace List

variable {m : ℕ}

/-- A nonempty list in `Fin m` whose adjacent entries decrease by one at each step satisfies
`g.getLast hg ≤ g.head hg` and equals `Fin.descendingRun (g.head hg) (g.getLast hg)`. -/
theorem getLast_le_head_and_eq_descendingRun_of_isChain {g : List (Fin m)} (hg : g ≠ [])
    (hc : g.IsChain fun x y : Fin m ↦ (y : ℕ) + 1 = x) :
    g.getLast hg ≤ g.head hg ∧ g = Fin.descendingRun (g.head hg) (g.getLast hg) := by
  induction g with
  | nil => exact absurd rfl hg
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b rest =>
      rw [isChain_cons_cons] at hc
      obtain ⟨hba, hct⟩ := hc
      obtain ⟨hle, heq⟩ := ih (cons_ne_nil b rest) hct
      dsimp only [head_cons] at hle heq ⊢
      have hlast : (a :: b :: rest).getLast hg = (b :: rest).getLast (cons_ne_nil b rest) :=
        getLast_cons (cons_ne_nil b rest)
      have hlt : (a :: b :: rest).getLast hg < a := by
        have _ := Fin.le_def.mp hle
        rw [hlast, Fin.lt_def]; omega
      have hpred : (⟨a.val - 1, by have := a.isLt; omega⟩ : Fin m) = b := by
        ext; dsimp only; omega
      refine ⟨hlt.le, ?_⟩
      rw [Fin.descendingRun_cons hlt, hpred, hlast, ← heq]

/-- Decompose a word in `Fin m` into maximal descending-by-one runs `(i, j)`. -/
def parseDescendingRuns (l : List (Fin m)) : List (Fin m × Fin m) :=
  (l.splitBy fun x y : Fin m ↦ decide ((y : ℕ) + 1 = x)).attach.map fun ⟨g, hg⟩ ↦
    (g.head (ne_nil_of_mem_splitBy hg), g.getLast (ne_nil_of_mem_splitBy hg))

private theorem parseDescendingRuns_eq_of_splitBy {l : List (Fin m)} {gs : List (List (Fin m))}
    (h : l.splitBy (fun x y : Fin m ↦ decide ((y : ℕ) + 1 = x)) = gs) :
    l.parseDescendingRuns = gs.attach.map fun ⟨g, hg⟩ ↦
      have hne : g ≠ [] := ne_nil_of_mem_splitBy (h ▸ hg)
      (g.head hne, g.getLast hne) := by
  unfold parseDescendingRuns
  subst h
  rfl

/-- The empty word has no runs. -/
@[simp]
theorem parseDescendingRuns_nil : ([] : List (Fin m)).parseDescendingRuns = [] := by
  simp [parseDescendingRuns]

/-- A single-letter word `[x]` has the single run `[(x, x)]`. -/
@[simp]
theorem parseDescendingRuns_singleton (x : Fin m) : [x].parseDescendingRuns = [(x, x)] := by
  have h : [x].splitBy (fun a b : Fin m ↦ decide ((b : ℕ) + 1 = a)) = [[x]] :=
    splitBy_of_isChain (cons_ne_nil x []) (isChain_singleton x)
  rw [parseDescendingRuns_eq_of_splitBy h]
  rfl

/-- `List.parseDescendingRuns l` is empty if and only if `l` is empty. -/
@[simp]
theorem parseDescendingRuns_eq_nil {l : List (Fin m)} :
    l.parseDescendingRuns = [] ↔ l = [] := by
  simp [parseDescendingRuns]

/-- On any nonempty list `y :: rest`, the first run returned by `List.parseDescendingRuns` has upper
endpoint `y`. -/
theorem exists_parseDescendingRuns_cons (y : Fin m) (rest : List (Fin m)) :
    ∃ j rs, (y :: rest).parseDescendingRuns = (y, j) :: rs := by
  set rel : Fin m → Fin m → Bool := fun a b ↦ decide ((b : ℕ) + 1 = a)
  have hne : (y :: rest).splitBy rel ≠ [] := splitBy_ne_nil.mpr (cons_ne_nil y rest)
  have hhead := head_head_splitBy rel (cons_ne_nil y rest)
  obtain ⟨g, gs, hsplit⟩ := exists_cons_of_ne_nil hne
  have hg : g ∈ (y :: rest).splitBy rel := by simp [hsplit]
  have hy : g.head (ne_nil_of_mem_splitBy hg) = y := by simpa [hsplit] using hhead
  have hp := parseDescendingRuns_eq_of_splitBy hsplit
  rw [attach_cons, map_cons] at hp
  exact ⟨g.getLast (ne_nil_of_mem_splitBy hg), _, by simpa [hy] using hp⟩

/-- Every run `(i, j)` in `List.parseDescendingRuns l` satisfies `j ≤ i`. -/
theorem snd_le_fst_of_mem_parseDescendingRuns {l : List (Fin m)} {r : Fin m × Fin m}
    (hr : r ∈ l.parseDescendingRuns) : r.2 ≤ r.1 := by
  simp only [parseDescendingRuns, mem_map, mem_attach, true_and, Subtype.exists] at hr
  obtain ⟨g, hg, rfl⟩ := hr
  exact (getLast_le_head_and_eq_descendingRun_of_isChain (ne_nil_of_mem_splitBy hg)
    ((isChain_of_mem_splitBy hg).imp fun _ _ ↦ of_decide_eq_true)).1

/-- Concatenating the descending runs produced by `List.parseDescendingRuns l` recovers `l`. -/
@[simp]
theorem flatMap_parseDescendingRuns (l : List (Fin m)) :
    l.parseDescendingRuns.flatMap (fun r ↦ Fin.descendingRun r.1 r.2) = l := by
  unfold parseDescendingRuns
  rw [flatMap_def, map_map]
  have hmap : (l.splitBy fun x y : Fin m ↦ decide ((y : ℕ) + 1 = x)).attach.map
      ((fun r : Fin m × Fin m ↦ Fin.descendingRun r.1 r.2) ∘ fun ⟨g, hg⟩ ↦
        (g.head (ne_nil_of_mem_splitBy hg), g.getLast (ne_nil_of_mem_splitBy hg))) =
      l.splitBy fun x y : Fin m ↦ decide ((y : ℕ) + 1 = x) := by
    conv_rhs => rw [← attach_map_subtype_val (l.splitBy _)]
    refine map_congr_left fun ⟨g, hg⟩ _ ↦ ?_
    exact (getLast_le_head_and_eq_descendingRun_of_isChain (ne_nil_of_mem_splitBy hg)
      ((isChain_of_mem_splitBy hg).imp fun _ _ ↦ of_decide_eq_true)).2.symm
  rw [hmap, flatten_splitBy]

/-- Adjacent runs `(i₁, j₁), (i₂, j₂)` produced by `List.parseDescendingRuns` never satisfy
`(i₂ : ℕ) + 1 = j₁`. -/
theorem isChain_parseDescendingRuns (l : List (Fin m)) :
    l.parseDescendingRuns.IsChain fun r₁ r₂ ↦ (r₂.1 : ℕ) + 1 ≠ r₁.2 := by
  unfold parseDescendingRuns
  rw [isChain_map]
  have hc := isChain_getLast_head_splitBy (fun a b : Fin m ↦ decide ((b : ℕ) + 1 = a)) l
  rw [← attach_map_subtype_val (l.splitBy _), isChain_map] at hc
  exact hc.imp fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _, hfalse⟩ ↦ by
    simpa [decide_eq_false_iff_not] using hfalse

/-- Prepending a descending run `[i, …, j]` before `rest` prepends `(i, j)` to
`List.parseDescendingRuns` whenever the first letter of `rest` does not continue the run as
`j - 1`. -/
theorem parseDescendingRuns_descendingRun_append {i j : Fin m} (hji : j ≤ i)
    {rest : List (Fin m)} (hsep : ∀ y rest', rest = y :: rest' → (y : ℕ) + 1 ≠ j) :
    (Fin.descendingRun i j ++ rest).parseDescendingRuns =
      (i, j) :: rest.parseDescendingRuns := by
  set rel : Fin m → Fin m → Bool := fun a b ↦ decide ((b : ℕ) + 1 = a)
  have hne : Fin.descendingRun i j ≠ [] := Fin.descendingRun_eq_nil.not.mpr (not_lt_of_ge hji)
  have hsplit : (Fin.descendingRun i j ++ rest).splitBy rel =
      Fin.descendingRun i j :: rest.splitBy rel := by
    rw [splitBy_append, splitBy_of_isChain hne
      ((Fin.isChain_descendingRun i j).imp fun _ _ ↦ decide_eq_true), singleton_append]
    intro x hx y hy
    obtain ⟨init, hinit⟩ := Fin.exists_concat_descendingRun hji
    have hxj : j = x := by simpa [hinit] using hx
    cases rest with
    | nil => simp at hy
    | cons y' rest' =>
      have hyy' : y' = y := by simpa using hy
      simp [rel, ← hxj, ← hyy', hsep y' rest' rfl]
  rw [parseDescendingRuns_eq_of_splitBy hsplit, attach_cons, map_cons, map_map]
  simp [parseDescendingRuns, rel, Function.comp_def]

/-- Uniqueness characterization of `List.parseDescendingRuns`: `l.parseDescendingRuns = rs` holds if
and only if every run in `rs` is valid (`r.2 ≤ r.1`), adjacent runs cannot merge
(`(r₂.1 : ℕ) + 1 ≠ r₁.2`), and the concatenation of the runs is `l`. -/
theorem parseDescendingRuns_eq_iff {l : List (Fin m)} {rs : List (Fin m × Fin m)} :
    l.parseDescendingRuns = rs ↔
      (∀ r ∈ rs, r.2 ≤ r.1) ∧
      (rs.IsChain fun r₁ r₂ ↦ (r₂.1 : ℕ) + 1 ≠ r₁.2) ∧
      rs.flatMap (fun r ↦ Fin.descendingRun r.1 r.2) = l := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨fun _ ↦ snd_le_fst_of_mem_parseDescendingRuns, isChain_parseDescendingRuns l,
      flatMap_parseDescendingRuns l⟩
  · rintro ⟨hle, hchain, rfl⟩
    set rel : Fin m → Fin m → Bool := fun a b ↦ decide ((b : ℕ) + 1 = a)
    set gs := rs.map fun r ↦ Fin.descendingRun r.1 r.2
    have hne : ∀ r ∈ rs, Fin.descendingRun r.1 r.2 ≠ [] :=
      fun r hr ↦ Fin.descendingRun_eq_nil.not.mpr (not_lt_of_ge (hle r hr))
    have hsplit : (rs.flatMap fun r ↦ Fin.descendingRun r.1 r.2).splitBy rel = gs := by
      rw [splitBy_eq_iff]
      refine ⟨flatMap_def, ?_, ?_, ?_⟩
      · simp only [gs, mem_map, not_exists, not_and]
        exact fun r hr hnil ↦ hne r hr hnil
      · simp only [gs, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        exact fun r _ ↦ (Fin.isChain_descendingRun r.1 r.2).imp fun _ _ ↦ decide_eq_true
      · rw [isChain_map]
        rw [isChain_iff_forall_rel_of_append_cons_cons] at hchain ⊢
        intro r₁ r₂ l₁ l₂ hrs
        have hr₁ : r₁ ∈ rs := by rw [hrs]; simp
        have hr₂ : r₂ ∈ rs := by rw [hrs]; simp
        refine ⟨hne r₁ hr₁, hne r₂ hr₂, ?_⟩
        simp [rel, hchain hrs]
    rw [parseDescendingRuns_eq_of_splitBy hsplit]
    refine ext_getElem (by simp [gs]) fun k hk₁ hk₂ ↦ ?_
    simp [gs]

/-- Recursive step of `List.parseDescendingRuns` on a list of length at least two. -/
theorem parseDescendingRuns_cons_cons (x y : Fin m) (rest : List (Fin m)) :
    (x :: y :: rest).parseDescendingRuns =
      match (y :: rest).parseDescendingRuns with
      | [] => [(x, x)]
      | (i, j) :: rs =>
        if (y : ℕ) + 1 = x then (x, j) :: rs else (x, x) :: (i, j) :: rs := by
  obtain ⟨j, rs, h⟩ := exists_parseDescendingRuns_cons y rest
  rw [h]
  obtain ⟨hle, hchain, hflat⟩ := parseDescendingRuns_eq_iff.mp h
  have hjy : j ≤ y := hle (y, j) mem_cons_self
  split_ifs with hyx
  · refine parseDescendingRuns_eq_iff.mpr ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases mem_cons.mp hr with rfl | hr
      · have _ := Fin.le_def.mp hjy; rw [Fin.le_def]; dsimp only; omega
      · exact hle r (mem_cons_of_mem _ hr)
    · cases rs with
      | nil => simp
      | cons r₂ rs' => exact isChain_cons_cons.mpr ⟨(isChain_cons_cons.mp hchain).1, hchain.tail⟩
    · have hlt : j < x := by have _ := Fin.le_def.mp hjy; rw [Fin.lt_def]; omega
      have hpred : (⟨x.val - 1, by have := x.isLt; omega⟩ : Fin m) = y := by
        ext; dsimp only; omega
      rw [flatMap_cons] at hflat
      rw [flatMap_cons, Fin.descendingRun_cons hlt, hpred, cons_append, hflat]
  · have hsep : ∀ z rest', y :: rest = z :: rest' → (z : ℕ) + 1 ≠ x := by
      rintro _ _ ⟨rfl, rfl⟩; exact hyx
    simpa [h] using parseDescendingRuns_descendingRun_append (le_refl x) hsep

end List

