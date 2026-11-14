/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Set.Finite.List
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Farey symbols

A **Farey symbol** (`TauCeti.FareySymbol`), introduced by Kulkarni, is a finite combinatorial
datum encoding a finite-index subgroup of `PSL(2, ℤ)` together with a fundamental hyperbolic
polygon and a presentation by independent generators.

Concretely, it consists of a strictly increasing nonempty list `x_0 < x_1 < ⋯ < x_m` of rational
numbers `x_i = a_i / b_i` in lowest terms (`b_i > 0`), extended by the two signed representatives
`x_{-1} = -1 / 0` and `x_{m + 1} = 1 / 0` of the cusp `∞`, such that every consecutive pair is
unimodular (`a_{i + 1} b_i - a_i b_{i + 1} = 1`, forcing `x_0` and `x_m` to be integers), together
with a label from `TauCeti.SideLabel` (`even`, `odd`, or `free j`) on each of the `m + 2` sides
`(x_{i - 1}, x_i)` such that every free label occurs on either zero or two sides and the symbol is
nondegenerate (`1 < xs.length` or an `odd` label occurs, equivalently
`6 < 6 * freePairs + 3 * evenCount + 4 * oddCount`). Nondegeneracy excludes the two singleton
configurations of score `6` (`[0]` with `[even, even]` or `[free j, free j]`), whose side matrices
generate groups of infinite index in `PSL(2, ℤ)`.

This file defines `SideLabel` and `FareySymbol`, proves extensionality, the side-count and score
identities, consecutive unimodularity and cross-product monotonicity of the homogeneous endpoint
list `FareySymbol.endpoints`, the reflection and integer-translation symmetries, finiteness under
numerator, denominator, and free-label bounds, and constructs the worked symbols for `PSL(2, ℤ)`,
`Γ₀(2)`, `Γ(2)`, and the index-`7` noncongruence class with cusp widths `{4, 3}`.

## Main definitions and results

* `TauCeti.SideLabel`: the label `even`, `odd`, or `free j` carried by a side of a Farey symbol.
* `TauCeti.FareySymbol`: a bundled nondegenerate Farey symbol, extensional in `xs` and `labels`.
* `TauCeti.FareySymbol.evenCount`, `TauCeti.FareySymbol.oddCount`,
  `TauCeti.FareySymbol.freePairs`: the numbers `e₂`, `e₃`, `r` of even sides, odd sides, and free
  side pairs, satisfying `evenCount + oddCount + 2 * freePairs = labels.length`.
* `TauCeti.FareySymbol.nondegenerate_iff_six_lt_score` and
  `TauCeti.FareySymbol.six_lt_six_mul_freePairs_add_three_mul_evenCount_add_four_mul_oddCount`:
  nondegeneracy is equivalent to the hyperbolic-area positivity bound `6 < 6r + 3e₂ + 4e₃`.
* `TauCeti.FareySymbol.endpoints`, `TauCeti.FareySymbol.leftEndpoint`,
  `TauCeti.FareySymbol.rightEndpoint`, `TauCeti.FareySymbol.unimodular_endpoints`: the homogeneous
  endpoint list `[(-1, 0), (a_0, b_0), …, (a_m, b_m), (1, 0)]` and unimodularity of every side.
* `TauCeti.FareySymbol.reflect` and `TauCeti.FareySymbol.translate`: reflection `x ↦ -x` and
  integer translation `x ↦ x + j` (forming an `AddAction ℤ FareySymbol`).
* `TauCeti.FareySymbol.finite_setOf_abs_num_le_and_den_le_and_free_lt`: finiteness of Farey
  symbols with bounded numerators, denominators, and free-label indices.

## References

* R. S. Kulkarni, *An arithmetic-geometric method in the study of the subgroups of the modular
  group*, Amer. J. Math. **113** (1991), no. 6, 1053–1133.
* C. A. Kurth and L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey
  symbols*, J. Number Theory **128** (2008), no. 7, 1862–1888, arXiv:0710.1835.
-/

@[expose] public section

namespace TauCeti

/-- The label attached to a side `(x_{i - 1}, x_i)` of a Farey symbol: an elliptic involution
(`even`), an elliptic three-cycle (`odd`), or half of a paired side identification (`free j`). -/
inductive SideLabel where
  /-- An even side, carrying an elliptic involution fixing the side's geodesic midpoint. -/
  | even
  /-- An odd side, carrying an elliptic element of order `3` fixing an interior ideal-triangle
  center. -/
  | odd
  /-- Half of a paired free side identification indexed by `j : ℕ`. -/
  | free (j : ℕ)
  deriving DecidableEq, Repr

namespace SideLabel

/-- Whether a `SideLabel` is of the form `free j`. -/
def isFree : SideLabel → Bool
  | .free _ => true
  | _ => false

@[simp] theorem isFree_even : isFree .even = false := (rfl)
@[simp] theorem isFree_odd : isFree .odd = false := (rfl)
@[simp] theorem isFree_free (j : ℕ) : isFree (.free j) = true := (rfl)

/-- A label satisfies `isFree` precisely when it is `free j` for some `j`. -/
theorem isFree_eq_true_iff {l : SideLabel} : l.isFree = true ↔ ∃ j, l = .free j := by
  cases l <;> simp

/-- A label fails `isFree` precisely when it is `even` or `odd`. -/
theorem isFree_eq_false_iff {l : SideLabel} : l.isFree = false ↔ l = .even ∨ l = .odd := by
  cases l <;> simp

/-- Extract the index of a `free` label, or `none` on `even` and `odd` labels. -/
def freeIndex? : SideLabel → Option ℕ
  | .free j => some j
  | _ => none

@[simp] theorem freeIndex?_even : freeIndex? .even = none := (rfl)
@[simp] theorem freeIndex?_odd : freeIndex? .odd = none := (rfl)
@[simp] theorem freeIndex?_free (j : ℕ) : freeIndex? (.free j) = some j := (rfl)

/-- On any list of side labels, the counts of `even`, `odd`, and `free` entries partition the
length. -/
theorem count_even_add_count_odd_add_length_filter_free (labels : List SideLabel) :
    labels.count .even + labels.count .odd +
      (labels.filter fun l ↦ l matches .free _).length = labels.length := by
  induction labels with
  | nil => simp
  | cons l ls ih => cases l <;> simp <;> omega

/-- Filtering a list of `SideLabel`s by `freeIndex?` has the same length as filtering for `free`
entries. -/
theorem length_filterMap_freeIndex? (labels : List SideLabel) :
    (labels.filterMap freeIndex?).length =
      (labels.filter fun l ↦ l matches .free _).length := by
  induction labels with
  | nil => simp
  | cons l ls ih => cases l <;> simp [ih]

/-- Counting `j` in `labels.filterMap freeIndex?` agrees with counting `free j` in `labels`. -/
@[simp]
theorem count_filterMap_freeIndex? (labels : List SideLabel) (j : ℕ) :
    (labels.filterMap freeIndex?).count j = labels.count (.free j) := by
  induction labels with
  | nil => simp
  | cons l ls ih =>
    cases l with
    | even => simp [ih]
    | odd => simp [ih]
    | free k => simp [ih, List.count_cons]

/-- Membership in `labels.filterMap freeIndex?` is membership of `free j` in `labels`. -/
theorem mem_filterMap_freeIndex? {labels : List SideLabel} {j : ℕ} :
    j ∈ labels.filterMap freeIndex? ↔ SideLabel.free j ∈ labels := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, h⟩
    cases l with
    | even => cases h
    | odd => cases h
    | free k =>
      cases h
      exact hl
  · intro hj
    exact ⟨.free j, hj, rfl⟩

/-- If every free label in `labels` occurs either zero or two times, the number of free entries is
twice the number of distinct free indices occurring in `labels`. -/
theorem length_filter_free_eq_two_mul_card_of_count_free {labels : List SideLabel}
    (hfree : ∀ j, labels.count (.free j) = 0 ∨ labels.count (.free j) = 2) :
    (labels.filter fun l ↦ l matches .free _).length =
      2 * (labels.filterMap freeIndex?).toFinset.card := by
  rw [← length_filterMap_freeIndex?]
  set ns := labels.filterMap freeIndex?
  have hsum := List.sum_toFinset_count_eq_length ns
  have htwo : ∀ j ∈ ns.toFinset, ns.count j = 2 := by
    intro j hj
    have hmem : SideLabel.free j ∈ labels :=
      mem_filterMap_freeIndex?.mp (List.mem_toFinset.mp hj)
    have hpos : 0 < labels.count (.free j) := List.count_pos_iff.mpr hmem
    rw [count_filterMap_freeIndex?]
    exact (hfree j).resolve_left hpos.ne'
  rw [← hsum, Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul, mul_comm]

end SideLabel

/-- **A Farey symbol**: a strictly increasing nonempty list of reduced rationals `x_0 < ⋯ < x_m`
whose first and last entries are integers (`den = 1`, expressing unimodularity with `-1 / 0` and
`1 / 0`), whose consecutive entries are unimodular (`a_{i + 1} b_i - a_i b_{i + 1} = 1`), and whose
`m + 2` sides `(x_{i - 1}, x_i)` carry labels from `SideLabel` such that every free label occurs
either zero or two times and the symbol is nondegenerate (`1 < xs.length` or `SideLabel.odd`
occurs). -/
@[ext]
structure FareySymbol where
  /-- The strictly increasing rational cusps `x_0 < ⋯ < x_m`. -/
  xs : List ℚ
  /-- The labels on the `m + 2` sides `(x_{i - 1}, x_i)`, `0 ≤ i ≤ m + 1`. -/
  labels : List SideLabel
  /-- There is at least one finite rational cusp. -/
  ne_nil : xs ≠ []
  /-- There is one side label for each of the `xs.length + 1` intervals between `-∞`, the entries
  of `xs`, and `+∞`. -/
  labels_length : labels.length = xs.length + 1
  /-- The rational cusps are strictly increasing. -/
  sorted : xs.Pairwise (· < ·)
  /-- Unimodularity with `-1 / 0`: the first entry `x_0` has denominator `1`. -/
  head_den : (xs.head ne_nil).den = 1
  /-- Unimodularity with `1 / 0`: the last entry `x_m` has denominator `1`. -/
  last_den : (xs.getLast ne_nil).den = 1
  /-- Consecutive rational cusps `a_i / b_i < a_{i + 1} / b_{i + 1}` satisfy
  `a_{i + 1} b_i - a_i b_{i + 1} = 1`. -/
  unimodular : ∀ (i : ℕ) (h : i + 1 < xs.length),
    (xs[i + 1]'h).num * (xs[i]'(by omega)).den - (xs[i]'(by omega)).num * (xs[i + 1]'h).den = 1
  /-- Nondegeneracy: either `xs` has at least two entries, or an `odd` side occurs. -/
  nondegenerate : 1 < xs.length ∨ SideLabel.odd ∈ labels
  /-- Every free label occurs on either zero or two sides. -/
  free_twice : ∀ j, labels.count (.free j) = 0 ∨ labels.count (.free j) = 2
  deriving DecidableEq, Repr

namespace FareySymbol

/-! ### Basic list and sorting properties -/

/-- The list of finite cusps of a Farey symbol has positive length. -/
theorem xs_length_pos (F : FareySymbol) : 0 < F.xs.length :=
  List.length_pos_iff.mpr F.ne_nil

/-- Every Farey symbol has at least two sides. -/
theorem two_le_labels_length (F : FareySymbol) : 2 ≤ F.labels.length := by
  have := F.xs_length_pos
  have := F.labels_length
  omega

/-- The rational cusps of a Farey symbol have no duplicates. -/
theorem nodup_xs (F : FareySymbol) : F.xs.Nodup :=
  F.sorted.imp ne_of_lt

/-- Indexing into `F.xs` is strictly increasing. -/
theorem strictMono_xs (F : FareySymbol) ⦃i j : ℕ⦄ (hi : i < F.xs.length)
    (hj : j < F.xs.length) (hij : i < j) : F.xs[i] < F.xs[j] :=
  List.pairwise_iff_getElem.mp F.sorted i j hi hj hij

/-- The first finite cusp `x_0` has denominator `1` at index `0`. -/
@[simp]
theorem den_xs_zero (F : FareySymbol) : (F.xs[0]'F.xs_length_pos).den = 1 := by
  simpa [List.head_eq_getElem_zero] using F.head_den

/-- The last finite cusp `x_m` has denominator `1` at index `F.xs.length - 1`. -/
theorem den_xs_pred_length (F : FareySymbol) :
    (F.xs[F.xs.length - 1]'(by have := F.xs_length_pos; omega)).den = 1 := by
  simpa [List.getLast_eq_getElem] using F.last_den

/-! ### Side counts, free pairs, and the nondegeneracy score -/

/-- The number `e₂` of even sides of `F`. -/
def evenCount (F : FareySymbol) : ℕ := F.labels.count .even

/-- Definitional expansion of `evenCount`. -/
theorem evenCount_def (F : FareySymbol) : F.evenCount = F.labels.count .even := (rfl)

/-- The number `e₃` of odd sides of `F`. -/
def oddCount (F : FareySymbol) : ℕ := F.labels.count .odd

/-- Definitional expansion of `oddCount`. -/
theorem oddCount_def (F : FareySymbol) : F.oddCount = F.labels.count .odd := (rfl)

/-- The number `r` of free side pairs of `F`. -/
def freePairs (F : FareySymbol) : ℕ :=
  (F.labels.filter fun l ↦ l matches .free _).length / 2

/-- Definitional expansion of `freePairs`. -/
theorem freePairs_def (F : FareySymbol) :
    F.freePairs = (F.labels.filter fun l ↦ l matches .free _).length / 2 := (rfl)

/-- The finite set of free-label indices occurring on sides of `F`. -/
def freeLabels (F : FareySymbol) : Finset ℕ :=
  (F.labels.filterMap SideLabel.freeIndex?).toFinset

@[simp]
theorem mem_freeLabels {F : FareySymbol} {j : ℕ} :
    j ∈ F.freeLabels ↔ SideLabel.free j ∈ F.labels := by
  rw [freeLabels, List.mem_toFinset, SideLabel.mem_filterMap_freeIndex?]

/-- A free label occurring in `F.labels` occurs with multiplicity `2`. -/
theorem count_free_eq_two_of_mem {F : FareySymbol} {j : ℕ} (h : SideLabel.free j ∈ F.labels) :
    F.labels.count (.free j) = 2 :=
  (F.free_twice j).resolve_left (List.count_pos_iff.mpr h).ne'

/-- The number of free sides of `F` is `2 * F.freePairs`. -/
theorem length_filter_free (F : FareySymbol) :
    (F.labels.filter fun l ↦ l matches .free _).length = 2 * F.freePairs := by
  have h := SideLabel.length_filter_free_eq_two_mul_card_of_count_free F.free_twice
  rw [freePairs_def, h]
  omega

/-- The cardinality of `F.freeLabels` equals `F.freePairs`. -/
@[simp]
theorem card_freeLabels (F : FareySymbol) : F.freeLabels.card = F.freePairs := by
  have h1 := F.length_filter_free
  have h2 := SideLabel.length_filter_free_eq_two_mul_card_of_count_free F.free_twice
  rw [freeLabels] at *
  omega

/-- Every side of `F` is either even, odd, or part of one of the `freePairs` free pairs:
`e₂ + e₃ + 2r = m + 2`. -/
theorem evenCount_add_oddCount_add_two_mul_freePairs (F : FareySymbol) :
    F.evenCount + F.oddCount + 2 * F.freePairs = F.labels.length := by
  rw [evenCount_def, oddCount_def, ← F.length_filter_free,
    SideLabel.count_even_add_count_odd_add_length_filter_free]

/-- Positive `oddCount` is equivalent to `SideLabel.odd` occurring in `F.labels`. -/
@[simp]
theorem oddCount_pos_iff {F : FareySymbol} : 0 < F.oddCount ↔ SideLabel.odd ∈ F.labels :=
  List.count_pos_iff

/-- The number of side indices `j` carrying label `x` equals `F.labels.count x`. -/
theorem card_filter_labels_eq_count (F : FareySymbol) (x : SideLabel) :
    (Finset.univ.filter fun j : Fin F.labels.length ↦ F.labels[j] = x).card =
      F.labels.count x := by
  have hmap : (List.finRange F.labels.length).map (fun j ↦ F.labels[j]) = F.labels :=
    List.ext_getElem (by simp) (fun i h1 h2 ↦ by simp)
  have hset :
      ((List.finRange F.labels.length).filter (fun j ↦ decide (F.labels[j] = x))).toFinset =
        Finset.univ.filter (fun j : Fin F.labels.length ↦ F.labels[j] = x) := by
    ext j
    simp
  rw [← hset, List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
    ← List.countP_eq_length_filter]
  conv_rhs => rw [← hmap]
  rw [List.count_eq_countP, List.countP_map]
  exact List.countP_congr fun j _ ↦ by simp [beq_iff_eq]

/-- Every free side `i` of `F` has a partner side `j ≠ i` carrying the same free label. -/
theorem exists_other_free {F : FareySymbol} {i : Fin F.labels.length} {l : ℕ}
    (hi : F.labels[i] = .free l) :
    ∃ j : Fin F.labels.length, j ≠ i ∧ F.labels[j] = .free l := by
  have hmem : SideLabel.free l ∈ F.labels := hi ▸ List.getElem_mem ..
  have hcnt : F.labels.count (.free l) = 2 := F.count_free_eq_two_of_mem hmem
  by_contra! hall
  have hfilter :
      (Finset.univ.filter fun j : Fin F.labels.length ↦ F.labels[j] = .free l) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj ↦ by_contra fun hne ↦ hall j hne hj, fun h ↦ h ▸ hi⟩
  have hcard := F.card_filter_labels_eq_count (.free l)
  rw [hfilter, Finset.card_singleton, hcnt] at hcard
  omega

/-- The partner of a free side `i` in `F` is unique: no third side can share its free label. -/
theorem eq_of_free_partner {F : FareySymbol} {i j₁ j₂ : Fin F.labels.length} {l : ℕ}
    (hi : F.labels[i] = .free l) (hne₁ : j₁ ≠ i) (hj₁ : F.labels[j₁] = .free l)
    (hne₂ : j₂ ≠ i) (hj₂ : F.labels[j₂] = .free l) : j₁ = j₂ := by
  by_contra h12
  have hmem : SideLabel.free l ∈ F.labels := hi ▸ List.getElem_mem ..
  have hcnt : F.labels.count (.free l) = 2 := F.count_free_eq_two_of_mem hmem
  have hsub : ({i, j₁, j₂} : Finset (Fin F.labels.length)) ⊆
      Finset.univ.filter fun j : Fin F.labels.length ↦ F.labels[j] = .free l := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk with rfl | rfl | rfl <;> assumption
  have hle := Finset.card_le_card hsub
  have h3 : ({i, j₁, j₂} : Finset (Fin F.labels.length)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h12]
    · simp [hne₁.symm, hne₂.symm]
  have hcard := F.card_filter_labels_eq_count (.free l)
  omega

/-- If a free label occurs in `F`, then `F.xs` has at least two entries (`1 < F.xs.length`): a
singleton symbol with a free label would have two free sides and no odd side, violating
`nondegenerate`. -/
theorem one_lt_xs_length_of_free_mem {F : FareySymbol} {l : ℕ}
    (hl : SideLabel.free l ∈ F.labels) : 1 < F.xs.length := by
  rcases F.nondegenerate with hlt | hodd
  · exact hlt
  · have hodd' := List.count_pos_iff.mpr hodd
    have hsum := F.evenCount_add_oddCount_add_two_mul_freePairs
    have hfp : 1 ≤ F.freePairs := by
      rw [← F.card_freeLabels]
      exact Finset.card_pos.mpr ⟨l, mem_freeLabels.mpr hl⟩
    have := F.labels_length
    rw [oddCount_def] at hsum
    omega

/-- **Nondegeneracy score equivalence**: for a nonempty cusp list `xs` and a paired label list
`labels` of length `xs.length + 1`, the nondegeneracy condition `1 < xs.length ∨ .odd ∈ labels` is
equivalent to `6 < 6r + 3e₂ + 4e₃`. -/
theorem nondegenerate_iff_six_lt_score {xs : List ℚ} {labels : List SideLabel}
    (hne : xs ≠ []) (hlen : labels.length = xs.length + 1)
    (hfree : ∀ j, labels.count (.free j) = 0 ∨ labels.count (.free j) = 2) :
    (1 < xs.length ∨ SideLabel.odd ∈ labels) ↔
      6 < 6 * ((labels.filter fun l ↦ l matches .free _).length / 2) +
        3 * labels.count .even + 4 * labels.count .odd := by
  have hpart := SideLabel.count_even_add_count_odd_add_length_filter_free labels
  have heven := SideLabel.length_filter_free_eq_two_mul_card_of_count_free hfree
  have hxpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hodd_iff : SideLabel.odd ∈ labels ↔ 0 < labels.count .odd := List.count_pos_iff.symm
  rw [hodd_iff]
  omega

/-- The hyperbolic-area score `6r + 3e₂ + 4e₃` equals `3 * (F.xs.length + 1) + F.oddCount`. -/
theorem six_mul_freePairs_add_three_mul_evenCount_add_four_mul_oddCount (F : FareySymbol) :
    6 * F.freePairs + 3 * F.evenCount + 4 * F.oddCount = 3 * (F.xs.length + 1) + F.oddCount := by
  have h := F.evenCount_add_oddCount_add_two_mul_freePairs
  have hlen := F.labels_length
  omega

/-- Every Farey symbol satisfies the positivity bound `6 < 6r + 3e₂ + 4e₃`. -/
theorem six_lt_six_mul_freePairs_add_three_mul_evenCount_add_four_mul_oddCount (F : FareySymbol) :
    6 < 6 * F.freePairs + 3 * F.evenCount + 4 * F.oddCount :=
  (nondegenerate_iff_six_lt_score F.ne_nil F.labels_length F.free_twice).mp F.nondegenerate

/-! ### Homogeneous endpoints and consecutive unimodularity -/

/-- The homogeneous endpoints `[(-1, 0), (a_0, b_0), …, (a_m, b_m), (1, 0)]` of `F`, with the two
signed representatives of `∞`. -/
def endpoints (F : FareySymbol) : List (ℤ × ℤ) :=
  [(-1, 0)] ++ F.xs.map (fun x ↦ (x.num, (x.den : ℤ))) ++ [(1, 0)]

/-- Definitional expansion of `endpoints`. -/
theorem endpoints_def (F : FareySymbol) :
    F.endpoints = [(-1, 0)] ++ F.xs.map (fun x ↦ (x.num, (x.den : ℤ))) ++ [(1, 0)] := (rfl)

@[simp]
theorem endpoints_length (F : FareySymbol) : F.endpoints.length = F.xs.length + 2 := by
  simp [endpoints]

/-- `F.endpoints` has one more entry than `F.labels`. -/
theorem endpoints_length_eq_labels_length_add_one (F : FareySymbol) :
    F.endpoints.length = F.labels.length + 1 := by
  rw [endpoints_length, F.labels_length]

@[simp]
theorem endpoints_zero (F : FareySymbol) :
    F.endpoints[0]'(by simp) = (-1, 0) := by
  simp [endpoints]

@[simp]
theorem endpoints_succ (F : FareySymbol) (i : ℕ) (h : i < F.xs.length) :
    F.endpoints[i + 1]'(by simp; omega) = ((F.xs[i]'h).num, ((F.xs[i]'h).den : ℤ)) := by
  simp [endpoints, h]

@[simp]
theorem endpoints_last (F : FareySymbol) :
    F.endpoints[F.xs.length + 1]'(by simp) = (1, 0) := by
  simp [endpoints]

/-- Every homogeneous endpoint has nonnegative second coordinate (`b ≥ 0`). -/
theorem snd_endpoints_nonneg (F : FareySymbol) (k : ℕ) (hk : k < F.endpoints.length) :
    0 ≤ (F.endpoints[k]'hk).2 := by
  rw [endpoints_length] at hk
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · rcases eq_or_ne k (F.xs.length + 1) with rfl | hkl
    · simp
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hi : i < F.xs.length := by omega
      simp [endpoints_succ F i hi]

/-- The second coordinate of `F.endpoints[k]` vanishes exclusively at the two infinite ends
`k = 0` and `k = F.xs.length + 1`. -/
theorem snd_endpoints_eq_zero_iff (F : FareySymbol) (k : ℕ) (hk : k < F.endpoints.length) :
    (F.endpoints[k]'hk).2 = 0 ↔ k = 0 ∨ k = F.xs.length + 1 := by
  rw [endpoints_length] at hk
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · rcases eq_or_ne k (F.xs.length + 1) with rfl | hkl
    · simp
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hi : i < F.xs.length := by omega
      simp only [endpoints_succ F i hi, Nat.cast_eq_zero, (F.xs[i]'hi).den_nz, false_iff]
      omega

/-- No homogeneous endpoint of `F` is `(0, 0)`. -/
theorem endpoints_ne_zero (F : FareySymbol) (k : ℕ) (hk : k < F.endpoints.length) :
    F.endpoints[k]'hk ≠ (0, 0) := by
  intro h
  have h2 : (F.endpoints[k]'hk).2 = 0 := congrArg Prod.snd h
  rcases (F.snd_endpoints_eq_zero_iff k hk).mp h2 with rfl | hkl
  · simp at h
  · subst hkl
    simp at h

/-- Every homogeneous endpoint `(a, b)` of `F` has coprime coordinates `IsCoprime a b`. -/
theorem isCoprime_endpoints (F : FareySymbol) (k : ℕ) (hk : k < F.endpoints.length) :
    IsCoprime (F.endpoints[k]'hk).1 (F.endpoints[k]'hk).2 := by
  rw [endpoints_length] at hk
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [endpoints_zero]
    exact ⟨-1, 0, by ring⟩
  · rcases eq_or_ne k (F.xs.length + 1) with rfl | hkl
    · simp only [endpoints_last]
      exact ⟨1, 0, by ring⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hi : i < F.xs.length := by omega
      rw [endpoints_succ F i hi]
      exact (F.xs[i]'hi).isCoprime_num_den

/-- The homogeneous left endpoint `(a, b)` of side `i`. -/
def leftEndpoint (F : FareySymbol) (i : Fin F.labels.length) : ℤ × ℤ :=
  F.endpoints[i.val]'(by have := F.endpoints_length_eq_labels_length_add_one; omega)

/-- The homogeneous right endpoint `(c, d)` of side `i`. -/
def rightEndpoint (F : FareySymbol) (i : Fin F.labels.length) : ℤ × ℤ :=
  F.endpoints[i.val + 1]'(by have := F.endpoints_length_eq_labels_length_add_one; omega)

/-- Definitional expansion of `leftEndpoint`. -/
theorem leftEndpoint_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.leftEndpoint i =
      F.endpoints[i.val]'(by have := F.endpoints_length_eq_labels_length_add_one; omega) := (rfl)

/-- Definitional expansion of `rightEndpoint`. -/
theorem rightEndpoint_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.rightEndpoint i = F.endpoints[i.val + 1]'(by
      have := F.endpoints_length_eq_labels_length_add_one; omega) := (rfl)

/-- **Side unimodularity**: for every side `i` (including the two infinite ends), its endpoints
`(a, b) = F.leftEndpoint i` and `(c, d) = F.rightEndpoint i` satisfy `c * b - a * d = 1`. -/
theorem unimodular_endpoints (F : FareySymbol) (i : Fin F.labels.length) :
    (F.rightEndpoint i).1 * (F.leftEndpoint i).2 -
      (F.leftEndpoint i).1 * (F.rightEndpoint i).2 = 1 := by
  rcases i with ⟨i, hi⟩
  rw [F.labels_length] at hi
  rw [leftEndpoint_def, rightEndpoint_def]
  rcases eq_or_ne i 0 with rfl | hi0
  · simp [F.xs_length_pos, F.den_xs_zero]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hj | hj
    · rw [endpoints_succ F j (by omega), endpoints_succ F (j + 1) hj]
      exact F.unimodular j hj
    · have hjlen : j + 1 = F.xs.length := hj
      have hlast : F.endpoints[j + 1 + 1]'(by simp; omega) = (1, 0) := by
        simp [hjlen]
      have hpen : F.endpoints[j + 1]'(by simp; omega) =
          ((F.xs[j]'(by omega)).num, ((F.xs[j]'(by omega)).den : ℤ)) :=
        endpoints_succ F j (by omega)
      have hden : (F.xs[j]'(by omega)).den = 1 := by
        have hjeq : j = F.xs.length - 1 := by omega
        simpa [hjeq] using F.den_xs_pred_length
      rw [hlast, hpen, hden]
      ring

/-- For ordered indices `k < l` into `F.endpoints` other than the opposite infinite pair
`(0, F.xs.length + 1)`, the cross-product determinant `c * b - a * d` is strictly positive. -/
theorem det_endpoints_pos {F : FareySymbol} {k l : ℕ}
    (hkl : k < l) (hl : l < F.endpoints.length) (hne : ¬ (k = 0 ∧ l = F.xs.length + 1)) :
    0 < (F.endpoints[l]'hl).1 * (F.endpoints[k]'(hkl.trans hl)).2 -
      (F.endpoints[k]'(hkl.trans hl)).1 * (F.endpoints[l]'hl).2 := by
  rw [endpoints_length] at hl
  rcases eq_or_ne k 0 with rfl | hk0
  · have hlt : l < F.xs.length + 1 := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkl)
    have hj : j < F.xs.length := by omega
    simpa [endpoints_succ F j hj] using (F.xs[j]'hj).den_pos
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hi : i < F.xs.length := by omega
    rcases eq_or_ne l (F.xs.length + 1) with rfl | hll
    · simpa [endpoints_succ F i hi] using (F.xs[i]'hi).den_pos
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      have hj : j < F.xs.length := by omega
      have hij : i < j := by omega
      have hlt : F.xs[i]'hi < F.xs[j]'hj := F.strictMono_xs hi hj hij
      have hdiv : ((F.xs[i]'hi).num : ℚ) / (F.xs[i]'hi).den <
          ((F.xs[j]'hj).num : ℚ) / (F.xs[j]'hj).den := by
        rwa [Rat.num_div_den, Rat.num_div_den]
      rw [div_lt_div_iff₀ (Nat.cast_pos.mpr (F.xs[i]'hi).den_pos)
        (Nat.cast_pos.mpr (F.xs[j]'hj).den_pos)] at hdiv
      have hmul : (F.xs[i]'hi).num * (F.xs[j]'hj).den <
          (F.xs[j]'hj).num * (F.xs[i]'hi).den := by
        exact_mod_cast hdiv
      simp only [endpoints_succ F i hi, endpoints_succ F j hj]
      omega

/-- For any `k ≤ l < F.endpoints.length`, the cross-product determinant `c * b - a * d` is
nonnegative. -/
theorem det_endpoints_nonneg {F : FareySymbol} {k l : ℕ}
    (hkl : k ≤ l) (hl : l < F.endpoints.length) :
    0 ≤ (F.endpoints[l]'hl).1 * (F.endpoints[k]'(hkl.trans_lt hl)).2 -
      (F.endpoints[k]'(hkl.trans_lt hl)).1 * (F.endpoints[l]'hl).2 := by
  rcases eq_or_lt_of_le hkl with rfl | hlt
  · simp
  · by_cases hne : k = 0 ∧ l = F.xs.length + 1
    · rcases hne with ⟨rfl, rfl⟩
      simp
    · exact (F.det_endpoints_pos hlt hl hne).le

/-- For `k ≤ l < F.endpoints.length`, the cross-product determinant vanishes precisely when
`k = l` or `(k, l) = (0, F.xs.length + 1)` (the two signed representatives of `∞`). -/
theorem det_endpoints_eq_zero_iff {F : FareySymbol} {k l : ℕ}
    (hkl : k ≤ l) (hl : l < F.endpoints.length) :
    (F.endpoints[l]'hl).1 * (F.endpoints[k]'(hkl.trans_lt hl)).2 -
      (F.endpoints[k]'(hkl.trans_lt hl)).1 * (F.endpoints[l]'hl).2 = 0 ↔
      k = l ∨ (k = 0 ∧ l = F.xs.length + 1) := by
  constructor
  · intro hz
    rcases eq_or_lt_of_le hkl with rfl | hlt
    · exact Or.inl rfl
    · right
      by_contra hne
      exact (F.det_endpoints_pos hlt hl hne).ne' hz
  · rintro (rfl | ⟨rfl, rfl⟩) <;> simp

/-! ### Reflection and integer translation -/

/-- **Reflection of a Farey symbol**: send each rational cusp `x` to `-x`, reversing both `xs` and
`labels`. -/
def reflect (F : FareySymbol) : FareySymbol where
  xs := (F.xs.map (-·)).reverse
  labels := F.labels.reverse
  ne_nil := by simp [F.ne_nil]
  labels_length := by simp [F.labels_length]
  sorted := by
    rw [List.pairwise_reverse, List.pairwise_map]
    exact F.sorted.imp fun h ↦ neg_lt_neg h
  head_den := by
    have hlast := F.last_den
    simpa [List.head_reverse, List.getLast_map, Rat.den_neg_eq_den] using hlast
  last_den := by
    have hhead := F.head_den
    simpa [List.getLast_reverse, List.head_map, Rat.den_neg_eq_den] using hhead
  unimodular := by
    intro i hi
    simp only [List.length_reverse, List.length_map] at hi
    set j := F.xs.length - 2 - i
    have hj : j + 1 < F.xs.length := by omega
    have huni := F.unimodular j hj
    have h1 : F.xs.length - 1 - (i + 1) = j := by omega
    have h2 : F.xs.length - 1 - i = j + 1 := by omega
    simp only [List.getElem_reverse, List.length_map, List.getElem_map, h1, h2,
      Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]
    linarith
  nondegenerate := by
    simpa using F.nondegenerate
  free_twice := fun j ↦ by simpa using F.free_twice j

@[simp] theorem reflect_xs (F : FareySymbol) : F.reflect.xs = (F.xs.map (-·)).reverse := (rfl)
@[simp] theorem reflect_labels (F : FareySymbol) : F.reflect.labels = F.labels.reverse := (rfl)

/-- Side `i` of `F.reflect` carries the label of the opposite side `i.rev` of `F`. -/
theorem getElem_reflect_labels (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.labels[i] = F.labels[(i.rev.cast (by simp) : Fin F.labels.length)] := by
  have h : F.labels.length - 1 - i.val = F.reflect.labels.length - (i.val + 1) := by
    simp; omega
  simp [List.getElem_reverse, Fin.val_rev, h]

/-- Reflection is an involution on Farey symbols. -/
@[simp]
theorem reflect_reflect (F : FareySymbol) : F.reflect.reflect = F := by
  ext <;> simp [List.map_reverse]

@[simp]
theorem evenCount_reflect (F : FareySymbol) : F.reflect.evenCount = F.evenCount := by
  simp [evenCount]

@[simp]
theorem oddCount_reflect (F : FareySymbol) : F.reflect.oddCount = F.oddCount := by
  simp [oddCount]

@[simp]
theorem freePairs_reflect (F : FareySymbol) : F.reflect.freePairs = F.freePairs := by
  simp [freePairs, List.filter_reverse]

/-- Reflection reverses `F.endpoints` while negating first coordinates (including swapping
`(-1, 0)` and `(1, 0)` up to sign). -/
theorem endpoints_reflect (F : FareySymbol) :
    F.reflect.endpoints = F.endpoints.reverse.map (fun p ↦ (-p.1, p.2)) := by
  simp [endpoints, List.reverse_append, List.map_reverse, List.map_append, Function.comp_def]

/-- Side `i` of `F.reflect` has left endpoint `(-c, d)`, where `(c, d)` is the right endpoint of
the opposite side `i.rev` of `F`. -/
theorem leftEndpoint_reflect (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.leftEndpoint i =
      (-(F.rightEndpoint (i.rev.cast (by simp))).1,
        (F.rightEndpoint (i.rev.cast (by simp))).2) := by
  have := F.labels_length
  have : F.reflect.labels.length = F.labels.length := by simp
  have hidx : F.xs.length + 1 - i.val = F.reflect.labels.length - (i.val + 1) + 1 := by omega
  simp [leftEndpoint_def, rightEndpoint_def, endpoints_reflect, List.getElem_reverse,
    Fin.val_rev, hidx]

/-- Side `i` of `F.reflect` has right endpoint `(-a, b)`, where `(a, b)` is the left endpoint of
the opposite side `i.rev` of `F`. -/
theorem rightEndpoint_reflect (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.rightEndpoint i =
      (-(F.leftEndpoint (i.rev.cast (by simp))).1,
        (F.leftEndpoint (i.rev.cast (by simp))).2) := by
  have := F.labels_length
  have : F.reflect.labels.length = F.labels.length := by simp
  have hidx : F.xs.length - i.val = F.reflect.labels.length - (i.val + 1) := by omega
  simp [leftEndpoint_def, rightEndpoint_def, endpoints_reflect, List.getElem_reverse,
    Fin.val_rev, hidx]

/-- **Integer translation of a Farey symbol**: shift every rational cusp by `j ∈ ℤ` while keeping
the side labels unchanged. -/
def translate (j : ℤ) (F : FareySymbol) : FareySymbol where
  xs := F.xs.map (· + (j : ℚ))
  labels := F.labels
  ne_nil := by simp [F.ne_nil]
  labels_length := by simp [F.labels_length]
  sorted := by
    rw [List.pairwise_map]
    exact F.sorted.imp fun h ↦ by linarith
  head_den := by
    simpa [List.head_map, Rat.add_intCast_den] using F.head_den
  last_den := by
    simpa [List.getLast_map, Rat.add_intCast_den] using F.last_den
  unimodular := by
    intro i hi
    simp only [List.length_map] at hi
    have hnum : ∀ q : ℚ, (q + (j : ℚ)).num = q.num + j * q.den := fun q ↦ by
      have h := Rat.add_num_den' q (j : ℚ)
      simp only [Rat.den_intCast, Nat.cast_one, mul_one, Rat.num_intCast,
        Rat.add_intCast_den] at h
      exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz) h
    simp only [List.getElem_map, hnum, Rat.add_intCast_den]
    linear_combination F.unimodular i hi
  nondegenerate := by
    simpa using F.nondegenerate
  free_twice := F.free_twice

@[simp] theorem translate_xs (j : ℤ) (F : FareySymbol) :
    (F.translate j).xs = F.xs.map (· + (j : ℚ)) := (rfl)

@[simp] theorem translate_labels (j : ℤ) (F : FareySymbol) :
    (F.translate j).labels = F.labels := (rfl)

@[simp]
theorem translate_zero (F : FareySymbol) : F.translate 0 = F := by
  ext <;> simp

theorem translate_add (j k : ℤ) (F : FareySymbol) :
    F.translate (j + k) = (F.translate k).translate j := by
  ext <;> simp [add_comm (j : ℚ)]

/-- Integer translation defines an additive action of `ℤ` on `FareySymbol`. -/
instance instAddActionInt : AddAction ℤ FareySymbol where
  vadd := translate
  zero_vadd := translate_zero
  add_vadd := translate_add

@[simp]
theorem vadd_eq_translate (j : ℤ) (F : FareySymbol) : j +ᵥ F = F.translate j := (rfl)

@[simp]
theorem evenCount_translate (j : ℤ) (F : FareySymbol) :
    (F.translate j).evenCount = F.evenCount := (rfl)

@[simp]
theorem oddCount_translate (j : ℤ) (F : FareySymbol) :
    (F.translate j).oddCount = F.oddCount := (rfl)

@[simp]
theorem freePairs_translate (j : ℤ) (F : FareySymbol) :
    (F.translate j).freePairs = F.freePairs := (rfl)

/-- Integer translation acts faithfully on every Farey symbol: `F.translate j = F.translate k`
implies `j = k`. -/
theorem translate_injective (F : FareySymbol) : Function.Injective (fun j : ℤ ↦ F.translate j) := by
  intro j k hjk
  have hxs := congrArg (fun G : FareySymbol ↦ G.xs[0]'(by simp [G.xs_length_pos])) hjk
  simp only [translate_xs, List.getElem_map, add_right_inj, Int.cast_inj] at hxs
  exact hxs

/-- Under translation by `j ∈ ℤ`, every homogeneous endpoint `(a, b)` of `F` (including `(-1, 0)`
and `(1, 0)`) maps to `(a + j * b, b)`. -/
theorem endpoints_translate (j : ℤ) (F : FareySymbol) :
    (F.translate j).endpoints = F.endpoints.map (fun p ↦ (p.1 + j * p.2, p.2)) := by
  have hnum : ∀ q : ℚ, (q + (j : ℚ)).num = q.num + j * q.den := fun q ↦ by
    have h := Rat.add_num_den' q (j : ℚ)
    simp only [Rat.den_intCast, Nat.cast_one, mul_one, Rat.num_intCast,
      Rat.add_intCast_den] at h
    exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz) h
  simp [endpoints, List.map_append, Function.comp_def, hnum, Rat.add_intCast_den]

/-- Left endpoint of side `i` after translating `F` by `j ∈ ℤ`. -/
theorem leftEndpoint_translate (j : ℤ) (F : FareySymbol) (i : Fin (F.translate j).labels.length) :
    (F.translate j).leftEndpoint i =
      ((F.leftEndpoint (i.cast (by simp))).1 + j * (F.leftEndpoint (i.cast (by simp))).2,
        (F.leftEndpoint (i.cast (by simp))).2) := by
  simp [leftEndpoint_def, endpoints_translate]

/-- Right endpoint of side `i` after translating `F` by `j ∈ ℤ`. -/
theorem rightEndpoint_translate (j : ℤ) (F : FareySymbol) (i : Fin (F.translate j).labels.length) :
    (F.translate j).rightEndpoint i =
      ((F.rightEndpoint (i.cast (by simp))).1 + j * (F.rightEndpoint (i.cast (by simp))).2,
        (F.rightEndpoint (i.cast (by simp))).2) := by
  simp [rightEndpoint_def, endpoints_translate]

/-! ### Finiteness under height and label bounds -/

/-- **Finiteness of bounded Farey symbols**: for fixed natural numbers `A`, `B`, `L`, there are
only finitely many Farey symbols whose cusps satisfy `|x.num| ≤ A` and `x.den ≤ B` and whose free
labels satisfy `j < L`. No separate bound on `xs.length` is required because `F.xs` is strictly
increasing and draws without repetition from the finite set of eligible rationals. -/
theorem finite_setOf_abs_num_le_and_den_le_and_free_lt (A B L : ℕ) :
    {F : FareySymbol | (∀ x ∈ F.xs, |x.num| ≤ (A : ℤ) ∧ x.den ≤ B) ∧
      ∀ j, SideLabel.free j ∈ F.labels → j < L}.Finite := by
  classical
  let SQ : Set ℚ := {x : ℚ | |x.num| ≤ (A : ℤ) ∧ x.den ≤ B}
  have hSQ : SQ.Finite := by
    have hinj : Function.Injective fun x : ℚ ↦ (x.num, x.den) := fun x y h ↦
      Rat.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
    refine (((Set.finite_Icc (-(A : ℤ)) (A : ℤ)).prod (Set.finite_Iic B)).preimage
      hinj.injOn).subset ?_
    rintro x ⟨hnum, hden⟩
    exact ⟨abs_le.mp hnum, hden⟩
  have : Finite SQ := hSQ.to_subtype
  let SL : Set SideLabel := insert .even (insert .odd (SideLabel.free '' Set.Iio L))
  have hSL : SL.Finite :=
    ((Set.finite_Iio L).image SideLabel.free).insert .odd |>.insert .even
  have : Finite SL := hSL.to_subtype
  let N : ℕ := hSQ.toFinset.card
  have hX : ({xs : List ℚ | xs.length ≤ N ∧ ∀ x ∈ xs, x ∈ SQ}).Finite := by
    refine ((List.finite_length_le SQ N).image (List.map Subtype.val)).subset ?_
    rintro xs ⟨hlen, hmem⟩
    exact ⟨xs.pmap Subtype.mk hmem, by simpa using hlen, by simp [List.map_pmap]⟩
  have hY : ({ls : List SideLabel | ls.length ≤ N + 1 ∧ ∀ l ∈ ls, l ∈ SL}).Finite := by
    refine ((List.finite_length_le SL (N + 1)).image (List.map Subtype.val)).subset ?_
    rintro ls ⟨hlen, hmem⟩
    exact ⟨ls.pmap Subtype.mk hmem, by simpa using hlen, by simp [List.map_pmap]⟩
  have hinj : Function.Injective fun F : FareySymbol ↦ (F.xs, F.labels) := fun F₁ F₂ h ↦
    FareySymbol.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  refine ((hX.prod hY).preimage hinj.injOn).subset ?_
  rintro F ⟨hFxs, hFfree⟩
  have hsub : F.xs.toFinset ⊆ hSQ.toFinset := fun x hx ↦
    hSQ.mem_toFinset.mpr (hFxs x (List.mem_toFinset.mp hx))
  have hlen : F.xs.length ≤ N := by
    rw [← List.toFinset_card_of_nodup F.nodup_xs]
    exact Finset.card_le_card hsub
  refine ⟨⟨hlen, hFxs⟩, ⟨by rw [F.labels_length]; omega, ?_⟩⟩
  intro l hl
  cases l with
  | even => exact Or.inl rfl
  | odd => exact Or.inr (Or.inl rfl)
  | free j => exact Or.inr (Or.inr ⟨j, hFfree j hl, rfl⟩)

/-- A Farey symbol satisfies the height bounds `A = B = 1` if and only if every cusp in `F.xs`
belongs to `{-1, 0, 1}`. -/
theorem forall_mem_xs_abs_num_le_one_and_den_le_one_iff (F : FareySymbol) :
    (∀ x ∈ F.xs, |x.num| ≤ 1 ∧ x.den ≤ 1) ↔ ∀ x ∈ F.xs, x ∈ ({-1, 0, 1} : Set ℚ) := by
  refine forall₂_congr fun x _ ↦ ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hnum, hden⟩
    have hd : x.den = 1 := Nat.le_antisymm hden x.den_pos
    rw [← Rat.intCast_num_of_den_eq_one hd]
    rw [abs_le] at hnum
    have hcases : x.num = -1 ∨ x.num = 0 ∨ x.num = 1 := by omega
    rcases hcases with h | h | h <;> simp [h]
  · rintro (rfl | rfl | rfl) <;> norm_num

/-! ### Standard worked Farey symbols -/

/-- The level-one Farey symbol: `xs = [0]` with sides `(even, odd)`, of score `7`. -/
def levelOne : FareySymbol where
  xs := [0]
  labels := [.even, .odd]
  ne_nil := by decide
  labels_length := by decide
  sorted := by decide
  head_den := by decide
  last_den := by decide
  unimodular := fun _ hi ↦ by simp at hi
  nondegenerate := Or.inr (by decide)
  free_twice := fun _ ↦ Or.inl rfl

/-- The singleton Farey symbol `xs = [0]` with two odd sides `(odd, odd)`, of score `8`. -/
def oddSingleton : FareySymbol where
  xs := [0]
  labels := [.odd, .odd]
  ne_nil := by decide
  labels_length := by decide
  sorted := by decide
  head_den := by decide
  last_den := by decide
  unimodular := fun _ hi ↦ by simp at hi
  nondegenerate := Or.inr (by decide)
  free_twice := fun _ ↦ Or.inl rfl

/-- The Farey symbol for `Γ₀(2)`: `xs = [0, 1]` with labels `[free 1, even, free 1]`. -/
def gamma0Two : FareySymbol where
  xs := [0, 1]
  labels := [.free 1, .even, .free 1]
  ne_nil := by decide
  labels_length := by decide
  sorted := by decide
  head_den := by decide
  last_den := by decide
  unimodular := fun i hi ↦ by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    norm_num
  nondegenerate := Or.inl (by decide)
  free_twice := fun j ↦ by
    by_cases hj : j = 1
    · subst hj; exact Or.inr (by decide)
    · left; simp [List.count_cons]; omega

/-- The Farey symbol for `Γ(2)`: `xs = [0, 1, 2]` with labels `[free 2, free 1, free 1, free 2]`. -/
def gammaTwo : FareySymbol where
  xs := [0, 1, 2]
  labels := [.free 2, .free 1, .free 1, .free 2]
  ne_nil := by decide
  labels_length := by decide
  sorted := by decide
  head_den := by decide
  last_den := by decide
  unimodular := fun i hi ↦ by
    have hlt : i < 2 := by simp at hi; omega
    interval_cases i <;> norm_num
  nondegenerate := Or.inl (by decide)
  free_twice := fun j ↦ by
    by_cases hj1 : j = 1
    · subst hj1; exact Or.inr (by decide)
    · by_cases hj2 : j = 2
      · subst hj2; exact Or.inr (by decide)
      · left; simp [List.count_cons]; omega

/-- The Farey symbol for the index-`7` noncongruence subgroup class with cusp widths `{4, 3}`:
`xs = [0, 1, 2]` with labels `[even, free 1, odd, free 1]`. -/
def indexSeven43 : FareySymbol where
  xs := [0, 1, 2]
  labels := [.even, .free 1, .odd, .free 1]
  ne_nil := by decide
  labels_length := by decide
  sorted := by decide
  head_den := by decide
  last_den := by decide
  unimodular := fun i hi ↦ by
    have hlt : i < 2 := by simp at hi; omega
    interval_cases i <;> norm_num
  nondegenerate := Or.inl (by decide)
  free_twice := fun j ↦ by
    by_cases hj : j = 1
    · subst hj; exact Or.inr (by decide)
    · left; simp [List.count_cons]; omega

/-- Without a numerator bound, even `x.den ≤ 1` and zero free labels admit infinitely many Farey
symbols (namely the integer translates `levelOne.translate j`). -/
theorem infinite_setOf_den_le_one_and_free_lt :
    {F : FareySymbol | (∀ x ∈ F.xs, x.den ≤ 1) ∧
      ∀ j, SideLabel.free j ∈ F.labels → j < 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem levelOne.translate_injective fun j ↦ ⟨?_, ?_⟩
  · intro x hx
    simp only [levelOne, translate_xs, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨_, rfl, rfl⟩
    simp
  · intro k hk
    simp [levelOne] at hk

/-- Without a bound on free-label indices, even `|x.num| ≤ 1` and `x.den ≤ 1` admit infinitely
many Farey symbols (obtained by varying the free label on `[0, 1]`). -/
theorem infinite_setOf_abs_num_le_one_and_den_le_one :
    {F : FareySymbol | ∀ x ∈ F.xs, |x.num| ≤ 1 ∧ x.den ≤ 1}.Infinite := by
  let f : ℕ → FareySymbol := fun k ↦
    { xs := [0, 1]
      labels := [.free k, .even, .free k]
      ne_nil := by decide
      labels_length := rfl
      sorted := by decide
      head_den := by decide
      last_den := by decide
      unimodular := fun i hi ↦ by
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0
        norm_num
      nondegenerate := Or.inl (by decide)
      free_twice := fun j ↦ by
        by_cases hj : j = k
        · subst hj; exact Or.inr (by simp)
        · left; simp [List.count_cons]; omega }
  have hinj : Function.Injective f := fun a b hab ↦ by
    have h := congrArg (fun G : FareySymbol ↦ G.labels) hab
    simpa [f] using h
  refine Set.infinite_of_injective_forall_mem hinj fun k x hx ↦ ?_
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> norm_num

end FareySymbol

end TauCeti
