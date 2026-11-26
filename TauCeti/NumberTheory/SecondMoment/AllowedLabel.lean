/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
import TauCeti.Algebra.Polynomial.Card.MonicIsRoot
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Data.Set.Card
import TauCeti.RingTheory.Polynomial.DegreeLT
import TauCeti.RingTheory.Polynomial.Monic.Squarefree

/-!
# Allowed labels: monic polynomials avoiding squares, `0` and the `M`-th roots of unity

This file sets up the labels of the bad share of the main term of the second moments of
Poincaré series over finite fields: the monic squarefree polynomials with nonzero constant term
that index characters of `GL_r` over a finite field, and among them the allowed ones. The names
`IsLabel` and `IsAllowedLabel` are meant in this sense only, hence the namespace
`TauCeti.SecondMoment`.

A *label* is a monic squarefree polynomial with nonzero constant term. For `M : ℕ` a label is
*allowed* if it has no root `x` in the coefficient semiring with `x ^ M = 1` (roots in extensions
do not count). Over a finite field with `q` elements and for `M ≠ 0`, a monic polynomial of
degree `r` that is not an allowed label has a root at `0`, a root at an `M`-th root of unity of
the field, or a square factor of positive degree. The counts of
`TauCeti.Polynomial.ncard_setOf_monic_natDegree_isRoot_le` and
`Polynomial.ncard_setOf_monic_natDegree_not_squarefree_le` give at most
`(1 + M + r) * q ^ (r - 1)` of them.

## Main definitions

* `TauCeti.SecondMoment.IsLabel`: monic, squarefree, with nonzero constant term.
* `TauCeti.SecondMoment.IsAllowedLabel M`: a label with no root `x` in the coefficient semiring
  such that `x ^ M = 1`.

## Main results

* `TauCeti.SecondMoment.ncard_monic_not_isAllowedLabel_le`: for `M ≠ 0`, at most
  `(1 + M + r) * q ^ (r - 1)` monic polynomials of degree `r` are not allowed labels.
* `TauCeti.SecondMoment.one_sub_le_ncard_isAllowedLabel_mul`: if `M ≠ 0` and
  `(1 + M + 2 * r) / q ≤ ε`, a lower bound `1 - ε` on the total weight of the allowed labels of
  degree `r`, when each monic polynomial of degree `r` has weight `(1 - r / q) / q ^ r`.

## References

* R. Lidl and H. Niederreiter, *Finite Fields* (1983), ch. 3, for the counts of squarefree and
  irreducible polynomials over a finite field.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `New/Spanning/MainTerm/BadTypes.lean`
  (`New.card_not_isAllowedPolynomial_le`, `New.one_sub_le_card_allowed_mul`), for the statements.
-/

public section

open Polynomial TauCeti.Polynomial

namespace TauCeti.SecondMoment

section Defs

variable {R : Type*} [Semiring R]

/-- A *label* is a monic squarefree polynomial with nonzero constant term. -/
def IsLabel (f : R[X]) : Prop :=
  f.Monic ∧ Squarefree f ∧ f.coeff 0 ≠ 0

theorem isLabel_iff {f : R[X]} : IsLabel f ↔ f.Monic ∧ Squarefree f ∧ f.coeff 0 ≠ 0 :=
  Iff.rfl

/-- A label is *allowed* for `M : ℕ` if it has no root `x` in the coefficient semiring `R` with
`x ^ M = 1`. -/
def IsAllowedLabel (M : ℕ) (f : R[X]) : Prop :=
  IsLabel f ∧ ∀ x : R, x ^ M = 1 → ¬f.IsRoot x

theorem isAllowedLabel_iff {M : ℕ} {f : R[X]} :
    IsAllowedLabel M f ↔ IsLabel f ∧ ∀ x : R, x ^ M = 1 → ¬f.IsRoot x :=
  Iff.rfl

/-- A label is monic. -/
theorem IsLabel.monic {f : R[X]} (h : IsLabel f) : f.Monic :=
  (isLabel_iff.mp h).1

/-- A label is squarefree. -/
theorem IsLabel.squarefree {f : R[X]} (h : IsLabel f) : Squarefree f :=
  (isLabel_iff.mp h).2.1

/-- A label has nonzero constant term. -/
theorem IsLabel.coeff_zero_ne_zero {f : R[X]} (h : IsLabel f) : f.coeff 0 ≠ 0 :=
  (isLabel_iff.mp h).2.2

/-- An allowed label is a label. -/
theorem IsAllowedLabel.isLabel {M : ℕ} {f : R[X]} (h : IsAllowedLabel M f) : IsLabel f :=
  (isAllowedLabel_iff.mp h).1

/-- An allowed label for `M` does not vanish at any `x` in the coefficient semiring with
`x ^ M = 1`. -/
theorem IsAllowedLabel.not_isRoot {M : ℕ} {f : R[X]} (h : IsAllowedLabel M f) {x : R}
    (hx : x ^ M = 1) : ¬f.IsRoot x :=
  (isAllowedLabel_iff.mp h).2 x hx

/-- The polynomial `0` is not a label: its constant term is `0`. -/
@[simp]
theorem not_isLabel_zero : ¬IsLabel (0 : R[X]) :=
  fun h ↦ h.coeff_zero_ne_zero (coeff_zero 0)

/-- The polynomial `0` is not an allowed label, for any `M`. -/
@[simp]
theorem not_isAllowedLabel_zero (M : ℕ) : ¬IsAllowedLabel M (0 : R[X]) :=
  fun h ↦ not_isLabel_zero h.isLabel

/-- The polynomial `1` is a label. -/
@[simp]
theorem isLabel_one {R : Type*} [CommSemiring R] [Nontrivial R] : IsLabel (1 : R[X]) :=
  ⟨monic_one, squarefree_one, by simp⟩

/-- The polynomial `1` is an allowed label for every `M`: it has no roots at all. -/
@[simp]
theorem isAllowedLabel_one {R : Type*} [CommSemiring R] [Nontrivial R] (M : ℕ) :
    IsAllowedLabel M (1 : R[X]) :=
  ⟨isLabel_one, fun _ _ ↦ by simp⟩

end Defs

section Count

variable {K : Type*} [Field K]

/-- The possible bad roots: `0` and the `M`-th roots of unity. There are at most `1 + M`. -/
private lemma card_insert_zero_nthRootsFinset_le [DecidableEq K] (M : ℕ) :
    (insert 0 (nthRootsFinset M (1 : K))).card ≤ 1 + M := by
  have := card_nthRootsFinset_le M (1 : K)
  have := Finset.card_insert_le (0 : K) (nthRootsFinset M (1 : K))
  omega

/-- A monic polynomial that is not an allowed label has a root at `0` or at an `M`-th root of
unity, or is not squarefree. -/
private lemma isRoot_or_not_squarefree [DecidableEq K] {M : ℕ} (hM : M ≠ 0) {f : K[X]}
    (hf : f.Monic) (h : ¬IsAllowedLabel M f) :
    (∃ x ∈ insert 0 (nthRootsFinset M (1 : K)), f.IsRoot x) ∨ ¬Squarefree f := by
  simp only [isAllowedLabel_iff, isLabel_iff, hf, true_and, not_and_or, not_not, not_forall]
    at h
  rcases h with (h | h) | ⟨x, hx, hroot⟩
  · exact .inr h
  · exact .inl ⟨0, Finset.mem_insert_self _ _, by rwa [IsRoot, ← coeff_zero_eq_eval_zero]⟩
  · exact .inl ⟨x, Finset.mem_insert_of_mem
      ((mem_nthRootsFinset (Nat.pos_of_ne_zero hM) 1).mpr hx), hroot⟩

/-- In degree `0` the only monic polynomial is the allowed label `1`. -/
private lemma setOf_monic_natDegree_zero_not_isAllowedLabel (M : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = 0 ∧ ¬IsAllowedLabel M f} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f ⟨hf, h0, h⟩ ↦ h ?_
  rw [eq_one_of_monic_natDegree_zero hf h0]
  exact isAllowedLabel_one M

/-- **The non-allowed monic polynomials are few.** Over a finite field with `q` elements and for
`M ≠ 0`, at most `(1 + M + r) * q ^ (r - 1)` monic polynomials of degree `r` are not allowed
labels: at most `q ^ (r - 1)` have a root at `0`, at most `M * q ^ (r - 1)` a root at an `M`-th
root of unity, and at most `r * q ^ (r - 1)` are not squarefree. -/
theorem ncard_monic_not_isAllowedLabel_le [Finite K] {M : ℕ} (hM : M ≠ 0) (r : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard ≤
      (1 + M + r) * Nat.card K ^ (r - 1) := by
  classical
  set Z := insert 0 (nthRootsFinset M (1 : K))
  set V : K → Set K[X] := fun x ↦ {f : K[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot x}
  set Q := {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬Squarefree f}
  have hsub : {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f} ⊆
      (⋃ x ∈ Z, V x) ∪ Q := by
    rintro f ⟨hf, hr, h⟩
    rcases isRoot_or_not_squarefree hM hf h with ⟨x, hx, hroot⟩ | hsq
    · exact .inl (Set.mem_biUnion hx ⟨hf, hr, hroot⟩)
    · exact .inr ⟨hf, hr, hsq⟩
  -- the finiteness and the size of the root union come from one application
  have hV := Set.finite_and_ncard_le_sum_of_subset_biUnion (S := ⋃ x ∈ Z, V x) (t := Z) (C := V)
    subset_rfl fun x _ ↦
    ⟨(finite_setOf_monic_natDegree_eq K r).subset fun (_ : K[X]) (hf : _ ∈ V x) ↦
      ⟨hf.1, hf.2.1⟩, ncard_setOf_monic_natDegree_isRoot_le x r⟩
  rw [Finset.sum_const, smul_eq_mul] at hV
  have hQfin : Q.Finite := (finite_setOf_monic_natDegree_eq K r).subset fun _ hf ↦ ⟨hf.1, hf.2.1⟩
  have hQ : Q.ncard ≤ r * Nat.card K ^ (r - 1) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · -- in degree `0` the only monic polynomial is `1`, which is squarefree
      have hQ0 : Q = ∅ := Set.eq_empty_of_forall_notMem fun f ⟨hf, h0, hsq⟩ ↦
        hsq (eq_one_of_monic_natDegree_zero hf (h0.trans hr) ▸ squarefree_one)
      rw [hQ0, Set.ncard_empty]
      exact Nat.zero_le _
    · exact (ncard_setOf_monic_natDegree_not_squarefree_le K r).trans
        (Nat.le_mul_of_pos_left _ hr)
  calc _ ≤ ((⋃ x ∈ Z, V x) ∪ Q).ncard := Set.ncard_le_ncard hsub (hV.1.union hQfin)
    _ ≤ (⋃ x ∈ Z, V x).ncard + Q.ncard := Set.ncard_union_le _ _
    _ ≤ Z.card * Nat.card K ^ (r - 1) + r * Nat.card K ^ (r - 1) :=
        add_le_add hV.2 hQ
    _ ≤ (1 + M + r) * Nat.card K ^ (r - 1) := by
        rw [add_mul]
        gcongr
        exact card_insert_zero_nthRootsFinset_le M

/-- The count of `TauCeti.SecondMoment.ncard_monic_not_isAllowedLabel_le` multiplied by `q`. -/
private lemma ncard_monic_not_isAllowedLabel_mul_le [Finite K] {M : ℕ} (hM : M ≠ 0) (r : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard * Nat.card K ≤
      (1 + M + r) * Nat.card K ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [setOf_monic_natDegree_zero_not_isAllowedLabel, Set.ncard_empty, zero_mul]
    exact Nat.zero_le _
  · calc _ ≤ (1 + M + r) * Nat.card K ^ (r - 1) * Nat.card K :=
          Nat.mul_le_mul_right _ (ncard_monic_not_isAllowedLabel_le hM r)
      _ = (1 + M + r) * Nat.card K ^ r := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]

/-- The monic polynomials of degree `r` are the allowed labels of degree `r` and the others. -/
private lemma ncard_isAllowedLabel_add [Finite K] (M r : ℕ) :
    {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard +
      {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard = Nat.card K ^ r := by
  have hA : {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f} =
      {f : K[X] | f.Monic ∧ f.natDegree = r} ∩ {f | IsAllowedLabel M f} := by
    ext f
    exact ⟨fun h ↦ ⟨⟨h.2.isLabel.monic, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩
  have hB : {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f} =
      {f : K[X] | f.Monic ∧ f.natDegree = r} \ {f | IsAllowedLabel M f} := by
    ext f
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, and_assoc]
  rw [hA, hB, ← ncard_setOf_monic_natDegree_eq K r]
  exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (finite_setOf_monic_natDegree_eq K r)

/-- **A lower bound on the weight of the allowed labels.** Over a finite field with `q`
elements, let each monic polynomial of degree `r` have weight `(1 - r / q) / q ^ r`. If `M ≠ 0`
and `(1 + M + 2 * r) / q ≤ ε`, then the total weight of the allowed labels of degree `r` is at
least `1 - ε`. No bound `1 < r < q` is needed: for `r > q` the weight is negative and the total
is at least `1 - r / q`. -/
theorem one_sub_le_ncard_isAllowedLabel_mul [Finite K] {M r : ℕ} (hM : M ≠ 0) {ε : ℝ}
    (hε : (1 + M + 2 * r) / Nat.card K ≤ ε) :
    1 - ε ≤ {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard *
      ((1 - r / Nat.card K) / (Nat.card K : ℝ) ^ r) := by
  set A := {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard
  set B := {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard
  have hAB : (A : ℝ) + B = (Nat.card K : ℝ) ^ r := by
    exact_mod_cast ncard_isAllowedLabel_add (K := K) M r
  have hB : (B : ℝ) * Nat.card K ≤ (1 + M + r) * (Nat.card K : ℝ) ^ r := by
    exact_mod_cast ncard_monic_not_isAllowedLabel_mul_le (K := K) hM r
  set q : ℝ := (Nat.card K : ℝ)
  have hq : 0 < q := Nat.cast_pos.mpr Nat.card_pos
  have hqr : 0 < q ^ r := pow_pos hq r
  replace hB : (B : ℝ) / q ^ r ≤ (1 + M + r) / q := by
    rwa [div_le_div_iff₀ hqr hq]
  have ha : 0 ≤ (1 + M + r : ℝ) / q := by positivity
  have hb : 0 ≤ (r : ℝ) / q := by positivity
  have hε' : (1 + M + r : ℝ) / q + r / q ≤ ε := by
    rw [← add_div]
    exact le_of_eq_of_le (by ring) hε
  have ht : (A : ℝ) / q ^ r = 1 - B / q ^ r := by
    rw [eq_sub_iff_add_eq, ← add_div, hAB, div_self hqr.ne']
  have ht1 : (A : ℝ) / q ^ r ≤ 1 := by
    rw [ht, sub_le_self_iff]
    positivity
  have hw : (A : ℝ) * ((1 - r / q) / q ^ r) = A / q ^ r * (1 - r / q) := by ring
  have hlow : 1 - (1 + M + r) / q ≤ (A : ℝ) / q ^ r := by linarith
  rw [hw]
  rcases le_or_gt 0 (1 - (r : ℝ) / q) with hc | hc
  · have := mul_le_mul_of_nonneg_right hlow hc
    linarith [mul_nonneg ha hb]
  · have := mul_le_mul_of_nonpos_right ht1 hc.le
    linarith

end Count

end TauCeti.SecondMoment
