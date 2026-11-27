/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.RingTheory.Polynomial.Monic.Count
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Allowed labels: monic polynomials avoiding squares, `0` and the `M`-th roots of unity

This file sets up the labels of the bad share of the main term of the second moments of
Poincaré series over finite fields: the monic squarefree polynomials with nonzero constant term
that index characters of `GL_r` over a finite field, and among them the allowed ones. The names
`IsLabel` and `IsAllowedLabel` are meant in this sense only, hence the namespace
`TauCeti.SecondMoment`.

A *label* is a monic squarefree polynomial with nonzero constant term. For `M : ℕ` a label is
*allowed* if it has no root `x` with `x ^ M = 1`. Over a finite field with `q` elements and for
`M ≠ 0`, a monic polynomial of degree `r` that is not an allowed label has a root at `0`, a root
at an `M`-th root of unity, or a square factor of positive degree. The counts of
`Polynomial.ncard_monic_isRoot_le` and `Polynomial.ncard_monic_not_squarefree_le` give at most
`(1 + M + r) * q ^ (r - 1)` of them.

## Main definitions

* `TauCeti.SecondMoment.IsLabel`: monic, squarefree, with nonzero constant term.
* `TauCeti.SecondMoment.IsAllowedLabel M`: a label with no root `x` such that `x ^ M = 1`.

## Main results

* `TauCeti.SecondMoment.ncard_monic_not_isAllowedLabel_le`: for `M ≠ 0`, at most
  `(1 + M + r) * q ^ (r - 1)` monic polynomials of degree `r` are not allowed labels.
* `TauCeti.SecondMoment.one_sub_le_ncard_isAllowedLabel_mul`: if `M ≠ 0` and
  `(1 + M + 2 * r) / q ≤ ε`, the allowed labels of degree `r` have total weight at least `1 - ε`
  when each polynomial of degree `r` has weight `(1 - r / q) / q ^ r`.

## References

* R. Lidl and H. Niederreiter, *Finite Fields* (1983), ch. 3, for the counts of squarefree and
  irreducible polynomials over a finite field.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `New/Spanning/MainTerm/BadTypes.lean`
  (`New.card_not_isAllowedPolynomial_le`, `New.one_sub_le_card_allowed_mul`), for the statements.
-/

public section

open Polynomial

namespace TauCeti.SecondMoment

section Defs

variable {R : Type*} [Semiring R]

/-- A *label* is a monic squarefree polynomial with nonzero constant term. -/
def IsLabel (f : R[X]) : Prop :=
  f.Monic ∧ Squarefree f ∧ f.coeff 0 ≠ 0

theorem isLabel_iff {f : R[X]} : IsLabel f ↔ f.Monic ∧ Squarefree f ∧ f.coeff 0 ≠ 0 :=
  Iff.rfl

/-- Every label is monic. -/
theorem IsLabel.monic {f : R[X]} (hf : IsLabel f) : f.Monic :=
  (isLabel_iff.mp hf).1

/-- A label is *allowed* for `M : ℕ` if it has no root `x` with `x ^ M = 1`. -/
def IsAllowedLabel (M : ℕ) (f : R[X]) : Prop :=
  IsLabel f ∧ ∀ x : R, x ^ M = 1 → ¬f.IsRoot x

theorem isAllowedLabel_iff {M : ℕ} {f : R[X]} :
    IsAllowedLabel M f ↔ IsLabel f ∧ ∀ x : R, x ^ M = 1 → ¬f.IsRoot x :=
  Iff.rfl

/-- Every allowed label is monic. -/
theorem IsAllowedLabel.monic {M : ℕ} {f : R[X]} (hf : IsAllowedLabel M f) : f.Monic :=
  (isAllowedLabel_iff.mp hf).1.monic

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
  refine (Finset.card_insert_le _ _).trans ?_
  rw [add_comm, nthRootsFinset_def]
  gcongr
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots M 1)

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
  set R : Z → Set K[X] := fun x ↦ {f : K[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot x}
  set Q := {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬Squarefree f}
  have hsub : {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f} ⊆ (⋃ x, R x) ∪ Q := by
    rintro f ⟨hf, hr, h⟩
    rcases isRoot_or_not_squarefree hM hf h with ⟨x, hx, hroot⟩ | hsq
    · exact .inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hf, hr, hroot⟩)
    · exact .inr ⟨hf, hr, hsq⟩
  have hfin : ((⋃ x, R x) ∪ Q).Finite :=
    (Set.finite_iUnion fun x : Z ↦ (finite_setOf_monic_natDegree_eq K r).subset
      fun (f : K[X]) (hf : f ∈ R x) ↦ ⟨hf.1, hf.2.1⟩).union
      ((finite_setOf_monic_natDegree_eq K r).subset fun (f : K[X]) (hf : f ∈ Q) ↦ ⟨hf.1, hf.2.1⟩)
  calc _ ≤ ((⋃ x, R x) ∪ Q).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (⋃ x, R x).ncard + Q.ncard := Set.ncard_union_le _ _
    _ ≤ ∑ x, (R x).ncard + r * Nat.card K ^ (r - 1) :=
        add_le_add (Set.ncard_iUnion_le_of_fintype R) (ncard_monic_not_squarefree_le r)
    _ ≤ ∑ _x : Z, Nat.card K ^ (r - 1) + r * Nat.card K ^ (r - 1) := by
        gcongr with x
        exact ncard_monic_isRoot_le _ r
    _ ≤ (1 + M + r) * Nat.card K ^ (r - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, add_mul]
        gcongr
        exact card_insert_zero_nthRootsFinset_le M

/-- The count of `TauCeti.SecondMoment.ncard_monic_not_isAllowedLabel_le` multiplied by `q`. -/
private lemma ncard_monic_not_isAllowedLabel_mul_le [Finite K] {M : ℕ} (hM : M ≠ 0) (r : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard * Nat.card K ≤
      (1 + M + r) * Nat.card K ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [setOf_monic_natDegree_zero_not_isAllowedLabel]
  · calc _ ≤ (1 + M + r) * Nat.card K ^ (r - 1) * Nat.card K :=
          Nat.mul_le_mul_right _ (ncard_monic_not_isAllowedLabel_le hM r)
      _ = (1 + M + r) * Nat.card K ^ r := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]

/-- **The allowed labels carry almost all the weight.** Over a finite field with `q` elements,
let each polynomial of degree `r` have weight `(1 - r / q) / q ^ r`. If `M ≠ 0` and
`(1 + M + 2 * r) / q ≤ ε`, then the allowed labels of degree `r` have total weight at least
`1 - ε`. No bound `1 < r < q` is needed: for `r > q` the weight is negative and the total is at
least `1 - r / q`. -/
theorem one_sub_le_ncard_isAllowedLabel_mul [Finite K] {M r : ℕ} (hM : M ≠ 0) {ε : ℝ}
    (hε : (1 + M + 2 * r) / Nat.card K ≤ ε) :
    1 - ε ≤ {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard *
      ((1 - r / Nat.card K) / (Nat.card K : ℝ) ^ r) := by
  set A := {f : K[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard
  set B := {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬IsAllowedLabel M f}.ncard
  have hAB : (A : ℝ) + B = (Nat.card K : ℝ) ^ r := by
    exact_mod_cast ncard_monic_pred_add_ncard_monic_not_pred K r (IsAllowedLabel M)
      (fun _ hf ↦ hf.monic)
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
