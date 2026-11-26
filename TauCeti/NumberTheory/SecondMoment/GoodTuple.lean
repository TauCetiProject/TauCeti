/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.PrimitivePolynomial
public import TauCeti.NumberTheory.SecondMoment.AllowedLabel
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Good tuples of labels and their weight

Let `k_w`, for `w` in a finite set `ι` with `f` elements, be finite fields with `q` elements, and
give every monic polynomial of degree `r` over `k_w` the weight `(1 - r / q) / q ^ r`, and a tuple
of such polynomials, one over each `k_w`, the product of their weights. For `M : ℕ`, a tuple of
labels is *good* if every label is allowed for `M` (`TauCeti.SecondMoment.IsAllowedLabel`) and
some label is a primitive polynomial (`Polynomial.IsPrimitivePolynomial`).

This file shows that, for `M ≠ 0`, `0 < r`, `(1 + M + 2r) / q ≤ ε ≤ 1` and
`2r (2r log q + 1) L ≤ f`, the good tuples of degree `r` miss a total weight of at most
`f ε + exp(-L)`. The allowed labels at one place weigh at least `1 - ε`
(`TauCeti.SecondMoment.one_sub_le_ncard_isAllowedLabel_mul`), and the monic polynomials at one place
that are not primitive weigh at most `exp(-u)` with `u = 1 / (2r (2r log q + 1))`
(`TauCeti.SecondMoment.ncard_monic_not_isPrimitivePolynomial_mul_le_exp`). The good tuples are the
tuples of allowed labels less those in which no label is primitive, so they weigh at least
`(1 - ε) ^ f - exp(-u) ^ f ≥ 1 - f ε - exp(-L)`.

The labels index characters of `GL_r` over finite fields, and in the second moment of Poincaré
series the weight `(1 - r / q) / q ^ r` is a lower bound for the coefficient at the identity of the
central idempotent of the character of a label; the weight bound here is the arithmetic part of
the bound for the share of the bad characters.

## Main definitions

* `TauCeti.SecondMoment.IsGoodTuple M c`: every `c w` is an allowed label for `M` and some `c w`
  is primitive.

## Main results

* `TauCeti.SecondMoment.ncard_monic_not_isPrimitivePolynomial_mul_le_exp`: the monic polynomials of
  degree `r` that are not primitive weigh at most `exp(-1 / (2r (2r log q + 1)))`.
* `TauCeti.SecondMoment.one_sub_ncard_isGoodTuple_mul_le`: the good tuples of degree `r` miss a
  total weight of at most `f ε + exp(-L)`.

## References

* R. Lidl and H. Niederreiter, *Finite Fields* (1983), ch. 3, for the counts of squarefree and
  primitive polynomials over a finite field.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `New/Spanning/MainTerm/BadTypes.lean`
  (`New.card_not_primitive_mul_le`, `New.re_coeff_one_sub_sum_tupleIdem_le`), for the statements
  and the argument.
-/

public section

open Polynomial

namespace TauCeti.SecondMoment

section Primitive

variable {K : Type*} [Field K] [Finite K]

/-- **The monic polynomials that are not primitive weigh little.** Over a finite field with `q`
elements, let each polynomial of degree `r` have weight `(1 - r / q) / q ^ r`. Then the monic
polynomials of degree `r` that are not primitive have total weight at most
`exp(-1 / (2r (2r log q + 1)))`. No bound `1 < r < q` is needed: for `r > q` the weight is
negative. -/
theorem ncard_monic_not_isPrimitivePolynomial_mul_le_exp (r : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬f.IsPrimitivePolynomial}.ncard *
        ((1 - r / Nat.card K) / (Nat.card K : ℝ) ^ r) ≤
      Real.exp (-(1 / (2 * r * (2 * r * Real.log (Nat.card K) + 1)))) := by
  set N := {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬f.IsPrimitivePolynomial}.ncard
  have hq : (0 : ℝ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
  have hN : (0 : ℝ) ≤ N / (Nat.card K : ℝ) ^ r := by positivity
  have hw : (N : ℝ) * ((1 - r / Nat.card K) / (Nat.card K : ℝ) ^ r) =
      N / (Nat.card K : ℝ) ^ r * (1 - r / Nat.card K) := by ring
  rw [hw]
  refine le_trans ?_ (ncard_monic_not_isPrimitivePolynomial_div_le_exp r)
  exact mul_le_of_le_one_right hN (sub_le_self _ (by positivity))

end Primitive

section Tuple

variable {ι : Type*} {K : ι → Type*} [∀ w, Field (K w)]

/-- A tuple `c` of polynomials, one over each field `K w`, is *good* for `M : ℕ` if every `c w`
is an allowed label for `M` (monic and squarefree, with nonzero constant term and no root `x`
with `x ^ M = 1`) and some `c w` is a primitive polynomial. -/
def IsGoodTuple (M : ℕ) (c : ∀ w, (K w)[X]) : Prop :=
  (∀ w, IsAllowedLabel M (c w)) ∧ ∃ w, (c w).IsPrimitivePolynomial

/-- Unfolding `TauCeti.SecondMoment.IsGoodTuple`. -/
theorem isGoodTuple_iff {M : ℕ} {c : ∀ w, (K w)[X]} :
    IsGoodTuple M c ↔ (∀ w, IsAllowedLabel M (c w)) ∧ ∃ w, (c w).IsPrimitivePolynomial :=
  Iff.rfl

variable [Fintype ι] [∀ w, Finite (K w)]

/-- The good tuples of degree `r` are the tuples of allowed labels of degree `r` less those in
which no label is primitive, so their number is the product of the numbers of allowed labels less
at most the product of the numbers of non-primitive monic polynomials. -/
private lemma prod_ncard_le_ncard_isGoodTuple_add (M r : ℕ) :
    ∏ w, ({f : (K w)[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard : ℝ) ≤
      {c : ∀ w, (K w)[X] | (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c}.ncard +
        ∏ w, ({f : (K w)[X] | f.Monic ∧ f.natDegree = r ∧ ¬f.IsPrimitivePolynomial}.ncard : ℝ) := by
  classical
  have hA (w : ι) : {f : (K w)[X] | f.natDegree = r ∧ IsAllowedLabel M f}.Finite :=
    (finite_setOf_monic_natDegree_eq (K w) r).subset fun _ hf ↦
      ⟨(isLabel_iff.mp (isAllowedLabel_iff.mp hf.2).1).1, hf.1⟩
  set sA : ∀ w, Finset (K w)[X] := fun w ↦ (hA w).toFinset
  set sB : ∀ w, Finset (K w)[X] := fun w ↦ (sA w).filter fun f ↦ ¬f.IsPrimitivePolynomial
  have hgood : {c : ∀ w, (K w)[X] | (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c} =
      ↑(Fintype.piFinset sA \ Fintype.piFinset sB) := by
    ext c
    simp only [isGoodTuple_iff, Set.mem_ofPred_eq, Finset.coe_sdiff, Fintype.coe_piFinset,
      Set.Finite.coe_toFinset, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_sdiff,
      Set.mem_pi, Set.mem_univ, forall_const, forall_and, not_forall, not_and, not_not, sA, sB]
    tauto
  have hsub : Fintype.piFinset sB ⊆ Fintype.piFinset sA :=
    Fintype.piFinset_subset _ _ fun w ↦ Finset.filter_subset _ _
  have hcard : (Fintype.piFinset sA \ Fintype.piFinset sB).card + (Fintype.piFinset sB).card =
      ∏ w, (sA w).card := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.sub_add_cancel (Finset.card_le_card hsub),
      Fintype.card_piFinset]
  have hB (w : ι) : (sB w).card ≤
      {f : (K w)[X] | f.Monic ∧ f.natDegree = r ∧ ¬f.IsPrimitivePolynomial}.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard (fun f hf ↦ ?_)
      ((finite_setOf_monic_natDegree_eq (K w) r).subset fun _ hf ↦ ⟨hf.1, hf.2.1⟩)
    simp only [sB, sA, Finset.coe_filter, Set.Finite.mem_toFinset] at hf
    exact ⟨(isLabel_iff.mp (isAllowedLabel_iff.mp hf.1.2).1).1, hf.1.1, hf.2⟩
  rw [hgood, Set.ncard_coe_finset]
  have hA' : ∏ w, {f : (K w)[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard =
      ∏ w, (sA w).card :=
    Finset.prod_congr rfl fun w _ ↦ Set.ncard_eq_toFinset_card _ (hA w)
  rw [← Nat.cast_prod, hA', ← hcard, Nat.cast_add, Fintype.card_piFinset, Nat.cast_prod]
  gcongr with w
  exact_mod_cast hB w

/-- The weight `(1 - r / q) / q ^ r` is nonnegative when `(1 + M + 2r) / q ≤ 1`. -/
private lemma weight_nonneg {q : ℝ} {M r : ℕ} (hq : 0 < q) (h : (1 + M + 2 * r) / q ≤ 1) :
    0 ≤ (1 - r / q) / q ^ r := by
  have hMr : (1 + M + 2 * r : ℝ) ≤ q := (div_le_one hq).mp h
  have hrq : (r : ℝ) / q ≤ 1 := (div_le_one hq).mpr (by linarith [M.cast_nonneg (α := ℝ)])
  exact div_nonneg (by linarith) (by positivity)

/-- **The good tuples carry almost all the weight.** Let `K w`, for `w` in a finite set `ι` with
`f` elements, be finite fields with `q` elements. Give every polynomial of degree `r` the weight
`(1 - r / q) / q ^ r`, and a tuple of polynomials, one over each `K w`, the product
`((1 - r / q) / q ^ r) ^ f` of their weights. If `M ≠ 0`, `0 < r`, `(1 + M + 2r) / q ≤ ε ≤ 1` and
`2r (2r log q + 1) L ≤ f`, then the good tuples of degree `r` have total weight at least
`1 - (f ε + exp(-L))`. -/
theorem one_sub_ncard_isGoodTuple_mul_le {q M r : ℕ} {ε L : ℝ} (hK : ∀ w, Nat.card (K w) = q)
    (hM : M ≠ 0) (hr : 0 < r) (hε : (1 + M + 2 * r) / q ≤ ε) (hε1 : ε ≤ 1)
    (hL : 2 * r * (2 * r * Real.log q + 1) * L ≤ Fintype.card ι) :
    1 - {c : ∀ w, (K w)[X] | (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c}.ncard *
        ((1 - r / q) / (q : ℝ) ^ r) ^ Fintype.card ι ≤
      Fintype.card ι * ε + Real.exp (-L) := by
  set wt : ℝ := (1 - r / q) / (q : ℝ) ^ r
  set u : ℝ := 1 / (2 * r * (2 * r * Real.log q + 1))
  set A : ι → ℕ := fun w ↦ {f : (K w)[X] | f.natDegree = r ∧ IsAllowedLabel M f}.ncard
  set B : ι → ℕ := fun w ↦
    {f : (K w)[X] | f.Monic ∧ f.natDegree = r ∧ ¬f.IsPrimitivePolynomial}.ncard
  -- The bounds at one place; the weight is nonnegative since `2r < q`.
  have hwt (w : ι) : 0 ≤ wt :=
    weight_nonneg (hK w ▸ Nat.cast_pos.mpr Nat.card_pos) (hε.trans hε1)
  have hA (w : ι) : 1 - ε ≤ A w * wt := by
    have := one_sub_le_ncard_isAllowedLabel_mul (K := K w) (r := r) hM (ε := ε) (by rwa [hK w])
    rwa [hK w] at this
  have hB (w : ι) : B w * wt ≤ Real.exp (-u) := by
    have := ncard_monic_not_isPrimitivePolynomial_mul_le_exp (K := K w) r
    rwa [hK w] at this
  -- The good tuples weigh at least `∏ (A w * wt) - ∏ (B w * wt)`.
  have hwtf : 0 ≤ wt ^ Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with h | ⟨⟨w⟩⟩
    · simp [Fintype.card_eq_zero]
    · exact pow_nonneg (hwt w) _
  have hG : ∏ w, ((A w : ℝ) * wt) - ∏ w, ((B w : ℝ) * wt) ≤
      {c : ∀ w, (K w)[X] | (∀ w, (c w).natDegree = r) ∧ IsGoodTuple M c}.ncard *
        wt ^ Fintype.card ι := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← sub_mul]
    exact mul_le_mul_of_nonneg_right
      (by linarith [prod_ncard_le_ncard_isGoodTuple_add (K := K) M r]) hwtf
  -- The allowed tuples weigh at least `(1 - ε) ^ f ≥ 1 - f ε`.
  have h1 : 1 - Fintype.card ι * ε ≤ ∏ w, ((A w : ℝ) * wt) := by
    calc 1 - Fintype.card ι * ε = 1 + Fintype.card ι * (-ε) := by ring
      _ ≤ (1 + -ε) ^ Fintype.card ι := one_add_mul_le_pow (by linarith) _
      _ = ∏ _w : ι, (1 - ε) := by rw [Finset.prod_const, Finset.card_univ, ← sub_eq_add_neg]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ by linarith) fun w _ ↦ hA w
  -- The tuples with no primitive label weigh at most `exp(-u) ^ f ≤ exp(-L)`.
  have hD : 0 < 2 * (r : ℝ) * (2 * r * Real.log q + 1) := by
    have := Real.log_natCast_nonneg q
    have : (0 : ℝ) < r := Nat.cast_pos.mpr hr
    positivity
  have h2 : ∏ w, ((B w : ℝ) * wt) ≤ Real.exp (-L) := by
    calc ∏ w, ((B w : ℝ) * wt) ≤ ∏ _w : ι, Real.exp (-u) :=
          Finset.prod_le_prod₀ (fun w _ ↦ mul_nonneg (Nat.cast_nonneg _) (hwt w)) fun w _ ↦ hB w
      _ = Real.exp (-(u * Fintype.card ι)) := by
          rw [Finset.prod_const, Finset.card_univ, ← neg_mul, Real.exp_mul_natCast]
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (neg_le_neg ?_)
    rw [one_div_mul_eq_div, le_div_iff₀ hD]
    linarith
  linarith

end Tuple

end TauCeti.SecondMoment
