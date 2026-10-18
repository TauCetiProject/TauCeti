/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Thom.Roots
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.RootCount
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Thom
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.FieldTheory.RealClosure.AbstractRolle
import TauCeti.RingTheory.Polynomial.Reductum
import TauCeti.RingTheory.Polynomial.Subresultant.CauchyIndex

/-!
# Semialgebraic Thom encodings and ordered-root regions in polynomial families

For any polynomial family `P : (MvPolynomial σ R)[X]` whose coefficients are polynomial functions
of parameters `x : σ → R`, every Tarski query of a polynomial family `Q` at the roots of the
specialization of `P` is determined by finitely many signs of polynomial functions of `x`. On the
stratum where `P.map (MvPolynomial.eval x)` has degree `d`, multiplying both inputs by the leading
coefficient of `P.reductum (d + 1)` makes the left leading coefficient positive without changing the
distinct roots, so the Tarski query is the permanences minus variations of fixed-bound signed
principal subresultant coefficients
(`Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc_C_leadingCoeff_mul`).
Consequently any condition on finitely many Tarski queries is semialgebraic, with no monicity or
degree-preservation hypothesis.

Applying the Ben-Or–Kozen–Reif sign-moment inverse to the products of consecutive derivatives gives
a uniform coefficient-sign description of each realized Thom encoding, of its position in the order
of distinct roots, and of the comparison (`=`, `<`, `>`) between a polynomial threshold `T(x)` and
the root with a prescribed Thom encoding or a prescribed root index. In cylinder coordinates over
`R ^ n`, this describes the regions strictly below and strictly above the `i`-th distinct root.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval_eq`: one Tarski-query fiber is semialgebraic.
* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval`: any condition on finitely many Tarski
  queries is semialgebraic.
* `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq`,
  `TauCeti.isSemialgebraic_setOf_exists_root_derivative_signs_eq`: realization of a prescribed
  derivative-sign word by a root of the specialization.
* `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_eq`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_lt`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_lt_eval`: comparison of a
  polynomial evaluation `T(x)` with a Thom-encoded root.
* `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt`: realization of a
  Thom encoding by the `i`-th distinct root.
* `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt`,
  `TauCeti.isSemialgebraic_setOf_lt_root_card_roots_lt`,
  `TauCeti.isSemialgebraic_setOf_gt_root_card_roots_lt`: the graph and the regions strictly below
  and strictly above the `i`-th distinct root.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapters 4 and 10.
-/

public section

open Polynomial Set
open scoped Matrix

namespace TauCeti

variable {σ R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Uniform Tarski-query fiber.** The parameters at which a Tarski query of two specializations of
polynomial families has a prescribed value form a semialgebraic set. No monicity or
degree-preservation hypothesis is required. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval_eq
    (P Q : (MvPolynomial σ R)[X]) (c : ℤ) :
    IsSemialgebraic {x : σ → R |
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} := by
  let s : ℕ → ℕ → MvPolynomial σ R := fun d =>
    signedPsc (C ((P.reductum (d + 1)).coeff d) * P.reductum (d + 1))
      (C ((P.reductum (d + 1)).coeff d) * (derivative (P.reductum (d + 1)) * Q))
      d (d + Q.natDegree)
  have hquery (x : σ → R) {d : ℕ} (hd : (P.map (MvPolynomial.eval x)).natDegree = d) :
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) =
        (((List.range (d + 1)).reverse.map (s d)).map
          (MvPolynomial.eval x)).permanencesMinusVariations := by
    have hP : P.map (MvPolynomial.eval x) = (P.reductum (d + 1)).map (MvPolynomial.eval x) := by
      rw [← hd, map_reductum_natDegree_map_add_one]
    have hhp : (P.map (MvPolynomial.eval x)).natDegree ≤ d + Q.natDegree := by omega
    have hhq : (derivative (P.map (MvPolynomial.eval x)) *
        Q.map (MvPolynomial.eval x)).natDegree ≤ d + Q.natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add
        ((natDegree_derivative_le _).trans (by omega)) natDegree_map_le)
    rw [tarskiQuery_eq_permanencesMinusVariations_signedPsc_C_leadingCoeff_mul hhp hhq,
      ← coeff_natDegree, hd, hP]
    have hs : signedPsc
        (C (((P.reductum (d + 1)).map (MvPolynomial.eval x)).coeff d) *
          (P.reductum (d + 1)).map (MvPolynomial.eval x))
        (C (((P.reductum (d + 1)).map (MvPolynomial.eval x)).coeff d) *
          (derivative ((P.reductum (d + 1)).map (MvPolynomial.eval x)) *
            Q.map (MvPolynomial.eval x)))
        d (d + Q.natDegree) = fun j => MvPolynomial.eval x (s d j) := by
      funext j
      simpa only [s, coeff_map, map_C, Polynomial.map_mul, derivative_map] using
        signedPsc_map_map (MvPolynomial.eval x)
          (C ((P.reductum (d + 1)).coeff d) * P.reductum (d + 1))
          (C ((P.reductum (d + 1)).coeff d) * (derivative (P.reductum (d + 1)) * Q))
          d (d + Q.natDegree) j
    rw [hs, List.map_map]
    rfl
  have hset : {x : σ → R |
        tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} =
      ⋃ d ∈ Iic P.natDegree,
        {x | (P.map (MvPolynomial.eval x)).natDegree = d} ∩
          {x | (((List.range (d + 1)).reverse.map (s d)).map
            (MvPolynomial.eval x)).permanencesMinusVariations = c} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Iic, exists_prop]
    constructor
    · intro hx
      refine ⟨_, natDegree_map_le, rfl, ?_⟩
      rwa [← hquery x rfl]
    · rintro ⟨d, -, hd, hc⟩
      rwa [hquery x hd]
  rw [hset]
  exact .biUnion (finite_Iic _) fun d _ =>
    (isSemialgebraic_setOf_natDegree_map_eval_eq P d).inter
      (isSemialgebraic_setOf_permanencesMinusVariations_eval _ _)

/-- Any condition on finitely many Tarski queries of a polynomial family is semialgebraic. The
queries have a common finite range bounded by the formal degree of `P`, so the condition is a
finite union of intersections of query fibers. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval
    {ι : Type*} [Finite ι] (P : (MvPolynomial σ R)[X])
    (Q : ι → (MvPolynomial σ R)[X]) (Φ : (ι → ℤ) → Prop) :
    IsSemialgebraic {x : σ → R |
      Φ fun i => tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))} := by
  let V := Set.Icc (-(P.natDegree : ℤ)) (P.natDegree : ℤ)
  have hmem (x : σ → R) (i : ι) :
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x)) ∈ V := by
    have hdeg : ((P.map (MvPolynomial.eval x)).natDegree : ℤ) ≤ P.natDegree := by
      exact_mod_cast natDegree_map_le
    have hq := Polynomial.tarskiQuery_mem_Icc_natDegree
      (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))
    exact ⟨(neg_le_neg hdeg).trans hq.1, hq.2.trans hdeg⟩
  have hset : {x : σ → R |
        Φ fun i => tarskiQuery (P.map (MvPolynomial.eval x))
          (Q i |>.map (MvPolynomial.eval x))} =
      ⋃ v ∈ {v : ι → V | Φ fun i => (v i : ℤ)},
        ⋂ i, {x | tarskiQuery (P.map (MvPolynomial.eval x))
          (Q i |>.map (MvPolynomial.eval x)) = v i} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
    constructor
    · intro hx
      let v : ι → V := fun i => ⟨_, hmem x i⟩
      exact ⟨v, hx, fun _ => rfl⟩
    · rintro ⟨v, hv, heq⟩
      convert hv using 1
      funext i
      exact heq i
  rw [hset]
  exact .biUnion (toFinite _) fun v _ => .iInter fun i =>
    isSemialgebraic_setOf_tarskiQuery_map_eval_eq P (Q i) (v i)

/-- Two distinct roots of `P.map (MvPolynomial.eval x)` with the same consecutive derivative signs
of orders `1, …, P.natDegree` are equal. -/
private theorem eq_of_mem_roots_derivative_signs_eq {P : (MvPolynomial σ R)[X]} {x : σ → R}
    {τ : Fin P.natDegree → SignType} {r r' : R}
    (hr : r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset)
    (hr' : r' ∈ (P.map (MvPolynomial.eval x)).roots.toFinset)
    (hτ : ∀ j : Fin P.natDegree,
      SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r) = τ j)
    (hτ' : ∀ j : Fin P.natDegree,
      SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r') = τ j) :
    r = r' := by
  have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
  refine Polynomial.eq_of_derivativeSign_succ_eq_of_natDegree_le natDegree_map_le
    RealClosure.polynomialRolle_of_isRealClosed hp
    (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
    (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr')) ?_
  funext j
  simpa only [Polynomial.derivativeSign_def, iterate_derivative_map] using
    (hτ j).trans (hτ' j).symm

/-- At any specialization `P.map (MvPolynomial.eval x)`, the `τ`-entry of the BKR sign-moment
inverse applied to the Tarski queries of products of consecutive derivatives equals `1` exactly
when `P.map (MvPolynomial.eval x)` has a distinct root with derivative signs `τ`. -/
private theorem fullInverse_mulVec_tarskiQuery_derivative_eq_one_iff
    (P : (MvPolynomial σ R)[X]) (x : σ → R) (τ : Fin P.natDegree → SignType) :
    (SignDetermination.fullInverse (Fin P.natDegree) *ᵥ
      fun e : Fin P.natDegree → Fin 3 =>
        (tarskiQuery (P.map (MvPolynomial.eval x))
          ((∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val).map
            (MvPolynomial.eval x)) : ℚ)) τ = 1 ↔
      ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
        ∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j := by
  have hQ (e : Fin P.natDegree → Fin 3) :
      (∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val).map
        (MvPolynomial.eval x) =
      ∏ j : Fin P.natDegree,
        ((derivative^[j.val + 1] P).map (MvPolynomial.eval x)) ^ (e j).val := by
    simp [Polynomial.map_prod]
  simp only [hQ, Polynomial.fullInverse_mulVec_tarskiQuery]
  rw [Finset.signCount_eq_occCount, Function.occCount_of_injective]
  · simp only [Subtype.exists, exists_prop, funext_iff, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  · intro a b hab
    exact Subtype.ext (eq_of_mem_roots_derivative_signs_eq a.property b.property
      (congrFun hab) (fun _ => rfl))

/-- **Uniform Thom-encoding realization.** For a prescribed sign word `τ`, the parameters at which
the specialized polynomial is nonzero and has a root with consecutive derivative signs `τ` form a
semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq
    (P : (MvPolynomial σ R)[X]) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      ∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j} := by
  let Q : (Fin P.natDegree → Fin 3) → (MvPolynomial σ R)[X] := fun e =>
    ∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val
  convert isSemialgebraic_setOf_tarskiQuery_map_eval P Q
    (fun v => (SignDetermination.fullInverse (Fin P.natDegree) *ᵥ
      fun e => (v e : ℚ)) τ = 1) using 1
  ext x
  exact (fullInverse_mulVec_tarskiQuery_derivative_eq_one_iff P x τ).symm

/-- **Uniform derivative-sign realization at a zero.** For a prescribed sign word `τ`, the
parameters at which the specialized polynomial has a zero with consecutive derivative signs `τ` form
a semialgebraic set. Zero specializations have all derivatives zero and contribute when `τ = 0`. -/
theorem isSemialgebraic_setOf_exists_root_derivative_signs_eq
    (P : (MvPolynomial σ R)[X]) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r : R,
      (P.map (MvPolynomial.eval x)).eval r = 0 ∧
        ∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j} := by
  have hset : {x : σ → R | ∃ r : R,
        (P.map (MvPolynomial.eval x)).eval r = 0 ∧
          ∀ j : Fin P.natDegree,
            SignType.sign (((derivative^[j.val + 1] P).map
              (MvPolynomial.eval x)).eval r) = τ j} =
      {x | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
        ∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j} ∪
        {x | P.map (MvPolynomial.eval x) = 0 ∧ τ = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_union]
    by_cases hp : P.map (MvPolynomial.eval x) = 0
    · simp only [hp, roots_zero, Multiset.toFinset_zero, Finset.notMem_empty, false_and,
        exists_false, eval_zero, true_and, false_or, ← iterate_derivative_map,
        iterate_derivative_zero, sign_zero, funext_iff, Pi.zero_apply]
      exact ⟨fun ⟨_, h⟩ => fun j => (h j).symm, fun h => ⟨0, fun j => (h j).symm⟩⟩
    · simp [hp, Polynomial.mem_roots hp]
  rw [hset]
  refine (isSemialgebraic_setOf_mem_roots_derivative_signs_eq P τ).union ?_
  by_cases hτ : τ = 0
  · simpa [hτ] using isSemialgebraic_setOf_map_eval_eq_zero P
  · simp [hτ]

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **Equality with a Thom-encoded root.** For a polynomial `T` and sign word `τ`, the parameters
`x` at which `P.map (MvPolynomial.eval x)` has a root `r ∈ roots.toFinset` with derivative signs
`τ` and `MvPolynomial.eval x T = r` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_eq
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      (∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j) ∧
        MvPolynomial.eval x T = r} := by
  convert (isSemialgebraic_setOf_map_eval_eq_zero P).compl.inter
    ((isSemialgebraic_eval_eq_zero (P.eval T)).inter
      (isSemialgebraic_setOf_sign_eval
        (fun j : Fin P.natDegree => (derivative^[j.val + 1] P).eval T) (· = τ))) using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, Multiset.mem_toFinset,
    ← eval_map_apply, funext_iff]
  constructor
  · rintro ⟨r, hr, hτ, rfl⟩
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
    exact ⟨hp, (Polynomial.mem_roots hp).mp hr, hτ⟩
  · rintro ⟨hp, hr, hτ⟩
    exact ⟨MvPolynomial.eval x T, (Polynomial.mem_roots hp).mpr hr, hτ, rfl⟩

/-- **Strict inequality below a Thom-encoded root.** For a polynomial `T` and sign word `τ`, the
parameters `x` at which `P.map (MvPolynomial.eval x)` has a root `r ∈ roots.toFinset` with
derivative signs `τ` and `MvPolynomial.eval x T < r` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_lt
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      (∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j) ∧
        MvPolynomial.eval x T < r} := by
  convert (isSemialgebraic_setOf_mem_roots_derivative_signs_eq P τ).inter
    (isSemialgebraic_setOf_sign_eval
      (fun i : Fin (P.natDegree + 1) => (derivative^[i.val] P).eval T)
      (fun υ => ThomLT υ (Fin.cons 0 τ))) using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, ← eval_map_apply, ← iterate_derivative_map,
    ← Polynomial.derivativeSign_def]
  constructor
  · rintro ⟨r, hr, hτ, hlt⟩
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
    have hr0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    rw [Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_right natDegree_map_le
      RealClosure.polynomialRolle_of_isRealClosed hp hr0, funext hτ] at hlt
    exact ⟨⟨r, hr, hτ⟩, hlt⟩
  · rintro ⟨⟨r, hr, hτ⟩, hlt⟩
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
    have hr0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    rw [← funext hτ, ← Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_right
      natDegree_map_le RealClosure.polynomialRolle_of_isRealClosed hp hr0] at hlt
    exact ⟨r, hr, hτ, hlt⟩

/-- **Strict inequality above a Thom-encoded root.** For a polynomial `T` and sign word `τ`, the
parameters `x` at which `P.map (MvPolynomial.eval x)` has a root `r ∈ roots.toFinset` with
derivative signs `τ` and `r < MvPolynomial.eval x T` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_lt_eval
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      (∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j) ∧
        r < MvPolynomial.eval x T} := by
  convert (isSemialgebraic_setOf_mem_roots_derivative_signs_eq P τ).inter
    (isSemialgebraic_setOf_sign_eval
      (fun i : Fin (P.natDegree + 1) => (derivative^[i.val] P).eval T)
      (fun υ => ThomLT (Fin.cons 0 τ) υ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, ← eval_map_apply, ← iterate_derivative_map,
    ← Polynomial.derivativeSign_def]
  constructor
  · rintro ⟨r, hr, hτ, hlt⟩
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
    have hr0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    rw [Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_left natDegree_map_le
      RealClosure.polynomialRolle_of_isRealClosed hp hr0, funext hτ] at hlt
    exact ⟨⟨r, hr, hτ⟩, hlt⟩
  · rintro ⟨⟨r, hr, hτ⟩, hlt⟩
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := fun hp => by simp [hp] at hr
    have hr0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    rw [← funext hτ, ← Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_left
      natDegree_map_le RealClosure.polynomialRolle_of_isRealClosed hp hr0] at hlt
    exact ⟨r, hr, hτ, hlt⟩

/-- **Thom-encoding realization with prescribed root index.** For a sign word `τ` and index `i`,
the parameters `x` at which `P.map (MvPolynomial.eval x)` has a root `r ∈ roots.toFinset` with
derivative signs `τ` and with exactly `i` distinct roots strictly below `r` form a semialgebraic
set. -/
theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt
    (P : (MvPolynomial σ R)[X]) (τ : Fin P.natDegree → SignType) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      (∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j) ∧
        {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i} := by
  classical
  let Q : (Fin P.natDegree → Fin 3) → (MvPolynomial σ R)[X] := fun e =>
    ∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val
  let realized (v : (Fin P.natDegree → Fin 3) → ℤ) (υ : Fin P.natDegree → SignType) : Prop :=
    (SignDetermination.fullInverse (Fin P.natDegree) *ᵥ fun e => (v e : ℚ)) υ = 1
  convert isSemialgebraic_setOf_tarskiQuery_map_eval P Q
    (fun v => realized v τ ∧
      (Finset.univ.filter fun υ => ThomLT υ τ ∧ realized v υ).card = i) using 1
  ext x
  simp only [mem_ofPred_eq, realized, Q, fullInverse_mulVec_tarskiQuery_derivative_eq_one_iff]
  have hcard_eq {r : R} (hr : r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset)
      (hτ : ∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r) = τ j) :
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card =
        (Finset.univ.filter fun υ : Fin P.natDegree → SignType =>
          ThomLT υ τ ∧ ∃ r' ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
            ∀ j : Fin P.natDegree,
              SignType.sign (((derivative^[j.val + 1] P).map
                (MvPolynomial.eval x)).eval r') = υ j).card := by
    have hr0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    have hτ' : (fun j : Fin P.natDegree =>
        derivativeSign (P.map (MvPolynomial.eval x)) r (j.val + 1)) = τ := by
      funext j
      simpa only [Polynomial.derivativeSign_def, iterate_derivative_map] using hτ j
    rw [Polynomial.card_roots_lt_eq_card_filter_thomLT_of_natDegree_le natDegree_map_le
      RealClosure.polynomialRolle_of_isRealClosed hr0 hτ']
    congr 1
    ext υ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Polynomial.derivativeSign_def,
      iterate_derivative_map, funext_iff]
  exact ⟨fun ⟨r, hr, hτ, hcard⟩ => ⟨⟨r, hr, hτ⟩, (hcard_eq hr hτ).symm.trans hcard⟩,
    fun ⟨⟨r, hr, hτ⟩, hcard⟩ => ⟨r, hr, hτ, (hcard_eq hr hτ).trans hcard⟩⟩

/-- **Equality with the `i`-th distinct root.** For polynomials `P` and `T`, the parameters `x` at
which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r` (with `i` distinct roots
strictly below `r`) and `MvPolynomial.eval x T = r` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        MvPolynomial.eval x T = r} := by
  convert IsSemialgebraic.iUnion (fun τ : Fin P.natDegree → SignType =>
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt P τ i).inter
      (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_eq P T τ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨r, hr, hcard, hT⟩ =>
    ⟨fun j => SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r),
      ⟨r, hr, fun _ => rfl, hcard⟩, ⟨r, hr, fun _ => rfl, hT⟩⟩,
    fun ⟨_, ⟨r, hr, hτ, hcard⟩, ⟨r', hr', hτ', hT⟩⟩ =>
      ⟨r, hr, hcard, eq_of_mem_roots_derivative_signs_eq hr hr' hτ hτ' ▸ hT⟩⟩

/-- **Region where a polynomial lies strictly below the `i`-th distinct root.** For polynomials `P`
and `T`, the parameters `x` at which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r`
and `MvPolynomial.eval x T < r` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        MvPolynomial.eval x T < r} := by
  convert IsSemialgebraic.iUnion (fun τ : Fin P.natDegree → SignType =>
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt P τ i).inter
      (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_lt P T τ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨r, hr, hcard, hlt⟩ =>
    ⟨fun j => SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r),
      ⟨r, hr, fun _ => rfl, hcard⟩, ⟨r, hr, fun _ => rfl, hlt⟩⟩,
    fun ⟨_, ⟨r, hr, hτ, hcard⟩, ⟨r', hr', hτ', hlt⟩⟩ =>
      ⟨r, hr, hcard, eq_of_mem_roots_derivative_signs_eq hr hr' hτ hτ' ▸ hlt⟩⟩

/-- **Region where a polynomial lies strictly above the `i`-th distinct root.** For polynomials `P`
and `T`, the parameters `x` at which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r`
and `r < MvPolynomial.eval x T` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        r < MvPolynomial.eval x T} := by
  convert IsSemialgebraic.iUnion (fun τ : Fin P.natDegree → SignType =>
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt P τ i).inter
      (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_lt_eval P T τ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨r, hr, hcard, hlt⟩ =>
    ⟨fun j => SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r),
      ⟨r, hr, fun _ => rfl, hcard⟩, ⟨r, hr, fun _ => rfl, hlt⟩⟩,
    fun ⟨_, ⟨r, hr, hτ, hcard⟩, ⟨r', hr', hτ', hlt⟩⟩ =>
      ⟨r, hr, hcard, eq_of_mem_roots_derivative_signs_eq hr hr' hτ hτ' ▸ hlt⟩⟩

variable {n : ℕ}

/-- **The graph of the `i`-th distinct root in cylinder coordinates.** The points of `R ^ (n + 1)`
whose coordinate `0` is the `i`-th distinct root of the specialization of `P` at the remaining
coordinates form a semialgebraic set. Zero specializations have no roots in `Polynomial.roots` and
contribute nothing. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt
    (P : (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      y 0 ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset ∧
        {z ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | z < y 0}.card = i} := by
  set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq Q (MvPolynomial.X 0) i using 1
  ext y
  simp only [mem_ofPred_eq, Q, map_eval_map_rename, MvPolynomial.eval_X, Fin.tail_def,
    Function.comp_def]
  exact ⟨fun ⟨hy, hcard⟩ => ⟨y 0, hy, hcard, rfl⟩,
    fun ⟨_, hr, hcard, h⟩ => h ▸ ⟨hr, hcard⟩⟩

/-- **The region strictly below the `i`-th distinct root in cylinder coordinates.** The points of
`R ^ (n + 1)` whose coordinate `0` lies strictly below the `i`-th distinct root of the
specialization of `P` at the remaining coordinates form a semialgebraic set. -/
theorem isSemialgebraic_setOf_lt_root_card_roots_lt
    (P : (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      ∃ r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset,
        {z ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | z < r}.card = i ∧
          y 0 < r} := by
  set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt Q (MvPolynomial.X 0) i using 1
  ext y
  simp only [mem_ofPred_eq, Q, map_eval_map_rename, MvPolynomial.eval_X, Fin.tail_def,
    Function.comp_def]

/-- **The region strictly above the `i`-th distinct root in cylinder coordinates.** The points of
`R ^ (n + 1)` whose coordinate `0` lies strictly above the `i`-th distinct root of the
specialization of `P` at the remaining coordinates form a semialgebraic set. -/
theorem isSemialgebraic_setOf_gt_root_card_roots_lt
    (P : (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      ∃ r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset,
        {z ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | z < r}.card = i ∧
          r < y 0} := by
  set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval Q (MvPolynomial.X 0) i using 1
  ext y
  simp only [mem_ofPred_eq, Q, map_eval_map_rename, MvPolynomial.eval_X, Fin.tail_def,
    Function.comp_def]

end TauCeti
