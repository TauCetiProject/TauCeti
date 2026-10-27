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

For a polynomial whose coefficients are polynomial functions of parameters, every Tarski query
of a polynomial family is determined by finitely many signs of polynomial functions of the
parameters. Consequently any condition on finitely many such queries is semialgebraic.

The monic case reads the query off signed principal subresultant coefficients of a remainder,
since remainder by a monic polynomial commutes with every coefficient specialization. An
arbitrary root family is reduced to it on each stratum of the specialized degree `d`: there the
family agrees with its reductum below degree `d + 1`, whose leading coefficient does not vanish,
and `Polynomial.integralNormalization` clears that leading coefficient. The parameters at which
the root family specializes to zero form a separate stratum, on which every query is zero.

Applying the Ben-Or–Kozen–Reif sign-moment inverse to the products of consecutive derivatives gives
a uniform coefficient-sign description of each realized Thom encoding, of its position in the order
of distinct roots, and of the strict comparisons (`<`, `>`) between a polynomial threshold `T(x)`
and the root with a prescribed Thom encoding or a prescribed root index. Equality with a
Thom-encoded root follows directly from polynomial sign conditions. Equality with a prescribed
root index is given by `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq` in
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.RootCount`. In cylinder coordinates over `R ^ n`,
this file describes the regions strictly below and strictly above the `i`-th distinct root.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval_eq`: one Tarski-query fiber is semialgebraic.
* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval`: any condition on finitely many Tarski
  queries is semialgebraic.
* `TauCeti.isSemialgebraic_setOf_exists_root_derivative_signs_eq`: realization of a prescribed
  derivative-sign word by a root of the specialization.
* `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_eq`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_lt`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_lt_eval`: comparison of a
  polynomial evaluation `T(x)` with a Thom-encoded root.
* `TauCeti.isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt`: realization of a
  Thom encoding by the `i`-th distinct root.
* `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt`,
  `TauCeti.isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval`,
  `TauCeti.isSemialgebraic_setOf_lt_root_card_roots_lt`,
  `TauCeti.isSemialgebraic_setOf_gt_root_card_roots_lt`: the regions strictly below
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

section Domain

variable {σ R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

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
    have hp : P.map (MvPolynomial.eval x) ≠ 0 := Polynomial.ne_zero_of_mem_roots hr
    exact ⟨hp, (Polynomial.mem_roots hp).mp hr, hτ⟩
  · rintro ⟨hp, hr, hτ⟩
    exact ⟨MvPolynomial.eval x T, (Polynomial.mem_roots hp).mpr hr, hτ, rfl⟩

end Domain

variable {σ R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- On the parameters where `P` specializes to a nonzero polynomial of degree `d`, its Tarski
queries are those of the monic family obtained by clearing the leading coefficient of the reductum
of `P` below degree `d + 1`. -/
private theorem tarskiQuery_map_eval_eq_integralNormalization {P : (MvPolynomial σ R)[X]}
    (Q : (MvPolynomial σ R)[X]) {x : σ → R} {d : ℕ} (hx : P.map (MvPolynomial.eval x) ≠ 0)
    (hd : (P.map (MvPolynomial.eval x)).natDegree = d) :
    tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) =
      tarskiQuery ((P.reductum (d + 1)).integralNormalization.map (MvPolynomial.eval x))
        ((C ((P.reductum (d + 1)).leadingCoeff ^ Q.natDegree) *
          Q.scaleRoots (P.reductum (d + 1)).leadingCoeff).map (MvPolynomial.eval x)) := by
  set a := (P.reductum (d + 1)).leadingCoeff
  have hmap : (P.reductum (d + 1)).map (MvPolynomial.eval x) = P.map (MvPolynomial.eval x) := by
    simpa only [hd] using map_reductum_natDegree_map_add_one (MvPolynomial.eval x) P
  have hdeg : ((P.reductum (d + 1)).map (MvPolynomial.eval x)).natDegree =
      (P.reductum (d + 1)).natDegree := by
    have h := natDegree_reductum_natDegree_map_add_one (MvPolynomial.eval x) P
    rw [hd] at h
    rw [h, hmap, hd]
  have hlc : (P.map (MvPolynomial.eval x)).leadingCoeff = MvPolynomial.eval x a := by
    simp only [← hmap, a, leadingCoeff, coeff_map, hdeg]
  have ha : MvPolynomial.eval x a ≠ 0 := hlc ▸ leadingCoeff_ne_zero.mpr hx
  rw [← integralNormalization_map _ _ ha, hmap,
    tarskiQuery_integralNormalization hx fun z _ => ?_]
  rw [hlc, eval_map, sign_eval₂_C_pow_mul_scaleRoots _ _ ha, eval_map]

variable [IsRealClosed R]

/-- The parameters at which a Tarski query of two specializations of polynomial families has a
prescribed value form a semialgebraic set, provided the root family is monic. -/
private theorem isSemialgebraic_setOf_tarskiQuery_map_eval_eq_of_monic
    (P Q : (MvPolynomial σ R)[X]) (hP : P.Monic) (c : ℤ) :
    IsSemialgebraic {x : σ → R |
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} := by
  let H : (MvPolynomial σ R)[X] := (P.derivative * Q) %ₘ P
  let s : ℕ → ℕ → MvPolynomial σ R := fun e =>
    signedPsc P (H.reductum (e + 1)) P.natDegree e
  have hH (x : σ → R) : H.map (MvPolynomial.eval x) =
      ((P.map (MvPolynomial.eval x)).derivative * Q.map (MvPolynomial.eval x)) %
        P.map (MvPolynomial.eval x) := by
    dsimp only [H]
    rw [map_modByMonic _ hP,
      modByMonic_eq_mod _ (hP.map (MvPolynomial.eval x))]
    congr 1
    rw [Polynomial.map_mul, derivative_map]
  have hquery (x : σ → R) {e : ℕ} (he : (H.map (MvPolynomial.eval x)).natDegree = e) :
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) =
        (((List.range (P.natDegree + 1)).reverse.map (s e)).map
          (MvPolynomial.eval x)).permanencesMinusVariations := by
    rw [tarskiQuery_eq_permanencesMinusVariations_signedPsc,
      hP.natDegree_map, ← hH, he]
    have hred := map_reductum_natDegree_map_add_one (MvPolynomial.eval x) H
    rw [he] at hred
    rw [← hred]
    have hs : signedPsc (P.map (MvPolynomial.eval x))
        ((H.reductum (e + 1)).map (MvPolynomial.eval x)) P.natDegree e =
          fun j => MvPolynomial.eval x (s e j) :=
      funext fun j => signedPsc_map_map _ _ _ _ _ _
    rw [hs, List.map_map]
    rfl
  have hset : {x : σ → R |
        tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} =
      ⋃ e ∈ Iic H.natDegree,
        {x | (H.map (MvPolynomial.eval x)).natDegree = e} ∩
          {x | (((List.range (P.natDegree + 1)).reverse.map (s e)).map
            (MvPolynomial.eval x)).permanencesMinusVariations = c} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Iic, exists_prop]
    constructor
    · intro hx
      refine ⟨_, natDegree_map_le, rfl, ?_⟩
      rwa [← hquery x rfl]
    · rintro ⟨e, -, he, hc⟩
      rwa [hquery x he]
  rw [hset]
  exact .biUnion (finite_Iic _) fun e _ =>
    (isSemialgebraic_setOf_natDegree_map_eval_eq H e).inter
      (isSemialgebraic_setOf_permanencesMinusVariations_eval _ _)

/-- The parameters at which a Tarski query of two specializations of polynomial families has a
prescribed value form a semialgebraic set. The root family need not be monic: its specialized
degree may drop, and it may specialize to zero. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval_eq (P Q : (MvPolynomial σ R)[X]) (c : ℤ) :
    IsSemialgebraic {x : σ → R |
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} := by
  -- Stratify by the specialized degree `d`, and reduce each stratum to a monic family.
  have hpiece (d : ℕ) : IsSemialgebraic {x : σ → R | P.map (MvPolynomial.eval x) ≠ 0 ∧
      (P.map (MvPolynomial.eval x)).natDegree = d ∧
        tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} := by
    by_cases hPd : P.reductum (d + 1) = 0
    · convert (isSemialgebraic_empty : IsSemialgebraic (∅ : Set (σ → R))) using 1
      refine eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hd, _⟩ => hx ?_
      rw [← map_reductum_natDegree_map_add_one, hd, hPd, Polynomial.map_zero]
    let a := (P.reductum (d + 1)).leadingCoeff
    convert (((isSemialgebraic_setOf_map_eval_eq_zero P).compl).inter
      (isSemialgebraic_setOf_natDegree_map_eval_eq P d)).inter
      (isSemialgebraic_setOf_tarskiQuery_map_eval_eq_of_monic
        (P.reductum (d + 1)).integralNormalization (C (a ^ Q.natDegree) * Q.scaleRoots a)
        (monic_integralNormalization hPd) c) using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, and_assoc]
    exact and_congr_right fun hx => and_congr_right fun hd => by
      rw [tarskiQuery_map_eval_eq_integralNormalization Q hx hd]
  have hset : {x : σ → R |
        tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} =
      ({x | P.map (MvPolynomial.eval x) = 0} ∩ {_x | c = 0}) ∪
        ⋃ d ∈ Iic P.natDegree, {x | P.map (MvPolynomial.eval x) ≠ 0 ∧
          (P.map (MvPolynomial.eval x)).natDegree = d ∧
            tarskiQuery (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) = c} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, mem_Iic, exists_prop]
    by_cases hx : P.map (MvPolynomial.eval x) = 0
    · simp [hx, eq_comm]
    · simp only [hx, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      exact ⟨fun h => ⟨_, natDegree_map_le, rfl, h⟩, fun ⟨_, _, _, h⟩ => h⟩
  rw [hset]
  refine .union (.inter (isSemialgebraic_setOf_map_eval_eq_zero P) ?_)
    (.biUnion (finite_Iic _) fun d _ => hpiece d)
  by_cases hc : c = 0 <;> simp [hc]

/-- Any condition on finitely many Tarski queries of a polynomial family is semialgebraic. The
queries have a common finite range bounded by the formal degree of the root polynomial, so the
condition is a finite union of intersections of query fibers. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval
    {ι : Type*} [Finite ι] (P : (MvPolynomial σ R)[X])
    (Q : ι → (MvPolynomial σ R)[X]) (Φ : (ι → ℤ) → Prop) :
    IsSemialgebraic {x : σ → R |
      Φ fun i => tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))} := by
  let V := Set.Icc (-(P.natDegree : ℤ)) (P.natDegree : ℤ)
  have hmem (x : σ → R) (i : ι) :
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x)) ∈ V := by
    have h := Polynomial.tarskiQuery_mem_Icc_natDegree
      (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))
    have hle : ((P.map (MvPolynomial.eval x)).natDegree : ℤ) ≤ P.natDegree := by
      exact_mod_cast natDegree_map_le
    exact ⟨by grind, by grind⟩
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
  classical
  by_cases hp : P.map (MvPolynomial.eval x) = 0
  · simp [sign_eval_map_iterate_derivative, hp, ← Pi.zero_def, Matrix.mulVec_zero]
  · simp only [Polynomial.map_prod, Polynomial.map_pow, ← iterate_derivative_map]
    rw [fullInverse_mulVec_iterate_derivative_of_natDegree_le _
      RealClosure.polynomialRolle_of_isRealClosed hp natDegree_map_le]
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp, IsRoot.def,
      ite_eq_left_iff, zero_ne_one, imp_false, not_not]

/-- **Uniform Thom-encoding realization.** For a prescribed sign word on the derivatives of orders
`1, …, P.natDegree`, the parameters at which the specialized polynomial has a root with those
derivative signs form a semialgebraic set. The family need not be monic. Where it specializes to
zero, every point is a root and every derivative vanishes, so only the zero word is realized. -/
theorem isSemialgebraic_setOf_exists_root_derivative_signs_eq
    (P : (MvPolynomial σ R)[X]) (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r : R,
      (P.map (MvPolynomial.eval x)).eval r = 0 ∧
        ∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j} := by
  classical
  let Q : (Fin P.natDegree → Fin 3) → (MvPolynomial σ R)[X] := fun e =>
    ∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val
  let Φ : ((Fin P.natDegree → Fin 3) → ℤ) → Prop := fun v =>
    (SignDetermination.fullInverse (Fin P.natDegree) *ᵥ (fun e => (v e : ℚ))) τ = 1
  have hset : {x : σ → R | ∃ r : R,
        (P.map (MvPolynomial.eval x)).eval r = 0 ∧
          ∀ j : Fin P.natDegree,
            SignType.sign (((derivative^[j.val + 1] P).map
              (MvPolynomial.eval x)).eval r) = τ j} =
      ({x | P.map (MvPolynomial.eval x) = 0} ∩ {_x | τ = 0}) ∪
        ({x | P.map (MvPolynomial.eval x) = 0}ᶜ ∩ {x | Φ fun e =>
          tarskiQuery (P.map (MvPolynomial.eval x)) ((Q e).map (MvPolynomial.eval x))}) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff,
      ← iterate_derivative_map]
    by_cases hx : P.map (MvPolynomial.eval x) = 0
    · simp only [hx, iterate_derivative_zero, eval_zero, sign_zero, true_and,
        not_true_eq_false, false_and, or_false, funext_iff, Pi.zero_apply, exists_const,
        eq_comm (a := (0 : SignType))]
    · simp only [hx, false_and, false_or, not_false_eq_true, true_and, Φ, Q,
        fullInverse_mulVec_tarskiQuery_derivative_eq_one_iff, Multiset.mem_toFinset,
        Polynomial.mem_roots hx, IsRoot.def, ← iterate_derivative_map]
  rw [hset]
  refine .union (.inter (isSemialgebraic_setOf_map_eval_eq_zero P) ?_)
    (.inter (isSemialgebraic_setOf_map_eval_eq_zero P).compl
      (isSemialgebraic_setOf_tarskiQuery_map_eval P Q Φ))
  by_cases hτ : τ = 0 <;> simp [hτ]

/-- Two roots of `P.map (MvPolynomial.eval x)` with the same consecutive derivative signs
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
  have hp : P.map (MvPolynomial.eval x) ≠ 0 :=
    Polynomial.ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hr)
  refine Polynomial.eq_of_derivativeSign_succ_eq_of_natDegree_le natDegree_map_le
    RealClosure.polynomialRolle_of_isRealClosed hp
    (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
    (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr')) ?_
  funext j
  simpa only [sign_eval_map_iterate_derivative] using (hτ j).trans (hτ' j).symm

/-- Combine realization of a Thom word with a comparison determined by derivative signs. -/
private theorem isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (τ : Fin P.natDegree → SignType)
    (Φ : R → R → Prop)
    (Ψ : (Fin (P.natDegree + 1) → SignType) → (Fin P.natDegree → SignType) → Prop)
    (hiff : ∀ {p : R[X]}, p.natDegree ≤ P.natDegree → p ≠ 0 → ∀ {a b : R},
      p.eval b = 0 → (Φ a b ↔ Ψ (fun i => derivativeSign p a i.val)
        (fun j => derivativeSign p b (j.val + 1)))) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      (∀ j : Fin P.natDegree,
        SignType.sign (((derivative^[j.val + 1] P).map
          (MvPolynomial.eval x)).eval r) = τ j) ∧ Φ (MvPolynomial.eval x T) r} := by
  convert ((isSemialgebraic_setOf_map_eval_eq_zero P).compl.inter
    (isSemialgebraic_setOf_exists_root_derivative_signs_eq P τ)).inter
    (isSemialgebraic_setOf_sign_eval
      (fun i : Fin (P.natDegree + 1) => (derivative^[i.val] P).eval T)
      (fun υ => Ψ υ τ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, ← eval_map_apply,
    sign_eval_map_iterate_derivative]
  have hcmp {r : R} (hr : r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset)
      (hτ : ∀ j : Fin P.natDegree,
        derivativeSign (P.map (MvPolynomial.eval x)) r (j.val + 1) = τ j) :
      Φ (MvPolynomial.eval x T) r ↔
        Ψ (fun i => derivativeSign (P.map (MvPolynomial.eval x)) (MvPolynomial.eval x T) i.val)
          τ := by
    simpa only [funext hτ] using hiff natDegree_map_le
      (Polynomial.ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hr))
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
  constructor
  · rintro ⟨r, hr, hτ, h⟩
    exact ⟨⟨Polynomial.ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hr), r,
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr), hτ⟩, (hcmp hr hτ).mp h⟩
  · rintro ⟨⟨hp, r, hr, hτ⟩, h⟩
    have hr' := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hr)
    exact ⟨r, hr', hτ, (hcmp hr' hτ).mpr h⟩

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
  exact isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and P T τ
    (· < ·) (fun υ τ => ThomLT υ (Fin.cons 0 τ)) (fun {_} hd hp {_ _} hr =>
      Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_right hd
        RealClosure.polynomialRolle_of_isRealClosed hp hr)

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
  exact isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and P T τ
    (fun a b => b < a) (fun υ τ => ThomLT (Fin.cons 0 τ) υ) (fun {_} hd hp {_ _} hr =>
      Polynomial.lt_iff_thomLT_cons_derivativeSign_of_eval_eq_zero_left hd
        RealClosure.polynomialRolle_of_isRealClosed hp hr)

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
      simpa only [sign_eval_map_iterate_derivative] using hτ j
    rw [Polynomial.card_roots_lt_eq_card_filter_thomLT_of_natDegree_le natDegree_map_le
      RealClosure.polynomialRolle_of_isRealClosed hr0 hτ']
    congr 1
    ext υ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sign_eval_map_iterate_derivative,
      funext_iff]
  exact ⟨fun ⟨r, hr, hτ, hcard⟩ => ⟨⟨r, hr, hτ⟩, (hcard_eq hr hτ).symm.trans hcard⟩,
    fun ⟨⟨r, hr, hτ⟩, hcard⟩ => ⟨r, hr, hτ, (hcard_eq hr hτ).trans hcard⟩⟩

/-- Combine a prescribed root index with a predicate whose realization at each Thom word is
semialgebraic. The shared word ensures that both witnesses are the same root. -/
private theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and
    (P : (MvPolynomial σ R)[X]) (i : ℕ) (Φ : (σ → R) → R → Prop)
    (hΦ : ∀ τ : Fin P.natDegree → SignType,
      IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
        (∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j) ∧ Φ x r}) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧ Φ x r} := by
  convert IsSemialgebraic.iUnion (fun τ : Fin P.natDegree → SignType =>
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_card_roots_lt P τ i).inter
      (hΦ τ)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨r, hr, hcard, hΦ⟩ =>
    ⟨fun j => SignType.sign (((derivative^[j.val + 1] P).map (MvPolynomial.eval x)).eval r),
      ⟨r, hr, fun _ => rfl, hcard⟩, ⟨r, hr, fun _ => rfl, hΦ⟩⟩,
    fun ⟨_, ⟨r, hr, hτ, hcard⟩, ⟨r', hr', hτ', hΦ⟩⟩ =>
      ⟨r, hr, hcard, eq_of_mem_roots_derivative_signs_eq hr hr' hτ hτ' ▸ hΦ⟩⟩

/-- **Region where a polynomial lies strictly below the `i`-th distinct root.** For polynomials `P`
and `T`, the parameters `x` at which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r`
(with `i` distinct roots strictly below `r`, so `i = 0` is the smallest root)
and `MvPolynomial.eval x T < r` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        MvPolynomial.eval x T < r} := by
  exact isSemialgebraic_setOf_mem_roots_card_roots_lt_and P i
    (fun x r => MvPolynomial.eval x T < r)
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_eval_lt P T)

/-- **Region where a polynomial lies strictly above the `i`-th distinct root.** For polynomials `P`
and `T`, the parameters `x` at which `P.map (MvPolynomial.eval x)` has an `i`-th distinct root `r`
(with `i` distinct roots strictly below `r`, so `i = 0` is the smallest root)
and `r < MvPolynomial.eval x T` form a semialgebraic set. -/
theorem isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval
    (P : (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (i : ℕ) :
    IsSemialgebraic {x : σ → R | ∃ r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset,
      {z ∈ (P.map (MvPolynomial.eval x)).roots.toFinset | z < r}.card = i ∧
        r < MvPolynomial.eval x T} := by
  exact isSemialgebraic_setOf_mem_roots_card_roots_lt_and P i
    (fun x r => r < MvPolynomial.eval x T)
    (isSemialgebraic_setOf_mem_roots_derivative_signs_eq_and_lt_eval P T)

variable {n : ℕ}

/-- **The region strictly below the `i`-th distinct root in cylinder coordinates.** The points of
`R ^ (n + 1)` whose coordinate `0` lies strictly below the `i`-th distinct root of the
specialization of `P` at the remaining coordinates form a semialgebraic set. Here `i` counts
distinct roots strictly below that root, so `i = 0` is the smallest root. -/
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
specialization of `P` at the remaining coordinates form a semialgebraic set. Here `i` counts
distinct roots strictly below that root, so `i = 0` is the smallest root. -/
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
