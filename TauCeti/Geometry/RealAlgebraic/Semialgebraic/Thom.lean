/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.RootCount
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Thom
import TauCeti.FieldTheory.RealClosure.AbstractRolle
import TauCeti.RingTheory.Polynomial.Subresultant.CauchyIndex

/-!
# Semialgebraic Thom encodings in polynomial families

For a polynomial whose coefficients are polynomial functions of parameters, every Tarski query
of a polynomial family is determined by finitely many signs of polynomial functions of the
parameters. Consequently any condition on finitely many such queries is semialgebraic.

The monic case reads the query off signed principal subresultant coefficients of a remainder,
since remainder by a monic polynomial commutes with every coefficient specialization. An
arbitrary root family is reduced to it on each stratum of the specialized degree `d`: there the
family agrees with its reductum below degree `d + 1`, whose leading coefficient does not vanish,
and `Polynomial.integralNormalization` clears that leading coefficient. The parameters at which
the root family specializes to zero form a separate stratum, on which every query is zero.

Applying this to the products of consecutive derivatives in the full BKR moment system gives a
uniform coefficient-sign description of each realized Thom encoding. Derivatives are taken up to
the formal degree of the family, so the description does not depend on the specialized degree.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval_eq` describes one query fiber for an
  arbitrary root family.
* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval` allows an arbitrary condition on a finite
  family of queries.
* `TauCeti.isSemialgebraic_setOf_exists_root_derivative_signs_eq` describes realization of a
  prescribed Thom sign word.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapters 4 and 10.
-/

public section

open Polynomial Set
open scoped Matrix

namespace TauCeti

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
  have hQ (x : σ → R) (e : Fin P.natDegree → Fin 3) : (Q e).map (MvPolynomial.eval x) =
      ∏ j : Fin P.natDegree,
        (derivative^[j.val + 1] (P.map (MvPolynomial.eval x))) ^ (e j).val := by
    simp only [Q, Polynomial.map_prod, Polynomial.map_pow, iterate_derivative_map]
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
    · simp only [hx, false_and, false_or, not_false_eq_true, true_and, Φ, hQ,
        fullInverse_mulVec_iterate_derivative_of_natDegree_le _
          RealClosure.polynomialRolle_of_isRealClosed hx natDegree_map_le]
      simp
  rw [hset]
  refine .union (.inter (isSemialgebraic_setOf_map_eval_eq_zero P) ?_)
    (.inter (isSemialgebraic_setOf_map_eval_eq_zero P).compl
      (isSemialgebraic_setOf_tarskiQuery_map_eval P Q Φ))
  by_cases hτ : τ = 0 <;> simp [hτ]

end TauCeti
