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
# Semialgebraic Thom encodings in monic polynomial families

For a monic polynomial whose coefficients are polynomial functions of parameters, every Tarski
query of a polynomial family is determined by finitely many signs of polynomial functions of the
parameters. Consequently any condition on finitely many such queries is semialgebraic.

Applying this to the products of consecutive derivatives in the full BKR moment system gives a
uniform coefficient-sign description of each realized Thom encoding. This is the fixed-degree
monic case of the coefficient description of ordered roots. The monic hypothesis ensures that
polynomial remainder commutes with every coefficient specialization; arbitrary families require
separate degree strata and denominator clearing.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval_eq_of_monic` describes one query fiber.
* `TauCeti.isSemialgebraic_setOf_tarskiQuery_map_eval_of_monic` allows an arbitrary condition on
  a finite family of queries.
* `TauCeti.isSemialgebraic_setOf_exists_root_derivative_signs_eq_of_monic` describes realization
  of a prescribed Thom sign word.

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

/-- The parameters at which a Tarski query of two specializations of polynomial families has a
prescribed value form a semialgebraic set, provided the root family is monic. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval_eq_of_monic
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

/-- Any condition on finitely many Tarski queries of a monic polynomial family is
semialgebraic. The queries have a common finite range bounded by the degree of the root
polynomial, so the condition is a finite union of intersections of query fibers. -/
theorem isSemialgebraic_setOf_tarskiQuery_map_eval_of_monic
    {ι : Type*} [Finite ι] (P : (MvPolynomial σ R)[X]) (hP : P.Monic)
    (Q : ι → (MvPolynomial σ R)[X]) (Φ : (ι → ℤ) → Prop) :
    IsSemialgebraic {x : σ → R |
      Φ fun i => tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))} := by
  let V := Set.Icc (-(P.natDegree : ℤ)) (P.natDegree : ℤ)
  have hmem (x : σ → R) (i : ι) :
      tarskiQuery (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x)) ∈ V := by
    simpa only [V, hP.natDegree_map] using
      Polynomial.tarskiQuery_mem_Icc_natDegree
        (P.map (MvPolynomial.eval x)) (Q i |>.map (MvPolynomial.eval x))
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
    isSemialgebraic_setOf_tarskiQuery_map_eval_eq_of_monic P (Q i) hP (v i)

/-- **Uniform Thom-encoding realization for monic families.** For a prescribed sign word, the
parameters at which the specialized polynomial has a root with those signs of its consecutive
derivatives form a semialgebraic set. Monicity makes the formal index type agree with the degree
of every specialization. -/
theorem isSemialgebraic_setOf_exists_root_derivative_signs_eq_of_monic
    (P : (MvPolynomial σ R)[X]) (hP : P.Monic)
    (τ : Fin P.natDegree → SignType) :
    IsSemialgebraic {x : σ → R | ∃ r : R,
      (P.map (MvPolynomial.eval x)).eval r = 0 ∧
        ∀ j : Fin P.natDegree,
          SignType.sign (((derivative^[j.val + 1] P).map
            (MvPolynomial.eval x)).eval r) = τ j} := by
  let Q : (Fin P.natDegree → Fin 3) → (MvPolynomial σ R)[X] := fun e =>
    ∏ j : Fin P.natDegree, (derivative^[j.val + 1] P) ^ (e j).val
  have hsemi := isSemialgebraic_setOf_tarskiQuery_map_eval_of_monic P hP Q
    (fun v => (SignDetermination.fullInverse (Fin P.natDegree) *ᵥ
      (fun e => (v e : ℚ))) τ = 1)
  convert hsemi using 1
  ext x
  simp only [mem_ofPred_eq]
  have hderiv (k : ℕ) :
      (derivative^[k] P).map (MvPolynomial.eval x) =
        derivative^[k] (P.map (MvPolynomial.eval x)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← derivative_map, ih]
  have hQ (e : Fin P.natDegree → Fin 3) : (Q e).map (MvPolynomial.eval x) =
      ∏ j : Fin P.natDegree,
        (derivative^[j.val + 1] (P.map (MvPolynomial.eval x))) ^ (e j).val := by
    simp only [Q, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.map_pow, hderiv]
  simp only [hQ]
  rw [Polynomial.fullInverse_mulVec_tarskiQuery]
  simp only [hderiv]
  symm
  rw [Finset.signCount_eq_occCount, Function.occCount_of_injective]
  · have hexists :
        (∃ r : (P.map (MvPolynomial.eval x)).roots.toFinset,
          (fun j : Fin P.natDegree => SignType.sign
            ((derivative^[j.val + 1] (P.map (MvPolynomial.eval x))).eval (r : R))) = τ) ↔
          ∃ r, (P.map (MvPolynomial.eval x)).eval r = 0 ∧
            ∀ j : Fin P.natDegree, SignType.sign
              ((derivative^[j.val + 1] (P.map (MvPolynomial.eval x))).eval r) = τ j := by
        constructor
        · rintro ⟨r, hr⟩
          refine ⟨r, (Polynomial.mem_roots (hP.map (MvPolynomial.eval x)).ne_zero).mp
            (Multiset.mem_toFinset.mp r.property), fun j => congrFun hr j⟩
        · rintro ⟨r, hr, hs⟩
          refine ⟨⟨r, Multiset.mem_toFinset.mpr
            ((Polynomial.mem_roots (hP.map (MvPolynomial.eval x)).ne_zero).mpr hr)⟩, ?_⟩
          funext j
          exact hs j
    simp only [hexists, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_eq_left_iff,
      zero_ne_one, imp_false, not_not]
  · intro a b hab
    apply Subtype.ext
    apply Polynomial.thomEncoding_injOn (P.map (MvPolynomial.eval x))
      RealClosure.polynomialRolle_of_isRealClosed (hP.map (MvPolynomial.eval x)).ne_zero
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp a.property))
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp b.property))
    funext j
    have hj := congrFun hab (Fin.cast (hP.natDegree_map (MvPolynomial.eval x)) j)
    simpa only [Polynomial.thomEncoding_def, Fin.val_cast, hderiv] using hj

end TauCeti
