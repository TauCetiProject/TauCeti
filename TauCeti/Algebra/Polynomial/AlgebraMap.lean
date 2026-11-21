/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Abel

/-!
# Irreducibility under algebra isomorphisms, evaluation modulo an ideal and faithfulness

Irreducibility of a polynomial after extending its coefficients is invariant under an
isomorphism of algebras over the coefficient ring.

Since `x - c` divides `p(x) - p(c)`, a congruence `(x - c) e ≡ 0` modulo an ideal gives
`(p(x) - p(c)) e ≡ 0` for every polynomial `p` (`Polynomial.aeval_sub_algebraMap_eval_mul_mem`).
For an idempotent `e` commuting with `u`, evaluating a polynomial `P` at `u e` or `u (1 - e)`
splits as `P(u) e + P(0) • (1 - e)` or `P(u) (1 - e) + P(0) • e`
(`Polynomial.aeval_mul_of_isIdempotentElem`, `Polynomial.aeval_mul_one_sub_of_isIdempotentElem`).

A monic polynomial of positive degree dividing every polynomial that vanishes at `f : B` forces
`A` to act faithfully on `B` (`Polynomial.Monic.faithfulSMul_of_dvd`).

An element of an algebra killed by a polynomial whose constant coefficient maps to a unit in the
algebra is a unit (`Polynomial.isUnit_of_aeval_eq_zero`).
-/

public section

namespace TauCeti

open Polynomial

/-- Extending coefficients to isomorphic algebras preserves irreducibility. -/
theorem irreducible_map_iff_of_algEquiv {F K K' : Type*} [CommSemiring F] [Semiring K]
    [Semiring K'] [Algebra F K] [Algebra F K'] (ψ : K ≃ₐ[F] K') (g : F[X]) :
    Irreducible (g.map (algebraMap F K)) ↔ Irreducible (g.map (algebraMap F K')) := by
  have hψ : (ψ.toRingEquiv : K →+* K').comp (algebraMap F K) = algebraMap F K' :=
    RingHom.ext ψ.commutes
  rw [← MulEquiv.irreducible_iff (mapEquiv ψ.toRingEquiv), mapEquiv_apply, Polynomial.map_map,
    hψ]

end TauCeti

namespace Polynomial

/-- If `(x - c) e` lies in an ideal `K`, then so does `(p(x) - p(c)) e` for every polynomial `p`,
since `x - c` divides `p(x) - p(c)`. -/
theorem aeval_sub_algebraMap_eval_mul_mem {R S : Type*} [CommSemiring R] [CommRing S]
    [Algebra R S] {K : Ideal S} {x e : S} {c : R} (he : (x - algebraMap R S c) * e ∈ K)
    (p : R[X]) : (aeval x p - algebraMap R S (p.eval c)) * e ∈ K := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub x (algebraMap R S c) (p.map (algebraMap R S))
  rw [eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hw
  rw [hw, mul_right_comm]
  exact K.mul_mem_right w he

/-- Evaluating a polynomial `P` at `u * e` for a commuting idempotent `e` splits along `e` and
`1 - e` as `P(u) * e + P.coeff 0 • (1 - e)`. -/
theorem aeval_mul_of_isIdempotentElem {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    {u e : A} (he : IsIdempotentElem e) (hue : Commute u e) (P : R[X]) :
    aeval (u * e) P = aeval u P * e + P.coeff 0 • (1 - e) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, coeff_add, add_mul, add_smul, hp, hq]
    abel
  | monomial n a =>
    cases n with
    | zero =>
      simp only [monomial_zero_left, aeval_C, coeff_C_zero, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, ← smul_add, add_sub_cancel]
    | succ k =>
      simp only [aeval_monomial, coeff_monomial_succ, zero_smul, add_zero, hue.mul_pow,
        he.pow_succ_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- Evaluating a polynomial `P` at `u * (1 - e)` for a commuting idempotent `e` splits along
`1 - e` and `e` as `P(u) * (1 - e) + P.coeff 0 • e`. -/
theorem aeval_mul_one_sub_of_isIdempotentElem {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    {u e : A} (he : IsIdempotentElem e) (hue : Commute u e) (P : R[X]) :
    aeval (u * (1 - e)) P = aeval u P * (1 - e) + P.coeff 0 • e := by
  simpa only [sub_sub_cancel] using
    aeval_mul_of_isIdempotentElem he.one_sub ((Commute.one_right u).sub_right hue) P

/-- If a monic polynomial `p` over `A` of positive degree divides every polynomial over `A`
that vanishes at `f : B`, then `A` acts faithfully on `B`: a nonzero constant is not divisible
by `p`. -/
theorem Monic.faithfulSMul_of_dvd {A B : Type*} [CommRing A] [Ring B] [Algebra A B] {p : A[X]}
    (hp : p.Monic) (hpos : 0 < p.natDegree) {f : B} (hdvd : ∀ q : A[X], aeval f q = 0 → p ∣ q) :
    FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  exact hp.not_dvd_of_natDegree_lt (C_ne_zero.mpr ha0) (by rwa [natDegree_C])
    (hdvd _ (by rwa [aeval_C]))

/-- An element of an algebra killed by a polynomial whose constant coefficient maps to a unit in
the algebra is a unit. -/
theorem isUnit_of_aeval_eq_zero {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {x : A}
    {p : R[X]} (hp : IsUnit (algebraMap R A (p.coeff 0))) (hx : aeval x p = 0) : IsUnit x := by
  have hdiv := congrArg (aeval x) (X_mul_divX_add p)
  simp only [map_add, map_mul, aeval_X, aeval_C, hx] at hdiv
  let c : A := (hp.unit⁻¹ : Aˣ)
  have hc : c * algebraMap R A (p.coeff 0) = 1 := by
    simp [c]
  have hcx : Commute c x := by
    have hcomm : Commute (hp.unit : A) x := by
      simpa only [IsUnit.unit_spec] using Algebra.commute_algebraMap_left (p.coeff 0) x
    exact hcomm.units_inv_left
  let y : A := c * aeval x p.divX
  have hcomm : Commute x y :=
    hcx.symm.mul_right
      (by simpa only [aeval_X] using (Commute.all (X : R[X]) p.divX).map (aeval x))
  have he : x * y + 1 = 0 := by
    have hmul := congrArg (c * ·) hdiv
    rw [mul_zero, mul_add, hc, ← mul_assoc, hcx.eq, mul_assoc] at hmul
    exact hmul
  have hee : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = (x * y) * (x * y) + (x * y + 1) := by rw [he, add_zero]
      _ = (x * y) * (x * y + 1) + 1 := by rw [← add_assoc, mul_add, mul_one]
      _ = 1 := by rw [he, mul_zero, zero_add]
  have hxy : IsUnit (x * y) := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp <| by
    rw [pow_two, hee]
    exact isUnit_one
  exact (hcomm.isUnit_mul_iff.mp hxy).1

end Polynomial
