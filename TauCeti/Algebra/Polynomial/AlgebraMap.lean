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
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# Irreducibility under algebra isomorphisms, evaluation modulo an ideal and faithfulness

Irreducibility of a polynomial after extending its coefficients is invariant under an
isomorphism of algebras over the coefficient ring.

Since `x - c` divides `p(x) - p(c)`, a congruence `(x - c) e ≡ 0` modulo an ideal gives
`(p(x) - p(c)) e ≡ 0` for every polynomial `p` (`Polynomial.aeval_sub_algebraMap_eval_mul_mem`).
For an idempotent `e` commuting with `u`, evaluating a polynomial `P` at `u e` or `u (1 - e)`
splits as `P(u) e + P(0) • (1 - e)` or `P(u) (1 - e) + P(0) • e`
(`Polynomial.aeval_mul_of_isIdempotentElem`, `Polynomial.aeval_mul_one_sub_of_isIdempotentElem`),
and when `P(0)` is a unit and `P(u)` is invertible modulo `e`, `P(u (1 - e))` is a unit
(`Polynomial.isUnit_aeval_mul_one_sub_of_isIdempotentElem`).

For an `R[X]`-algebra `S` compatible with its `R`-algebra structure, the algebra map `R[X] → S` is
evaluation at the image of `X` (`Polynomial.algebraMap_eq_aeval`).

A monic polynomial of positive degree dividing every polynomial that vanishes at `f : B` forces
`A` to act faithfully on `B` (`Polynomial.Monic.faithfulSMul_of_dvd`), and evaluating
`1 - C c * P` at `u` recovers `c • P(u)` via `1 - (1 - C c * P)(u)`
(`Polynomial.one_sub_aeval_one_sub_C_mul`).
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

/-- For an `R[X]`-algebra `S` whose `R`-algebra structure factors through `R[X]`, the algebra map
`R[X] → S` is evaluation at the image of `X`. -/
theorem algebraMap_eq_aeval {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [Algebra R[X] S] [IsScalarTower R R[X] S] (f : R[X]) :
    algebraMap R[X] S f = aeval (algebraMap R[X] S X) f := by
  rw [← IsScalarTower.coe_toAlgHom' R, aeval_algHom_apply, aeval_X_left_apply]

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

/-- If `e` is a commuting idempotent for `u`, `P(0)` is a unit, and `P(u)` is invertible modulo
`e`, then `P(u * (1 - e))` is invertible. -/
theorem isUnit_aeval_mul_one_sub_of_isIdempotentElem {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {u e w : A} {P : R[X]} (he : IsIdempotentElem e) (hue : Commute u e)
    (hP0 : IsUnit (P.coeff 0)) (hw₁ : aeval u P * w = 1 - e) (hw₂ : w * aeval u P = 1 - e) :
    IsUnit (aeval (u * (1 - e)) P) := by
  have hunit := he.isUnit_add_mul_one_sub hw₁ hw₂
  have hscale := he.isUnit_one_add_sub_one_smul hP0
  have hCE : Commute (aeval u P) e := by
    have hCw : Commute (aeval u P) w := hw₁.trans hw₂.symm
    have h1 : Commute (aeval u P) (1 - e) := hw₂ ▸ hCw.mul_right (Commute.refl _)
    simpa using (Commute.one_right _).sub_right h1
  have hE_mul : e * (aeval u P * (1 - e)) = 0 := by
    rw [← mul_assoc, ← hCE.eq, mul_assoc]
    simp [mul_sub, he.eq]
  have heq : (1 + (P.coeff 0 - 1) • e) * (e + aeval u P * (1 - e)) = aeval (u * (1 - e)) P := by
    rw [aeval_mul_one_sub_of_isIdempotentElem he hue]
    simp only [add_mul, one_mul, mul_add, smul_mul_assoc, he.eq, hE_mul, smul_zero, add_zero]
    module
  exact heq ▸ hscale.mul hunit

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

/-- Evaluating `1 - C c * P` at `u` satisfies `1 - aeval u (1 - C c * P) = c • aeval u P`. -/
theorem one_sub_aeval_one_sub_C_mul {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (u : A) (c : R) (P : R[X]) :
    1 - aeval u (1 - C c * P) = c • aeval u P := by
  simp [Algebra.algebraMap_eq_smul_one]

end Polynomial
