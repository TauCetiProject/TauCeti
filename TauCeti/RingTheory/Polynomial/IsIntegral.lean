/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.IsIntegral

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.ComputeDegree

/-!
# Integrality in polynomial rings and from monic quadratic relations

This file collects two polynomial integrality results:

1. **Integrality from a monic quadratic relation.** Mathlib's
   `IsIntegral.of_aeval_monic_of_isIntegral_coeff` takes a monic polynomial and asks for each
   coefficient to be integral. Applying it to a quadratic means writing the polynomial out,
   discharging the degree computation, and answering the coefficient obligation index by index —
   the same half-dozen lines every time.
2. **Integral closure of constants in a polynomial ring.** Over a commutative ring `R`, the
   constants are integrally closed in `R[X]` if and only if `R` is reduced: a nilpotent `a ∈ R`
   makes `C a * X` nilpotent (hence integral over `R`) without being constant, while over a reduced
   ring `R`, passing modulo a prime ideal not containing the leading coefficient of a nonconstant
   polynomial `f` contradicts `Polynomial.transcendental` via `IsIntegral.isAlgebraic`. Transport
   along `RingEquiv.ofLeftInverse` transfers the same characterization to the subring
   `(Polynomial.C (R := R)).range ⊆ R[X]`.

## Main results

* `IsIntegral.of_sq_add_mul_add_eq_zero`: if `y ^ 2 + b * y + c = 0` with `b` and `c` integral over
  `R`, then `y` is integral over `R`.
* `TauCeti.isIntegrallyClosedIn_polynomial_iff_isReduced`:
  `IsIntegrallyClosedIn R R[X] ↔ IsReduced R`.
* `TauCeti.isIntegrallyClosedIn_polynomial`: instance of `IsIntegrallyClosedIn R R[X]` for
  `[IsReduced R]`.
* `TauCeti.isIntegrallyClosedIn_range_C_iff_isReduced`:
  `IsIntegrallyClosedIn (Polynomial.C (R := R)).range R[X] ↔ IsReduced R`.
* `TauCeti.isIntegrallyClosedIn_range_C`: `IsIntegrallyClosedIn (Polynomial.C (R := R)).range R[X]`
  when `[IsReduced R]`.

## Applications

For a Weierstrass equation over `R`, the equation is monic quadratic in `y`. When `x` is integral
over `R`, its remaining coefficients are integral as well, so the quadratic criterion proves
integrality of `y`. It also applies to the quadratic relations for `s` and `t` in a change of
variables between integral Weierstrass models.

The characterization of `IsIntegrallyClosedIn (Polynomial.C (R := R)).range R[X]` shows that
`(R[X], R)` with the discrete topology forms a Huber pair whenever `R` is reduced (in particular
for `R = ℤ`, the discrete affine line representing `CAff.globalSections`).

## Provenance

`IsIntegral.of_sq_add_mul_add_eq_zero` comes from the proof of
`WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x` in
`TauCeti/AlgebraicGeometry/EllipticCurve/Integrality.lean`.
-/

public section

open Polynomial

/-- **An element satisfying a monic quadratic relation with integral coefficients is integral.**
`y`, `b` and `c` live in an arbitrary commutative `R`-algebra `A`, and the relation is an equation
in `A` rather than a statement about `Polynomial.aeval`, so a caller supplies whatever identity it
already holds. -/
theorem IsIntegral.of_sq_add_mul_add_eq_zero {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {b c y : A} (hb : IsIntegral R b) (hc : IsIntegral R c)
    (h : y ^ 2 + b * y + c = 0) : IsIntegral R y := by
  -- `IsIntegral.of_aeval_monic_of_isIntegral_coeff` for `X ^ 2 + C b * X + C c`, with the degree
  -- computation and the per-coefficient obligations discharged index by index.
  nontriviality A
  have hdeg : (X ^ 2 + (C b * X + C c) : A[X]).natDegree = 2 := by compute_degree!
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := X ^ 2 + (C b * X + C c))
    (monic_X_pow_add (by compute_degree!)) (by omega) ?_ ?_
  · have : Polynomial.eval y (X ^ 2 + (C b * X + C c) : A[X]) = 0 := by
      simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h
    rw [this]
    exact isIntegral_zero
  · intro i
    match i with
    | 0 => simpa using hc
    | 1 => simpa using hb
    | 2 => simpa using (isIntegral_one : IsIntegral R (1 : A))
    | (n + 3) => simpa using (isIntegral_zero : IsIntegral R (0 : A))

namespace TauCeti

/-- Over a commutative ring `R`, `R` is integrally closed in `R[X]` if and only if `R` is
reduced. -/
theorem isIntegrallyClosedIn_polynomial_iff_isReduced {R : Type*} [CommRing R] :
    IsIntegrallyClosedIn R R[X] ↔ IsReduced R := by
  refine ⟨fun h ↦ ⟨fun a ⟨n, hn⟩ ↦ ?_⟩, fun hred ↦ ?_⟩
  · have hint : IsIntegral R (C a * X) :=
      ⟨X ^ n, monic_X_pow n, by simp [mul_pow, ← map_pow, hn]⟩
    obtain ⟨r, hr⟩ := (isIntegrallyClosedIn_iff.mp h).2 hint
    simpa [coeff_C] using (congrArg (fun p : R[X] ↦ p.coeff 1) hr).symm
  · refine isIntegrallyClosedIn_iff.mpr ⟨Polynomial.C_injective, fun {f} hf ↦ ?_⟩
    by_cases hdeg : f.natDegree = 0
    · exact ⟨f.coeff 0, (eq_C_of_natDegree_eq_zero hdeg).symm⟩
    exfalso
    have hlc_ne : f.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr fun h0 ↦ hdeg (h0 ▸ natDegree_zero)
    have hnotnil : ¬ IsNilpotent f.leadingCoeff := fun hnil ↦ hlc_ne (hred.eq_zero _ hnil)
    rw [nilpotent_iff_mem_prime] at hnotnil
    push Not at hnotnil
    obtain ⟨P, hP, hlc_notMem⟩ := hnotnil
    let q : R →+* R ⧸ P := Ideal.Quotient.mk P
    have : P.IsPrime := hP
    have hq_lc : q f.leadingCoeff ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    have hmap_deg : (f.map q).natDegree = f.natDegree :=
      natDegree_map_eq_iff.mpr (Or.inl hq_lc)
    have hmap_lc : (f.map q).leadingCoeff = q f.leadingCoeff :=
      leadingCoeff_map_of_leadingCoeff_ne_zero q hq_lc
    have hmap_int : IsIntegral (R ⧸ P) (f.map q) :=
      hf.map_of_comp_eq q (Polynomial.mapRingHom q) (by ext; simp)
    exact Polynomial.transcendental (f.map q) (hmap_deg ▸ hdeg)
      (mem_nonZeroDivisors_of_ne_zero (hmap_lc ▸ hq_lc)) hmap_int.isAlgebraic

/-- Over a reduced commutative ring `R`, `R` is integrally closed in `R[X]`. -/
instance isIntegrallyClosedIn_polynomial (R : Type*) [CommRing R] [IsReduced R] :
    IsIntegrallyClosedIn R R[X] :=
  isIntegrallyClosedIn_polynomial_iff_isReduced.mpr ‹_›

/-- Over a commutative ring `R`, the subring `Polynomial.C.range` of constant polynomials is
integrally closed in `R[X]` if and only if `R` is reduced. -/
theorem isIntegrallyClosedIn_range_C_iff_isReduced {R : Type*} [CommRing R] :
    IsIntegrallyClosedIn (Polynomial.C (R := R)).range R[X] ↔ IsReduced R := by
  let e : R ≃+* (Polynomial.C (R := R)).range :=
    RingEquiv.ofLeftInverse (f := Polynomial.C (R := R))
      (g := fun p : R[X] ↦ p.coeff 0) fun _ ↦ coeff_C_zero
  have he : (algebraMap (Polynomial.C (R := R)).range R[X]).comp e.toRingHom =
      algebraMap R R[X] := by
    ext r
    rfl
  rw [← isIntegrallyClosedIn_polynomial_iff_isReduced, Subring.isIntegrallyClosedIn_iff,
    isIntegrallyClosedIn_iff, Polynomial.algebraMap_eq, and_iff_right Polynomial.C_injective]
  exact forall_congr' fun f ↦ imp_congr (e.isIntegral_iff he f).symm Iff.rfl

/-- Over a reduced commutative ring `R`, the subring `Polynomial.C.range` of constant polynomials
is integrally closed in `R[X]`. -/
theorem isIntegrallyClosedIn_range_C {R : Type*} [CommRing R] [IsReduced R] :
    IsIntegrallyClosedIn (Polynomial.C (R := R)).range R[X] :=
  isIntegrallyClosedIn_range_C_iff_isReduced.mpr ‹_›

end TauCeti

end
