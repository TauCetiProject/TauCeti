/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quartic.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Discriminants of quartics and their resolvent cubics

A monic quartic of degree four and the cubic obtained by specializing `quarticD4Spec` have the
same discriminant. Consequently, the specialized resolvent is separable exactly when the quartic
is separable, so downstream quartic Galois-group criteria require no additional separation
hypothesis.

For the depressed quartic

`X⁴ + pX² + qX + r`

and its cubic resolvent

`X³ - pX² - 4rX + (4pr - q²)`

the specialized resolvent is `TauCeti.resolventCubic p q r`, giving the corresponding closed-form
identity and separability results. All these statements hold over an arbitrary commutative ring.

## Main results

* `Polynomial.Monic.discr_of_natDegree_eq_four`: the coefficient formula for the discriminant of
  a monic quartic.
* `TauCeti.discr_depressedQuartic`: the explicit discriminant of a depressed quartic.
* `TauCeti.discr_quarticD4Spec_specialize`: a monic quartic of degree four and its specialized
  resolvent have equal discriminants.
* `TauCeti.separable_quarticD4Spec_specialize_iff`: the quartic is separable exactly when its
  specialized resolvent is.
* `TauCeti.discr_resolventCubic`: a depressed quartic and its resolvent cubic have equal
  discriminants.
* `TauCeti.separable_resolventCubic_iff`: the quartic is separable exactly when its resolvent is.
* `TauCeti.separable_resolventCubic`: a separable quartic has a separable resolvent cubic.

## References

* K. Conrad, *Galois groups of cubics and quartics (not in characteristic 2)*, Theorem 3.4.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A monic quartic of degree four and the specialization of the quartic `D₄` resolvent have the
same discriminant. -/
theorem discr_quarticD4Spec_specialize {f : R[X]} (hmonic : f.Monic)
    (hf : f.natDegree = 4) :
    f.discr = (quarticD4Spec.specialize R f).discr := by
  nontriviality R
  have hres : quarticD4Spec.specialize R f =
      (Cubic.toPoly
        ⟨1, -f.coeff 2, f.coeff 3 * f.coeff 1 - 4 * f.coeff 0,
          -(f.coeff 3 ^ 2 * f.coeff 0 + f.coeff 1 ^ 2 -
            4 * f.coeff 2 * f.coeff 0)⟩ : R[X]) := by
    exact quarticD4Spec_specialize_eq_toPoly R f
  rw [hres, Cubic.toPoly_discr one_ne_zero, Cubic.discr,
    hmonic.discr_of_natDegree_eq_four hf]
  ring

/-- The specialization of the quartic `D₄` resolvent is separable exactly when the monic
quartic of degree four is separable. -/
theorem separable_quarticD4Spec_specialize_iff {f : R[X]} (hmonic : f.Monic)
    (hf : f.natDegree = 4) :
    (quarticD4Spec.specialize R f).Separable ↔ f.Separable := by
  nontriviality R
  rw [← (quarticD4Spec.monic_specialize R f).isUnit_discr_iff,
    ← hmonic.isUnit_discr_iff, discr_quarticD4Spec_specialize hmonic hf]

/-- A depressed quartic and its resolvent cubic have the same discriminant. -/
theorem discr_resolventCubic (p q r : R) :
    (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).discr =
      (resolventCubic p q r).discr := by
  nontriviality R
  have hquartic : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Monic := by
    have hdeg : degree (C p * X ^ 2 + C q * X + C r : R[X]) < 4 := by
      compute_degree
      norm_num
    simpa only [add_assoc] using monic_X_pow_add hdeg
  have hdegree : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).natDegree = 4 := by
    compute_degree <;> norm_num
  rw [← quarticD4Spec_specialize_depressed]
  exact discr_quarticD4Spec_specialize hquartic hdegree

/-- The resolvent cubic of a depressed quartic is separable exactly when the quartic is
separable. This holds over every commutative ring, where separability of a monic polynomial is
equivalent to its discriminant being a unit. -/
@[simp]
theorem separable_resolventCubic_iff (p q r : R) :
    (resolventCubic p q r).Separable ↔
      (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Separable := by
  nontriviality R
  have hquartic : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Monic := by
    have hdeg : degree (C p * X ^ 2 + C q * X + C r : R[X]) < 4 := by
      compute_degree
      norm_num
    simpa only [add_assoc] using monic_X_pow_add hdeg
  have hdegree : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).natDegree = 4 := by
    compute_degree <;> norm_num
  rw [← quarticD4Spec_specialize_depressed]
  exact separable_quarticD4Spec_specialize_iff hquartic hdegree

/-- The resolvent cubic of a separable depressed quartic is separable. -/
theorem separable_resolventCubic (p q r : R)
    (h : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Separable) :
    (resolventCubic p q r).Separable :=
  (separable_resolventCubic_iff p q r).2 h

end TauCeti
